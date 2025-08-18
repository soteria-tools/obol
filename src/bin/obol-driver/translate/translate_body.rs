extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_smir;
extern crate rustc_span;
extern crate stable_mir;

use log::trace;
use rustc_smir::IndexedVal;
use stable_mir::{abi, mir, rustc_internal, ty};
use std::{
    collections::{HashMap, VecDeque},
    mem,
    ops::{Deref, DerefMut},
    panic,
};

use charon_lib::{ast::*, ids::Vector, raise_error, register_error, ullbc_ast::*};

use crate::translate::translate_ctx::ItemTransCtx;

/// A translation context for function bodies.
pub(crate) struct BodyTransCtx<'tcx, 'tctx, 'ictx> {
    /// The translation context for the item.
    pub i_ctx: &'ictx mut ItemTransCtx<'tcx, 'tctx>,

    pub local_decls: &'ictx [mir::LocalDecl],

    /// The (regular) variables in the current function body.
    pub locals: Locals,
    /// The map from rust variable indices to translated variables indices.
    pub locals_map: HashMap<usize, LocalId>,
    /// The translated blocks.
    pub blocks: Vector<BlockId, BlockData>,
    /// The map from rust blocks to translated blocks.
    /// Note that when translating terminators like DropAndReplace, we might have
    /// to introduce new blocks which don't appear in the original MIR.
    pub blocks_map: HashMap<mir::BasicBlockIdx, BlockId>,
    /// We register the blocks to translate in a stack, so as to avoid
    /// writing the translation functions as recursive functions. We do
    /// so because we had stack overflows in the past.
    pub blocks_stack: VecDeque<mir::BasicBlockIdx>,
}

impl<'tcx, 'tctx, 'ictx> Deref for BodyTransCtx<'tcx, 'tctx, 'ictx> {
    type Target = ItemTransCtx<'tcx, 'tctx>;
    fn deref(&self) -> &Self::Target {
        self.i_ctx
    }
}
impl<'tcx, 'tctx, 'ictx> DerefMut for BodyTransCtx<'tcx, 'tctx, 'ictx> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.i_ctx
    }
}

impl<'tcx, 'tctx, 'ictx> BodyTransCtx<'tcx, 'tctx, 'ictx> {
    pub(crate) fn new(
        i_ctx: &'ictx mut ItemTransCtx<'tcx, 'tctx>,
        local_decls: &'ictx [mir::LocalDecl],
    ) -> Self {
        BodyTransCtx {
            i_ctx,
            local_decls,
            locals: Default::default(),
            locals_map: Default::default(),
            blocks: Default::default(),
            blocks_map: Default::default(),
            blocks_stack: Default::default(),
        }
    }
}

impl ItemTransCtx<'_, '_> {
    pub fn translate_variant_id(&self, id: stable_mir::ty::VariantIdx) -> VariantId {
        VariantId::new(id.to_index())
    }

    fn translate_field_id(&self, id: mir::FieldIdx) -> FieldId {
        FieldId::new(id)
    }
}

impl BodyTransCtx<'_, '_, '_> {
    pub(crate) fn translate_local(&self, local: &mir::Local) -> Option<LocalId> {
        self.locals_map.get(local).copied()
    }

    pub(crate) fn push_var(&mut self, rid: usize, ty: Ty, name: Option<String>) {
        let local_id = self
            .locals
            .locals
            .push_with(|index| Local { index, name, ty });
        self.locals_map.insert(rid, local_id);
    }

    fn translate_binaryop_kind(&mut self, _span: Span, binop: mir::BinOp) -> Result<BinOp, Error> {
        Ok(match binop {
            mir::BinOp::BitXor => BinOp::BitXor,
            mir::BinOp::BitAnd => BinOp::BitAnd,
            mir::BinOp::BitOr => BinOp::BitOr,
            mir::BinOp::Eq => BinOp::Eq,
            mir::BinOp::Lt => BinOp::Lt,
            mir::BinOp::Le => BinOp::Le,
            mir::BinOp::Ne => BinOp::Ne,
            mir::BinOp::Ge => BinOp::Ge,
            mir::BinOp::Gt => BinOp::Gt,
            mir::BinOp::Div => BinOp::Div(OverflowMode::UB),
            mir::BinOp::Rem => BinOp::Rem(OverflowMode::Wrap),
            mir::BinOp::Add => BinOp::Add(OverflowMode::Wrap),
            mir::BinOp::AddUnchecked => BinOp::Add(OverflowMode::UB),
            mir::BinOp::Sub => BinOp::Sub(OverflowMode::Wrap),
            mir::BinOp::SubUnchecked => BinOp::Sub(OverflowMode::UB),
            mir::BinOp::Mul => BinOp::Mul(OverflowMode::Wrap),
            mir::BinOp::MulUnchecked => BinOp::Mul(OverflowMode::UB),
            mir::BinOp::Shl => BinOp::Shl(OverflowMode::Wrap),
            mir::BinOp::ShlUnchecked => BinOp::Shl(OverflowMode::UB),
            mir::BinOp::Shr => BinOp::Shr(OverflowMode::Wrap),
            mir::BinOp::ShrUnchecked => BinOp::Shr(OverflowMode::UB),
            mir::BinOp::Cmp => BinOp::Cmp,
            mir::BinOp::Offset => BinOp::Offset,
        })
    }

    fn translate_checked_binaryop_kind(
        &mut self,
        span: Span,
        binop: mir::BinOp,
    ) -> Result<BinOp, Error> {
        Ok(match binop {
            mir::BinOp::Add => BinOp::AddChecked,
            mir::BinOp::Sub => BinOp::SubChecked,
            mir::BinOp::Mul => BinOp::MulChecked,
            _ => raise_error!(self, span, "Invalid checked binop: {:?}", binop),
        })
    }

    /// Translate a function's local variables by adding them in the environment.
    fn translate_body_locals(&mut self, body: &mir::Body) -> Result<(), Error> {
        // Translate the parameters
        for (index, var) in body.locals().iter().enumerate() {
            trace!("Translating local of index {} and type {:?}", index, var.ty);

            // Find the name of the variable
            // let name: Option<String> = body.var.name.clone();

            // Translate the type
            let span = self.translate_span_from_smir(&var.span);
            let ty = self.translate_ty(span, var.ty)?;

            // Add the variable to the environment
            self.push_var(index, ty, None);
        }

        Ok(())
    }

    /// Translate a basic block id and register it, if it hasn't been done.
    fn translate_basic_block_id(&mut self, block_id: mir::BasicBlockIdx) -> BlockId {
        match self.blocks_map.get(&block_id) {
            Some(id) => *id,
            // Generate a fresh id - this also registers the block
            None => {
                // Push to the stack of blocks awaiting translation
                self.blocks_stack.push_back(block_id);
                let id = self.blocks.reserve_slot();
                // Insert in the map
                self.blocks_map.insert(block_id, id);
                id
            }
        }
    }

    fn translate_basic_block(&mut self, block: &mir::BasicBlock) -> Result<BlockData, Error> {
        // Translate the statements
        let mut statements = Vec::new();
        for statement in &block.statements {
            trace!("statement: {:?}", statement);

            // Some statements might be ignored, hence the optional returned value
            let opt_statement = self.translate_statement(statement)?;
            if let Some(statement) = opt_statement {
                statements.push(statement)
            }
        }

        // Translate the terminator
        let terminator = self.translate_terminator(&block.terminator, &mut statements)?;

        Ok(BlockData {
            statements,
            terminator,
        })
    }

    fn translate_unsizing_metadata(
        &mut self,
        span: Span,
        src_ty: ty::Ty,
        tgt_ty: ty::Ty,
    ) -> Result<UnsizingMetadata, Error> {
        let tcx = self.t_ctx.tcx;
        let src_ty = rustc_internal::internal(tcx, src_ty);
        let tgt_ty = rustc_internal::internal(tcx, tgt_ty);
        match (src_ty.builtin_deref(true), tgt_ty.builtin_deref(true)) {
            (Some(src_ty), Some(tgt_ty)) => {
                use rustc_middle::ty;
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let (src_ty, tgt_ty) =
                    tcx.struct_lockstep_tails_for_codegen(src_ty, tgt_ty, typing_env);
                match tgt_ty.kind() {
                    ty::Slice(_) | ty::Str => match src_ty.kind() {
                        ty::Array(_, len) => {
                            let len = rustc_internal::stable(len);
                            let len = self.translate_tyconst_to_const_generic(span, &len)?;
                            Ok(UnsizingMetadata::Length(len))
                        }
                        _ => {
                            trace!("Unknown unsize for {src_ty:?} => {tgt_ty:?}");
                            Ok(UnsizingMetadata::Unknown)
                        }
                    },
                    ty::Dynamic(_preds, ..) => {
                        // let vtable = if let Some(pred) = preds.principal() {
                        // } else {
                        // };
                        // let tgt_ty = rustc_internal::stable(tgt_ty);
                        // let tgt_ty_kind = tgt_ty.kind();
                        // use stable_mir::ty;
                        // let Some(ty::RigidTy::Dynamic(preds, r, k)) = tgt_ty_kind.rigid() else {
                        //     unreachable!();
                        // };

                        // let pred = preds[0].with_self_ty(tcx, src_ty);
                        // let clause = pred.as_trait_clause().expect(
                        //     "the first `ExistentialPredicate` of `TyKind::Dynamic` \
                        //         should be a trait clause",
                        // );
                        // let tref = clause.rebind(clause.skip_binder().trait_ref);
                        Ok(UnsizingMetadata::VTablePtr(TraitRef {
                            kind: TraitRefKind::Unknown("dyn not supported".into()),
                            trait_decl_ref: RegionBinder::empty(TraitDeclRef {
                                id: TraitDeclId::ZERO,
                                generics: Box::new(GenericArgs::empty()),
                            }),
                        }))
                    }
                    _ => {
                        trace!("Unknown unsize for {src_ty:?} => {tgt_ty:?}");
                        Ok(UnsizingMetadata::Unknown)
                    }
                }
            }
            _ => {
                trace!("Unknown unsize for {src_ty:?} => {tgt_ty:?}");
                Ok(UnsizingMetadata::Unknown)
            }
        }
    }

    fn translate_projection(
        &mut self,
        span: Span,
        of_place: Place,
        place_ty: stable_mir::ty::Ty,
        variant_id: Option<VariantId>,
        proj: &mir::ProjectionElem,
    ) -> Result<(Place, stable_mir::ty::Ty, Option<VariantId>), Error> {
        let proj_ty = proj.ty(place_ty)?;
        let ty = self.translate_ty(span, proj_ty)?;

        let proj_elem = match proj {
            mir::ProjectionElem::Deref => ProjectionElem::Deref,
            mir::ProjectionElem::Index(local) => {
                let var_id = self.translate_local(local).unwrap();
                let local = self.locals.place_for_var(var_id);
                ProjectionElem::Index {
                    offset: Box::new(Operand::Copy(local)),
                    from_end: false,
                }
            }
            mir::ProjectionElem::ConstantIndex {
                offset, from_end, ..
            } => {
                let idx = ConstantExpr {
                    value: RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Unsigned(
                        UIntTy::Usize,
                        *offset as u128,
                    ))),
                    ty: TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)).into_ty(),
                };
                ProjectionElem::Index {
                    offset: Box::new(Operand::Const(Box::new(idx))),
                    from_end: *from_end,
                }
            }
            mir::ProjectionElem::Subslice { from, to, from_end } => {
                let from = ConstantExpr {
                    value: RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Unsigned(
                        UIntTy::Usize,
                        *from as u128,
                    ))),
                    ty: TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)).into_ty(),
                };
                let to = ConstantExpr {
                    value: RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Unsigned(
                        UIntTy::Usize,
                        *to as u128,
                    ))),
                    ty: TyKind::Literal(LiteralTy::UInt(UIntTy::Usize)).into_ty(),
                };
                ProjectionElem::Subslice {
                    from: Box::new(Operand::Const(Box::new(from))),
                    to: Box::new(Operand::Const(Box::new(to))),
                    from_end: *from_end,
                }
            }
            mir::ProjectionElem::Downcast(variant) => {
                return Ok((of_place, proj_ty, Some(self.translate_variant_id(*variant))));
            }
            mir::ProjectionElem::Field(field_idx, _) => {
                let kind = match of_place.ty().kind() {
                    TyKind::Adt(TypeDeclRef {
                        id: TypeId::Tuple,
                        generics,
                    }) => FieldProjKind::Tuple(generics.types.elem_count()),
                    TyKind::Adt(TypeDeclRef {
                        id: TypeId::Adt(id),
                        ..
                    }) => FieldProjKind::Adt(*id, variant_id),
                    kind => unreachable!("Unexpected type in field projection: {kind:?}"),
                };
                ProjectionElem::Field(kind, FieldId::from_usize(*field_idx))
            }
            mir::ProjectionElem::OpaqueCast(..) => {
                raise_error!(self, span, "Unexpected ProjectionElem::OpaqueCast");
            }
            mir::ProjectionElem::Subtype(..) => {
                raise_error!(self, span, "Unexpected ProjectionElem::Subtype");
            }
        };
        let place = of_place.project(proj_elem, ty);
        Ok((place, proj_ty, None))
    }

    /// Translate a place
    /// TODO: Hax represents places in a different manner than MIR. We should
    /// update our representation of places to match the Hax representation.
    fn translate_place(&mut self, span: Span, place: &mir::Place) -> Result<Place, Error> {
        let var_id = self.translate_local(&place.local).unwrap();
        let local = self.locals.place_for_var(var_id);
        let local_ty = self.local_decls[place.local].ty;
        place
            .projection
            .iter()
            .try_fold(
                (local, local_ty, None),
                |(place, place_ty, variant), proj| {
                    self.translate_projection(span, place, place_ty, variant, proj)
                },
            )
            .map(|(place, _, _)| place)
    }

    /// Translate an operand with its type
    fn translate_operand_with_type(
        &mut self,
        span: Span,
        operand: &mir::Operand,
    ) -> Result<(Operand, Ty), Error> {
        match operand {
            mir::Operand::Copy(place) => {
                let p = self.translate_place(span, place)?;
                let ty = p.ty().clone();
                Ok((Operand::Copy(p), ty))
            }
            mir::Operand::Move(place) => {
                let p = self.translate_place(span, place)?;
                let ty = p.ty().clone();
                Ok((Operand::Move(p), ty))
            }
            mir::Operand::Constant(const_op) => {
                let ty = self.translate_ty(span, const_op.ty())?;
                let cexpr = match &const_op.const_.kind() {
                    stable_mir::ty::ConstantKind::Allocated(alloc) => {
                        self.translate_allocation(span, alloc, ty.kind(), &const_op.ty())?
                    }
                    stable_mir::ty::ConstantKind::ZeroSized => {
                        self.translate_zst_constant(span, ty.kind(), &const_op.ty())?
                    }
                    stable_mir::ty::ConstantKind::Param(_) => ConstantExpr {
                        value: RawConstantExpr::Opaque("Unhandled: Param".into()),
                        ty: ty.clone(),
                    },
                    stable_mir::ty::ConstantKind::Ty(_) => ConstantExpr {
                        value: RawConstantExpr::Opaque("Unhandled: ty".into()),
                        ty: ty.clone(),
                    },
                    stable_mir::ty::ConstantKind::Unevaluated(_) => ConstantExpr {
                        value: RawConstantExpr::Opaque("Unhandled: uneval".into()),
                        ty: ty.clone(),
                    },
                };
                Ok((Operand::Const(Box::new(cexpr)), ty))
            }
        }
    }

    /// Translate an operand
    fn translate_operand(&mut self, span: Span, operand: &mir::Operand) -> Result<Operand, Error> {
        Ok(self.translate_operand_with_type(span, operand)?.0)
    }

    /// Translate a `BorrowKind`
    fn translate_borrow_kind(&mut self, borrow_kind: mir::BorrowKind) -> BorrowKind {
        match borrow_kind {
            mir::BorrowKind::Shared => BorrowKind::Shared,
            mir::BorrowKind::Mut { kind } => match kind {
                mir::MutBorrowKind::Default => BorrowKind::Mut,
                mir::MutBorrowKind::TwoPhaseBorrow => BorrowKind::TwoPhaseMut,
                mir::MutBorrowKind::ClosureCapture => BorrowKind::UniqueImmutable,
            },
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Shallow) => BorrowKind::Shallow,
            // This one is used only in deref patterns.
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Deep) => unimplemented!(),
        }
    }

    /// Translate an rvalue
    fn translate_rvalue(&mut self, span: Span, rvalue: &mir::Rvalue) -> Result<Rvalue, Error> {
        match rvalue {
            mir::Rvalue::Use(operand) => Ok(Rvalue::Use(self.translate_operand(span, operand)?)),
            mir::Rvalue::CopyForDeref(place) => {
                // According to the documentation, it seems to be an optimisation
                // for drop elaboration. We treat it as a regular copy.
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::Use(Operand::Copy(place)))
            }
            mir::Rvalue::Repeat(operand, cnst) => {
                let c = self.translate_tyconst_to_const_generic(span, cnst)?;
                let (operand, t) = self.translate_operand_with_type(span, operand)?;
                // Remark: we could desugar this into a function call later.
                Ok(Rvalue::Repeat(operand, t, c))
            }
            mir::Rvalue::Ref(_region, borrow_kind, place) => {
                let place = self.translate_place(span, place)?;
                let borrow_kind = self.translate_borrow_kind(*borrow_kind);
                Ok(Rvalue::Ref(place, borrow_kind))
            }
            mir::Rvalue::AddressOf(mtbl, place) => {
                let mtbl = match mtbl {
                    mir::RawPtrKind::Mut => RefKind::Mut,
                    mir::RawPtrKind::Const => RefKind::Shared,
                    mir::RawPtrKind::FakeForPtrMetadata => RefKind::Shared,
                };
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::RawPtr(place, mtbl))
            }
            mir::Rvalue::Len(place) => {
                let place = self.translate_place(span, place)?;
                let ty = place.ty().clone();
                let tref = ty.as_adt().unwrap();
                let cg = match tref.id {
                    TypeId::Builtin(BuiltinTy::Array) => {
                        Some(tref.generics.const_generics[0].clone())
                    }
                    TypeId::Builtin(BuiltinTy::Slice) => None,
                    _ => unreachable!(),
                };
                Ok(Rvalue::Len(place, ty, cg))
            }
            mir::Rvalue::Cast(cast_kind, mir_operand, mir_tgt_ty) => {
                trace!("Rvalue::Cast: {:?}", rvalue);
                // Translate the target type
                let tgt_ty = self.translate_ty(span, *mir_tgt_ty)?;

                // Translate the operand
                let (mut operand, src_ty) = self.translate_operand_with_type(span, mir_operand)?;

                let cast_kind = match cast_kind {
                    mir::CastKind::IntToInt
                    | mir::CastKind::IntToFloat
                    | mir::CastKind::FloatToInt
                    | mir::CastKind::FloatToFloat => {
                        let tgt_ty = *tgt_ty.kind().as_literal().unwrap();
                        let src_ty = *src_ty.kind().as_literal().unwrap();
                        CastKind::Scalar(src_ty, tgt_ty)
                    }
                    mir::CastKind::PointerCoercion(
                        mir::PointerCoercion::ClosureFnPointer(_),
                        ..,
                    ) => {
                        let op_ty = mir_operand.ty(self.local_decls)?;
                        let op_ty_kind = op_ty.kind();
                        let Some(ty::RigidTy::Closure(def, args)) = op_ty_kind.rigid() else {
                            raise_error!(self, span, "ClosureFnPointer without closure?");
                        };
                        let fn_id = self.register_closure_as_fn_id(span, *def, args.clone());
                        let fn_ptr = FnPtr {
                            func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(fn_id))),
                            generics: Box::new(GenericArgs::empty()),
                        };
                        let src_ty = TyKind::FnDef(RegionBinder::empty(fn_ptr.clone())).into_ty();
                        operand = Operand::Const(Box::new(ConstantExpr {
                            value: RawConstantExpr::FnPtr(fn_ptr),
                            ty: src_ty.clone(),
                        }));
                        CastKind::FnPtr(src_ty, tgt_ty)
                    }
                    mir::CastKind::PtrToPtr
                    | mir::CastKind::FnPtrToPtr
                    | mir::CastKind::PointerExposeAddress
                    | mir::CastKind::PointerWithExposedProvenance
                    | mir::CastKind::PointerCoercion(
                        mir::PointerCoercion::MutToConstPointer
                        | mir::PointerCoercion::ArrayToPointer,
                        ..,
                    ) => CastKind::RawPtr(src_ty, tgt_ty),
                    mir::CastKind::PointerCoercion(
                        mir::PointerCoercion::UnsafeFnPointer
                        | mir::PointerCoercion::ReifyFnPointer,
                        ..,
                    ) => CastKind::FnPtr(src_ty, tgt_ty),
                    mir::CastKind::Transmute => CastKind::Transmute(src_ty, tgt_ty),
                    mir::CastKind::PointerCoercion(mir::PointerCoercion::Unsize) => {
                        let mir_src_ty = mir_operand.ty(self.local_decls)?;
                        let unsizing_meta =
                            self.translate_unsizing_metadata(span, mir_src_ty, *mir_tgt_ty)?;
                        CastKind::Unsize(src_ty.clone(), tgt_ty.clone(), unsizing_meta)
                    }
                };
                Ok(Rvalue::UnaryOp(UnOp::Cast(cast_kind), operand))
            }
            mir::Rvalue::BinaryOp(binop, left, right) => Ok(Rvalue::BinaryOp(
                self.translate_binaryop_kind(span, *binop)?,
                self.translate_operand(span, left)?,
                self.translate_operand(span, right)?,
            )),
            mir::Rvalue::CheckedBinaryOp(binop, left, right) => Ok(Rvalue::BinaryOp(
                self.translate_checked_binaryop_kind(span, *binop)?,
                self.translate_operand(span, left)?,
                self.translate_operand(span, right)?,
            )),
            mir::Rvalue::NullaryOp(nullop, ty) => {
                trace!("NullOp: {:?}", nullop);
                let ty = self.translate_ty(span, *ty)?;
                let op = match nullop {
                    mir::NullOp::SizeOf => NullOp::SizeOf,
                    mir::NullOp::AlignOf => NullOp::AlignOf,
                    mir::NullOp::OffsetOf(fields) => NullOp::OffsetOf(
                        fields
                            .iter()
                            .copied()
                            .map(|(n, idx)| (n.to_index(), FieldId::new(idx)))
                            .collect(),
                    ),
                    mir::NullOp::UbChecks => NullOp::UbChecks,
                    mir::NullOp::ContractChecks => {
                        raise_error!(self, span, "charon does not support contracts");
                    }
                };
                Ok(Rvalue::NullaryOp(op, ty))
            }
            mir::Rvalue::UnaryOp(unop, operand) => {
                let unop = match unop {
                    mir::UnOp::Not => UnOp::Not,
                    mir::UnOp::Neg => UnOp::Neg(OverflowMode::UB),
                    mir::UnOp::PtrMetadata => UnOp::PtrMetadata,
                };
                Ok(Rvalue::UnaryOp(
                    unop,
                    self.translate_operand(span, operand)?,
                ))
            }
            mir::Rvalue::Discriminant(place) => {
                let place = self.translate_place(span, place)?;
                Ok(Rvalue::Discriminant(place))
            }
            mir::Rvalue::Aggregate(aggregate_kind, operands) => {
                // It seems this instruction is not present in certain passes:
                // for example, it seems it is not used in optimized MIR, where
                // ADT initialization is split into several instructions, for
                // instance:
                // ```
                // p = Pair { x:xv, y:yv };
                // ```
                // Might become:
                // ```
                // p.x = x;
                // p.y = yv;
                // ```

                // First translate the operands
                let operands_t: Vec<Operand> = operands
                    .iter()
                    .map(|op| self.translate_operand(span, op))
                    .try_collect()?;

                match aggregate_kind {
                    mir::AggregateKind::Array(ty) => {
                        let t_ty = self.translate_ty(span, *ty)?;
                        let cg = ConstGeneric::Value(Literal::Scalar(ScalarValue::Unsigned(
                            UIntTy::Usize,
                            operands_t.len() as u128,
                        )));
                        Ok(Rvalue::Aggregate(
                            AggregateKind::Array(t_ty, cg),
                            operands_t,
                        ))
                    }
                    mir::AggregateKind::Tuple => {
                        let tref = TypeDeclRef::new(TypeId::Tuple, GenericArgs::empty());
                        Ok(Rvalue::Aggregate(
                            AggregateKind::Adt(tref, None, None),
                            operands_t,
                        ))
                    }
                    mir::AggregateKind::Adt(
                        item,
                        variant_idx,
                        generics,
                        _user_annotation,
                        field_index,
                    ) => {
                        use stable_mir::ty::AdtKind;
                        trace!("{:?}", rvalue);

                        let id = self.register_type_decl_id(span, *item, generics.clone());
                        let tref = TypeDeclRef {
                            id: TypeId::Adt(id),
                            generics: Box::new(GenericArgs::empty()),
                        };
                        let variant_id = match item.kind() {
                            AdtKind::Struct | AdtKind::Union => None,
                            AdtKind::Enum => Some(self.translate_variant_id(*variant_idx)),
                        };
                        let field_id = match item.kind() {
                            AdtKind::Struct | AdtKind::Enum => None,
                            AdtKind::Union => Some(self.translate_field_id(field_index.unwrap())),
                        };

                        let akind = AggregateKind::Adt(tref, variant_id, field_id);
                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    mir::AggregateKind::Closure(def, args) => {
                        let id = self.register_closure_type_decl_id(span, *def, args.clone());
                        let tref = TypeDeclRef {
                            id: TypeId::Adt(id),
                            generics: Box::new(GenericArgs::empty()),
                        };
                        let akind = AggregateKind::Adt(tref, None, None);
                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    mir::AggregateKind::RawPtr(ty, is_mut) => {
                        // TODO: replace with a call to `ptr::from_raw_parts`.
                        let t_ty = self.translate_ty(span, *ty)?;
                        let mutability = if matches!(is_mut, mir::Mutability::Mut) {
                            RefKind::Mut
                        } else {
                            RefKind::Shared
                        };

                        let akind = AggregateKind::RawPtr(t_ty, mutability);

                        Ok(Rvalue::Aggregate(akind, operands_t))
                    }
                    mir::AggregateKind::Coroutine(..)
                    | mir::AggregateKind::CoroutineClosure(..) => {
                        raise_error!(self, span, "Coroutines are not supported");
                    }
                }
            }
            mir::Rvalue::ShallowInitBox(op, ty) => {
                let op = self.translate_operand(span, op)?;
                let ty = self.translate_ty(span, *ty)?;
                Ok(Rvalue::ShallowInitBox(op, ty))
            }
            mir::Rvalue::ThreadLocalRef(_) => {
                raise_error!(
                    self,
                    span,
                    "charon does not support thread local references"
                );
            }
        }
    }

    /// Translate a statement
    ///
    /// We return an option, because we ignore some statements (`Nop`, `StorageLive`...)
    fn translate_statement(
        &mut self,
        statement: &mir::Statement,
    ) -> Result<Option<Statement>, Error> {
        trace!("About to translate statement (MIR) {:?}", statement);
        let span = self.t_ctx.translate_span_from_smir(&statement.span);

        use mir::StatementKind;
        let t_statement: Option<RawStatement> = match &statement.kind {
            StatementKind::Assign(place, rvalue) => {
                let t_place = self.translate_place(span, &place)?;
                let t_rvalue = self.translate_rvalue(span, &rvalue)?;
                Some(RawStatement::Assign(t_place, t_rvalue))
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let t_place = self.translate_place(span, &place)?;
                let variant_id = self.translate_variant_id(*variant_index);
                Some(RawStatement::SetDiscriminant(t_place, variant_id))
            }
            StatementKind::StorageLive(local) => {
                let var_id = self.translate_local(&local).unwrap();
                Some(RawStatement::StorageLive(var_id))
            }
            StatementKind::StorageDead(local) => {
                let var_id = self.translate_local(&local).unwrap();
                Some(RawStatement::StorageDead(var_id))
            }
            StatementKind::Deinit(place) => {
                let t_place = self.translate_place(span, &place)?;
                Some(RawStatement::Deinit(t_place))
            }
            // This asserts the operand true on pain of UB. We treat it like a normal assertion.
            StatementKind::Intrinsic(mir::NonDivergingIntrinsic::Assume(op)) => {
                let op = self.translate_operand(span, &op)?;
                Some(RawStatement::Assert(Assert {
                    cond: op,
                    expected: true,
                    on_failure: AbortKind::UndefinedBehavior,
                }))
            }
            StatementKind::Intrinsic(mir::NonDivergingIntrinsic::CopyNonOverlapping(
                mir::CopyNonOverlapping { src, dst, count },
            )) => {
                let src = self.translate_operand(span, &src)?;
                let dst = self.translate_operand(span, &dst)?;
                let count = self.translate_operand(span, &count)?;
                Some(RawStatement::CopyNonOverlapping(Box::new(
                    CopyNonOverlapping { src, dst, count },
                )))
            }
            // This is for the stacked borrows memory model.
            StatementKind::Retag(_, _) => None,
            // These two are only there to make borrow-checking accept less code, and are removed
            // in later MIRs.
            StatementKind::FakeRead(..) | StatementKind::PlaceMention(..) => None,
            // There are user-provided type annotations with no semantic effect (since we get a
            // fully-typechecked MIR (TODO: this isn't quite true with opaque types, we should
            // really use promoted MIR)).
            StatementKind::AscribeUserType { .. } => None,
            // Used for coverage instrumentation.
            StatementKind::Coverage(_) => None,
            // Used in the interpreter to check that const code doesn't run for too long or even
            // indefinitely.
            StatementKind::ConstEvalCounter => None,
            // Semantically equivalent to `Nop`, used only for rustc lints.
            StatementKind::Nop => None,
        };

        // Add the span information
        Ok(t_statement.map(|kind| Statement::new(span, kind)))
    }

    /// Translate a terminator
    fn translate_terminator(
        &mut self,
        terminator: &mir::Terminator,
        statements: &mut Vec<Statement>,
    ) -> Result<Terminator, Error> {
        trace!("About to translate terminator (MIR) {:?}", terminator);
        // Compute the span information beforehand (we might need it to introduce
        // intermediate statements - we desugar some terminators)
        let span = self.translate_span_from_smir(&terminator.span);

        // Translate the terminator
        use mir::TerminatorKind;
        let t_terminator: RawTerminator = match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                // Translate the operand which gives the discriminant
                let (discr, discr_ty) = self.translate_operand_with_type(span, discr)?;

                // Translate the switch targets
                // let targets = targets.
                let targets = self.translate_switch_targets(span, &discr_ty, targets)?;

                RawTerminator::Switch { discr, targets }
            }
            TerminatorKind::Resume => RawTerminator::UnwindResume,
            TerminatorKind::Abort => RawTerminator::Abort(AbortKind::UnwindTerminate),
            TerminatorKind::Return => RawTerminator::Return,
            // A MIR `Unreachable` terminator indicates undefined behavior of the rust abstract
            // machine.
            TerminatorKind::Unreachable => RawTerminator::Abort(AbortKind::UndefinedBehavior),
            TerminatorKind::Drop {
                place,
                target,
                unwind, // We consider that panic is an error, and don't model unwinding
            } => 'drop_case: {
                let target = self.translate_basic_block_id(*target);
                let place_ty = place.ty(self.local_decls)?;
                let drop_shim = mir::mono::Instance::resolve_drop_in_place(place_ty);

                if drop_shim.is_empty_shim() {
                    // If the drop shim is empty, we don't need to do anything.
                    break 'drop_case RawTerminator::Goto { target };
                }

                let place = self.translate_place(span, place)?;

                // need to make a pointer to the local we're dropping
                let ptr_place = self.locals.new_var(
                    None,
                    TyKind::RawPtr(place.ty.clone(), RefKind::Mut).into_ty(),
                );
                let unit_place = self.locals.new_var(None, Ty::mk_unit());
                statements.push(Statement::new(
                    span,
                    RawStatement::Assign(ptr_place.clone(), Rvalue::RawPtr(place, RefKind::Mut)),
                ));
                let operand = Operand::Move(ptr_place);

                let drop_fn_id = self.register_fun_decl_id(span, drop_shim);
                let on_unwind = self.translate_unwind(span, unwind);

                RawTerminator::Call {
                    call: Call {
                        func: FnOperand::Regular(FnPtr {
                            func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(drop_fn_id))),
                            generics: Box::new(GenericArgs::empty()),
                        }),
                        args: vec![operand],
                        dest: unit_place,
                    },
                    target,
                    on_unwind,
                }
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
            } => {
                let (term, stt) =
                    self.translate_function_call(span, func, args, destination, target, unwind)?;
                if let Some(stt) = stt {
                    statements.push(Statement::new(span, stt));
                };
                term
            }
            TerminatorKind::Assert {
                cond,
                expected,
                msg: _,
                target,
                unwind: _, // We model unwinding as an effet, we don't represent it in control flow
            } => {
                let assert = Assert {
                    cond: self.translate_operand(span, cond)?,
                    expected: *expected,
                    on_failure: AbortKind::Panic(None),
                };
                statements.push(Statement::new(span, RawStatement::Assert(assert)));
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
            }
            TerminatorKind::InlineAsm { .. } => {
                raise_error!(self, span, "Inline assembly is not supported");
            }
        };

        // Add the span information
        Ok(Terminator::new(span, t_terminator))
    }

    /// Translate switch targets
    fn translate_switch_targets(
        &mut self,
        span: Span,
        switch_ty: &Ty,
        targets: &mir::SwitchTargets,
    ) -> Result<SwitchTargets, Error> {
        trace!("targets: {:?}", targets);
        let switch_ty = *switch_ty.kind().as_literal().unwrap();
        match switch_ty {
            LiteralTy::Bool => {
                assert_eq!(targets.len(), 2);
                let (val, target) = targets.branches().next().unwrap();
                // It seems the block targets are inverted
                assert_eq!(val, 0u128);
                let if_block = self.translate_basic_block_id(targets.otherwise());
                let else_block = self.translate_basic_block_id(target);
                Ok(SwitchTargets::If(if_block, else_block))
            }
            LiteralTy::Int(int_ty) => {
                let targets_ullbc: Vec<(ScalarValue, BlockId)> = targets
                    .branches()
                    .map(|(v, tgt)| {
                        let v =
                            ScalarValue::from_le_bytes(IntegerTy::Signed(int_ty), v.to_le_bytes());
                        let tgt = self.translate_basic_block_id(tgt);
                        (v, tgt)
                    })
                    .collect();
                let otherwise = self.translate_basic_block_id(targets.otherwise());
                Ok(SwitchTargets::SwitchInt(
                    IntegerTy::Signed(int_ty),
                    targets_ullbc,
                    otherwise,
                ))
            }
            LiteralTy::UInt(uint_ty) => {
                let targets_ullbc: Vec<(ScalarValue, BlockId)> = targets
                    .branches()
                    .map(|(v, tgt)| {
                        let v = ScalarValue::from_le_bytes(
                            IntegerTy::Unsigned(uint_ty),
                            v.to_le_bytes(),
                        );
                        let tgt = self.translate_basic_block_id(tgt);
                        (v, tgt)
                    })
                    .collect();
                let otherwise = self.translate_basic_block_id(targets.otherwise());
                Ok(SwitchTargets::SwitchInt(
                    IntegerTy::Unsigned(uint_ty),
                    targets_ullbc,
                    otherwise,
                ))
            }
            _ => raise_error!(self, span, "Can't match on type {switch_ty}"),
        }
    }

    fn translate_unwind(&mut self, span: Span, unwind: &mir::UnwindAction) -> BlockId {
        match unwind {
            mir::UnwindAction::Continue => {
                let unwind_continue = Terminator::new(span, RawTerminator::UnwindResume);
                self.blocks.push(unwind_continue.into_block())
            }
            mir::UnwindAction::Unreachable => {
                let abort =
                    Terminator::new(span, RawTerminator::Abort(AbortKind::UndefinedBehavior));
                self.blocks.push(abort.into_block())
            }
            mir::UnwindAction::Terminate => {
                let abort = Terminator::new(span, RawTerminator::Abort(AbortKind::UnwindTerminate));
                self.blocks.push(abort.into_block())
            }
            mir::UnwindAction::Cleanup(bb) => self.translate_basic_block_id(*bb),
        }
    }

    /// Translate a function call statement.
    /// Note that `body` is the body of the function being translated, not of the
    /// function referenced in the function call: we need it in order to translate
    /// the blocks we go to after the function call returns.
    #[allow(clippy::too_many_arguments)]
    fn translate_function_call(
        &mut self,
        span: Span,
        fun: &mir::Operand,
        args: &Vec<mir::Operand>,
        destination: &mir::Place,
        target: &Option<usize>,
        unwind: &mir::UnwindAction,
    ) -> Result<(RawTerminator, Option<RawStatement>), Error> {
        // There are two cases, depending on whether this is a "regular"
        // call to a top-level function identified by its id, or if we
        // are using a local function pointer (i.e., the operand is a "move").
        let lval = self.translate_place(span, destination)?;
        // Translate the function operand.
        let fn_ty = fun.ty(self.local_decls)?;
        let mut extra_stt = None;
        let fn_operand = match fn_ty.kind() {
            ty::TyKind::RigidTy(ty::RigidTy::FnDef(fn_def, args)) => {
                let instance = mir::mono::Instance::resolve(fn_def, &args)?;

                // If this is a VTable call, do something else
                // if let mir::mono::InstanceKind::Virtual { .. } = instance.kind {};

                let fn_id = self.register_fun_decl_id(span, instance);
                let fn_ptr = FnPtr {
                    func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(fn_id))),
                    generics: Box::new(GenericArgs::empty()),
                };
                FnOperand::Regular(fn_ptr)
            }
            _ => {
                let (mir::Operand::Move(place) | mir::Operand::Copy(place)) = fun else {
                    raise_error!(
                        self,
                        span,
                        "Expected a move/copy function pointer operand, got constant {fun:?}"
                    );
                };
                // Call to a local function pointer
                let p = self.translate_place(span, place)?;

                if matches!(fun, mir::Operand::Copy(_)) {
                    // Charon doesn't allow copy as a fn operand, so we create a temporary
                    // variable that copies the value, and then move that
                    let local_id = self.locals.locals.push_with(|index| Local {
                        index,
                        name: None,
                        ty: p.ty.clone(),
                    });
                    let new_place = Place::new(local_id, p.ty.clone());
                    extra_stt = Some(RawStatement::Assign(
                        new_place.clone(),
                        Rvalue::Use(Operand::Copy(p)),
                    ));
                    FnOperand::Move(new_place)
                } else {
                    FnOperand::Move(p)
                }
            }
        };
        let args = self.translate_arguments(span, args)?;
        let call = Call {
            func: fn_operand,
            args,
            dest: lval,
        };

        let target = match target {
            Some(target) => self.translate_basic_block_id(*target),
            None => {
                let abort =
                    Terminator::new(span, RawTerminator::Abort(AbortKind::UndefinedBehavior));
                self.blocks.push(abort.into_block())
            }
        };
        let on_unwind = self.translate_unwind(span, unwind);
        Ok((
            RawTerminator::Call {
                call,
                target,
                on_unwind,
            },
            extra_stt,
        ))
    }

    /// Evaluate function arguments in a context, and return the list of computed
    /// values.
    fn translate_arguments(
        &mut self,
        span: Span,
        args: &Vec<mir::Operand>,
    ) -> Result<Vec<Operand>, Error> {
        args.iter()
            .map(|arg| self.translate_operand(span, arg))
            .try_collect()
    }

    // The body is translated as if the locals are: ret value, state, arg-1,
    // ..., arg-N, rest...
    // However, there is only one argument with the tupled closure arguments;
    // we must thus shift all locals with index >=2 by 1, and add a new local
    // for the tupled arg, giving us: ret value, state, args, arg-1, ...,
    // arg-N, rest...
    // We then add N statements of the form `locals[N+3] := move locals[2].N`,
    // to destructure the arguments.
    fn untuple_closure_arguments(&mut self, instance: mir::mono::Instance) -> Result<(), Error> {
        // We need to figure out if this is a closure;

        // 1. Only closures
        if !self.instance_is_closure(instance) {
            return Ok(());
        }

        // 2. There is a first argument
        let Ok(abi) = instance.fn_abi() else {
            return Ok(());
        };
        let Some(abi::ArgAbi { ty, .. }) = abi.args.get(0) else {
            return Ok(());
        };

        // 3. This argument is a closure !
        let ty_kind = ty.kind();
        let (_, generics) = match ty_kind.rigid() {
            Some(ty::RigidTy::Closure(def, generics)) => (def.clone(), generics.clone()),
            Some(ty::RigidTy::Ref(_, subty, _)) => {
                let ty_kind = subty.kind();
                match ty_kind.rigid() {
                    Some(ty::RigidTy::Closure(def, generics)) => (def.clone(), generics.clone()),
                    _ => return Ok(()),
                }
            }
            _ => return Ok(()),
        };

        // 4. Fetch the closure's signature from its generics -- see:
        // https://doc.rust-lang.org/beta/nightly-rustc/src/rustc_type_ir/ty_kind/closure.rs.html#12-29
        let [.., ty::GenericArgKind::Type(fnptr_ty), _] = generics.0.as_slice() else {
            return Ok(());
        };
        let fn_ptr_ty_kind = fnptr_ty.kind();
        let Some(ty::RigidTy::FnPtr(fn_sig)) = fn_ptr_ty_kind.rigid() else {
            return Ok(());
        };
        let [inputs_tupled] = fn_sig.value.inputs() else {
            return Ok(());
        };

        // Let's get to work...

        let tupled_inputs_ty = self.translate_ty(Span::dummy(), *inputs_tupled)?;

        self.blocks.dyn_visit_mut(|local: &mut LocalId| {
            let idx = local.index();
            if idx >= 2 {
                *local = LocalId::new(idx + 1)
            }
        });

        let mut old_locals = mem::take(&mut self.locals.locals).into_iter();
        self.locals.arg_count = 2;
        self.locals.locals.push(old_locals.next().unwrap()); // ret
        self.locals.locals.push(old_locals.next().unwrap()); // state
        let tupled_arg = self
            .locals
            .new_var(Some("tupled_args".to_string()), tupled_inputs_ty.clone());
        self.locals.locals.extend(old_locals.map(|mut l| {
            l.index += 1;
            l
        }));

        let untupled_args = tupled_inputs_ty.as_tuple().unwrap();
        let closure_arg_count = untupled_args.elem_count();
        let new_stts = untupled_args.iter().cloned().enumerate().map(|(i, ty)| {
            let nth_field = tupled_arg.clone().project(
                ProjectionElem::Field(FieldProjKind::Tuple(closure_arg_count), FieldId::new(i)),
                ty,
            );
            Statement::new(
                Span::dummy(),
                RawStatement::Assign(
                    self.locals.place_for_var(LocalId::new(i + 3)),
                    Rvalue::Use(Operand::Move(nth_field)),
                ),
            )
        });
        self.blocks[BlockId::ZERO].statements.splice(0..0, new_stts);
        Ok(())
    }

    /// Translate a function body.
    pub fn translate_body(
        &mut self,
        span: Span,
        instance: mir::mono::Instance,
        body: &mir::Body,
    ) -> Result<Result<Body, Opaque>, Error> {
        // Stopgap measure because there are still many panics in charon and hax.
        let mut this = panic::AssertUnwindSafe(&mut *self);
        let res = panic::catch_unwind(move || this.translate_body_aux(instance, body));
        match res {
            Ok(Ok(body)) => Ok(body),
            // Translation error
            Ok(Err(e)) => Err(e),
            Err(_) => {
                raise_error!(self, span, "Thread panicked when extracting body.");
            }
        }
    }

    fn translate_body_aux(
        &mut self,
        instance: mir::mono::Instance,
        body: &mir::Body,
    ) -> Result<Result<Body, Opaque>, Error> {
        // Compute the span information
        let span = self.translate_span_from_smir(&body.span);

        // Initialize the local variables
        trace!("Translating the body locals");
        let (inputs, _) = self.get_function_ins_outs(span, instance)?;
        self.locals.arg_count = inputs.len();
        self.translate_body_locals(&body)?;

        // Translate the expression body
        trace!("Translating the expression body");

        // Register the start block
        let id = self.translate_basic_block_id(0);
        assert!(id == START_BLOCK_ID);

        // For as long as there are blocks in the stack, translate them
        while let Some(mir_block_id) = self.blocks_stack.pop_front() {
            let mir_block = body.blocks.get(mir_block_id).unwrap();
            let block_id = self.translate_basic_block_id(mir_block_id);
            let block = self.translate_basic_block(mir_block)?;
            self.blocks.set_slot(block_id, block);
        }

        // If we're translating a closure, we need to tuple up the arguments!
        self.untuple_closure_arguments(instance)?;

        // Create the body
        Ok(Ok(Body::Unstructured(ExprBody {
            span,
            locals: mem::take(&mut self.locals),
            body: mem::take(&mut self.blocks),
            comments: vec![],
        })))
    }
}
