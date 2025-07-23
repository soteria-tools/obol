extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_smir;
extern crate rustc_span;
extern crate stable_mir;

use log::trace;
use rustc_smir::IndexedVal;
use stable_mir::{
    mir,
    ty::{self},
};
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

pub fn lift_err<T>(res: Result<T, stable_mir::Error>) -> Result<T, charon_lib::errors::Error> {
    match res {
        Ok(val) => Ok(val),
        Err(err) => Err(Error {
            span: Span::dummy(),
            msg: err.to_string(),
        }),
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

impl BodyTransCtx<'_, '_, '_> {
    pub(crate) fn translate_local(&self, local: &mir::Local) -> Option<LocalId> {
        self.locals_map.get(local).copied()
    }

    fn translate_variant_id(&self, id: stable_mir::ty::VariantIdx) -> VariantId {
        VariantId::new(id.to_index())
    }

    fn translate_field_id(&self, id: mir::FieldIdx) -> FieldId {
        FieldId::new(id)
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

    fn translate_projection(
        &mut self,
        span: Span,
        of_place: Place,
        place_ty: stable_mir::ty::Ty,
        variant_id: Option<VariantId>,
        proj: &mir::ProjectionElem,
    ) -> Result<(Place, stable_mir::ty::Ty, Option<VariantId>), Error> {
        let proj_ty = lift_err(proj.ty(place_ty))?;
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
        let (place, _, _) =
            place
                .projection
                .iter()
                .fold(Ok((local, local_ty, None)), |res, proj| {
                    let (place, place_ty, variant) = res?;
                    self.translate_projection(span, place, place_ty, variant, proj)
                })?;
        Ok(place)
        // match &place.kind {
        //     mir::PlaceKind::Local(local) => {
        //         let var_id = self.translate_local(local).unwrap();
        //         Ok(self.locals.place_for_var(var_id))
        //     }
        //     mir::PlaceKind::Projection {
        //         place: hax_subplace,
        //         kind,
        //     } => {
        //         let ty = self.translate_ty(span, &place.ty)?;
        //         // Compute the type of the value *before* projection - we use this
        //         // to disambiguate
        //         let subplace = self.translate_place(span, hax_subplace)?;
        //         let place = match kind {
        //             mir::ProjectionElem::Deref => subplace.project(ProjectionElem::Deref, ty),
        //             mir::ProjectionElem::Field(field_kind) => {
        //                 use mir::ProjectionElemFieldKind::*;
        //                 let proj_elem = match field_kind {
        //                     Tuple(id) => {
        //                         let tref = subplace.ty().kind().as_adt().unwrap();
        //                         let field_id = translate_field_id(*id);
        //                         let proj_kind =
        //                             FieldProjKind::Tuple(tref.generics.types.elem_count());
        //                         ProjectionElem::Field(proj_kind, field_id)
        //                     }
        //                     Adt {
        //                         typ: _,
        //                         variant,
        //                         index,
        //                     } => {
        //                         let field_id = translate_field_id(*index);
        //                         let variant_id = variant.map(translate_variant_id);
        //                         let tref = subplace.ty().kind().as_adt().unwrap();
        //                         let generics = &tref.generics;
        //                         match tref.id {
        //                             TypeId::Adt(type_id) => {
        //                                 let proj_kind = FieldProjKind::Adt(type_id, variant_id);
        //                                 ProjectionElem::Field(proj_kind, field_id)
        //                             }
        //                             TypeId::Tuple => {
        //                                 assert!(generics.regions.is_empty());
        //                                 assert!(variant.is_none());
        //                                 assert!(generics.const_generics.is_empty());
        //                                 let proj_kind =
        //                                     FieldProjKind::Tuple(generics.types.elem_count());
        //                                 ProjectionElem::Field(proj_kind, field_id)
        //                             }
        //                             TypeId::Builtin(BuiltinTy::Box) => {
        //                                 // Some more sanity checks
        //                                 assert!(generics.regions.is_empty());
        //                                 assert!(generics.types.elem_count() == 1);
        //                                 assert!(generics.const_generics.is_empty());
        //                                 assert!(variant_id.is_none());
        //                                 assert!(field_id == FieldId::ZERO);
        //                                 ProjectionElem::Deref
        //                             }
        //                             _ => raise_error!(self, span, "Unexpected field projection"),
        //                         }
        //                     }
        //                     ClosureState(index) => {
        //                         let field_id = translate_field_id(*index);
        //                         let type_id = *subplace
        //                             .ty
        //                             .kind()
        //                             .as_adt()
        //                             .expect("ClosureState projection should apply to an Adt type")
        //                             .id
        //                             .as_adt()
        //                             .unwrap();
        //                         ProjectionElem::Field(FieldProjKind::Adt(type_id, None), field_id)
        //                     }
        //                 };
        //                 subplace.project(proj_elem, ty)
        //             }
        //             mir::ProjectionElem::Index(local) => {
        //                 let var_id = self.translate_local(local).unwrap();
        //                 let local = self.locals.place_for_var(var_id);
        //                 let offset = Operand::Copy(local);
        //                 subplace.project(
        //                     ProjectionElem::Index {
        //                         offset: Box::new(offset),
        //                         from_end: false,
        //                     },
        //                     ty,
        //                 )
        //             }
        //             mir::ProjectionElem::Downcast(..) => {
        //                 // We view it as a nop (the information from the
        //                 // downcast has been propagated to the other
        //                 // projection elements by Hax)
        //                 subplace
        //             }
        //             &mir::ProjectionElem::ConstantIndex {
        //                 offset,
        //                 from_end,
        //                 min_length: _,
        //             } => {
        //                 let offset =
        //                     Operand::Const(Box::new(ScalarValue::Usize(offset).to_constant()));
        //                 subplace.project(
        //                     ProjectionElem::Index {
        //                         offset: Box::new(offset),
        //                         from_end,
        //                     },
        //                     ty,
        //                 )
        //             }
        //             &mir::ProjectionElem::Subslice { from, to, from_end } => {
        //                 let from = Operand::Const(Box::new(ScalarValue::Usize(from).to_constant()));
        //                 let to = Operand::Const(Box::new(ScalarValue::Usize(to).to_constant()));
        //                 subplace.project(
        //                     ProjectionElem::Subslice {
        //                         from: Box::new(from),
        //                         to: Box::new(to),
        //                         from_end,
        //                     },
        //                     ty,
        //                 )
        //             }
        //             mir::ProjectionElem::OpaqueCast => {
        //                 // Don't know what that is
        //                 raise_error!(self, span, "Unexpected ProjectionElem::OpaqueCast");
        //             }
        //         };

        //         // Return
        //         Ok(place)
        //     }
        // }
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
                        self.translate_allocation(span, alloc, ty.kind())?
                    }
                    stable_mir::ty::ConstantKind::Param(_) => {
                        RawConstantExpr::Opaque("Unhandled: Param".into())
                    }
                    stable_mir::ty::ConstantKind::Ty(_) => {
                        RawConstantExpr::Opaque("Unhandled: Ty".into())
                    }
                    stable_mir::ty::ConstantKind::Unevaluated(_) => {
                        RawConstantExpr::Opaque("Unhandled: Unevaluated".into())
                    }
                    stable_mir::ty::ConstantKind::ZeroSized => {
                        self.translate_zst_constant(span, ty.kind())?
                    }
                };
                Ok((
                    Operand::Const(Box::new(ConstantExpr {
                        ty: ty.clone(),
                        value: cexpr,
                    })),
                    ty,
                ))
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
            mir::Rvalue::Cast(cast_kind, hax_operand, tgt_ty) => {
                trace!("Rvalue::Cast: {:?}", rvalue);
                // Translate the target type
                let tgt_ty = self.translate_ty(span, *tgt_ty)?;

                // Translate the operand
                let (operand, src_ty) = self.translate_operand_with_type(span, hax_operand)?;

                match cast_kind {
                    mir::CastKind::IntToInt
                    | mir::CastKind::IntToFloat
                    | mir::CastKind::FloatToInt
                    | mir::CastKind::FloatToFloat => {
                        let tgt_ty = *tgt_ty.kind().as_literal().unwrap();
                        let src_ty = *src_ty.kind().as_literal().unwrap();
                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::Scalar(src_ty, tgt_ty)),
                            operand,
                        ))
                    }
                    mir::CastKind::PointerCoercion(
                        mir::PointerCoercion::ClosureFnPointer(_),
                        ..,
                    ) => {
                        let op_ty = lift_err(hax_operand.ty(self.local_decls))?;
                        let op_ty_kind = op_ty.kind();
                        let Some(ty::RigidTy::Closure(def, args)) = op_ty_kind.rigid() else {
                            raise_error!(self, span, "ClosureFnPointer without closure?");
                        };
                        let closure = lift_err(mir::mono::Instance::resolve_closure(
                            def.clone(),
                            args,
                            ty::ClosureKind::FnOnce,
                        ))?;
                        let fn_id = self.register_fun_decl_id(span, &closure);
                        let fn_ptr = FnPtr {
                            func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(fn_id))),
                            generics: Box::new(GenericArgs::empty()),
                        };
                        let src_ty = TyKind::FnDef(RegionBinder::empty(fn_ptr.clone())).into_ty();

                        Ok(Rvalue::UnaryOp(
                            UnOp::Cast(CastKind::RawPtr(src_ty.clone(), tgt_ty)),
                            Operand::Const(Box::new(ConstantExpr {
                                value: RawConstantExpr::FnPtr(fn_ptr),
                                ty: src_ty,
                            })),
                        ))
                    }
                    mir::CastKind::PtrToPtr
                    | mir::CastKind::FnPtrToPtr
                    | mir::CastKind::PointerExposeAddress
                    | mir::CastKind::PointerWithExposedProvenance
                    | mir::CastKind::PointerCoercion(
                        mir::PointerCoercion::MutToConstPointer
                        | mir::PointerCoercion::ArrayToPointer,
                        ..,
                    ) => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::RawPtr(src_ty, tgt_ty)),
                        operand,
                    )),
                    mir::CastKind::PointerCoercion(
                        mir::PointerCoercion::UnsafeFnPointer
                        | mir::PointerCoercion::ReifyFnPointer,
                        ..,
                    ) => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::FnPtr(src_ty, tgt_ty)),
                        operand,
                    )),
                    mir::CastKind::Transmute => Ok(Rvalue::UnaryOp(
                        UnOp::Cast(CastKind::Transmute(src_ty, tgt_ty)),
                        operand,
                    )),
                    mir::CastKind::PointerCoercion(mir::PointerCoercion::Unsize) => {
                        let unop = UnOp::Cast(CastKind::Unsize(
                            src_ty.clone(),
                            tgt_ty.clone(),
                            UnsizingMetadata::Unknown,
                        ));
                        Ok(Rvalue::UnaryOp(unop, operand))
                    }
                }
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

                        let id = self.register_type_decl_id(span, &item, &generics);
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
                        let id = self.register_closure_type_decl_id(span, def, args);
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
                unwind: _, // We consider that panic is an error, and don't model unwinding
                ..
            } => {
                let place = self.translate_place(span, place)?;
                statements.push(Statement::new(
                    span,
                    RawStatement::Drop(
                        place,
                        TraitRef {
                            kind: TraitRefKind::Unknown("Idk how to do this".to_string()),
                            trait_decl_ref: RegionBinder::empty(TraitDeclRef {
                                id: TraitDeclId::ZERO,
                                generics: Box::new(GenericArgs::empty()),
                            }),
                        },
                    ),
                ));
                let target = self.translate_basic_block_id(*target);
                RawTerminator::Goto { target }
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
        let fn_ty = lift_err(fun.ty(self.local_decls))?;
        let mut extra_stt = None;
        let fn_operand = match fn_ty.kind() {
            ty::TyKind::RigidTy(ty::RigidTy::FnDef(fn_def, args)) => {
                // trace!("func: {:?}", item.def_id);
                // let fun_def = self.hax_def(&item.def_id)?;
                // let fun_src = TransItemSource::Fun(item.def_id.clone());
                // let name = self.t_ctx.translate_name(&fun_src)?;
                // let panic_lang_items = &["panic", "panic_fmt", "begin_panic"];
                // let panic_names = &[&["core", "panicking", "assert_failed"], EXPLICIT_PANIC_NAME];

                // if fun_def
                //     .lang_item
                //     .as_deref()
                //     .is_some_and(|lang_it| panic_lang_items.iter().contains(&lang_it))
                //     || panic_names.iter().any(|panic| name.equals_ref_name(panic))
                // {
                //     // If the call is `panic!`, then the target is `None`.
                //     // I don't know in which other cases it can be `None`.
                //     assert!(target.is_none());
                //     // We ignore the arguments
                //     return Ok(RawTerminator::Abort(AbortKind::Panic(Some(name))));
                // } else {
                let instance = lift_err(stable_mir::mir::mono::Instance::resolve(fn_def, &args))?;
                let fn_id = self.register_fun_decl_id(span, &instance);
                let fn_ptr = FnPtr {
                    func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(fn_id))),
                    generics: Box::new(GenericArgs::empty()),
                };
                FnOperand::Regular(fn_ptr)
                // }
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
        let on_unwind = match unwind {
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
        };
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

    /// Translate a function body.
    pub fn translate_body(
        &mut self,
        span: Span,
        instance: &mir::mono::Instance,
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
        instance: &mir::mono::Instance,
        body: &mir::Body,
    ) -> Result<Result<Body, Opaque>, Error> {
        // Compute the span information
        let span = self.translate_span_from_smir(&body.span);

        // Initialize the local variables
        trace!("Translating the body locals");
        self.locals.arg_count = instance.fn_abi().unwrap().args.len();
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

        // Create the body
        Ok(Ok(Body::Unstructured(ExprBody {
            span,
            locals: mem::take(&mut self.locals),
            body: mem::take(&mut self.blocks),
            comments: vec![],
        })))
    }
}
