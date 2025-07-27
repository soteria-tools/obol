extern crate rustc_abi;
extern crate rustc_apfloat;
extern crate rustc_smir;
extern crate stable_mir;

use charon_lib::{ast::*, error_assert, raise_error, register_error};
use log::trace;
use rustc_apfloat::{Float, ieee};
use rustc_smir::IndexedVal;
use stable_mir::{abi, mir, ty};
use std::io::Read;

use crate::translate::translate_ctx::ItemTransCtx;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// Utility function used to read an allocation data into a unassigned integer.
    fn read_target_uint(&mut self, mut bytes: &[u8]) -> Result<u128, Error> {
        let mut buf = [0u8; size_of::<u128>()];
        match self.t_ctx.tcx.data_layout.endian {
            rustc_abi::Endian::Little => {
                bytes.read_exact(&mut buf[..bytes.len()])?;
                Ok(u128::from_le_bytes(buf))
            }
            rustc_abi::Endian::Big => {
                bytes.read_exact(&mut buf[16 - bytes.len()..])?;
                Ok(u128::from_be_bytes(buf))
            }
        }
    }

    /// Utility function used to read an allocation data into an assigned integer.
    fn read_target_int(&mut self, mut bytes: &[u8]) -> Result<i128, Error> {
        // we do sign extension manually because why not i guess.
        match self.t_ctx.tcx.data_layout.endian {
            rustc_abi::Endian::Little => {
                let sign = bytes.last().copied().unwrap_or(0) & 0x80 != 0;
                let default = if sign { 0xff } else { 0x00 };
                let mut buf = [default; size_of::<i128>()];
                bytes.read_exact(&mut buf[..bytes.len()])?;
                Ok(i128::from_le_bytes(buf))
            }
            rustc_abi::Endian::Big => {
                let sign = bytes.first().copied().unwrap_or(0) & 0x80 != 0;
                let default = if sign { 0xff } else { 0x00 };
                let mut buf = [default; size_of::<i128>()];
                bytes.read_exact(&mut buf[16 - bytes.len()..])?;
                Ok(i128::from_be_bytes(buf))
            }
        }
    }

    pub fn as_init(bytes: &[Option<u8>]) -> Result<Vec<u8>, Error> {
        bytes
            .iter()
            .copied()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| "Found uninitialized bytes".into())
    }

    pub fn translate_allocation(
        &mut self,
        span: Span,
        alloc: &ty::Allocation,
        ty: &TyKind,
        rty: &ty::Ty,
    ) -> Result<ConstantExpr, Error> {
        self.translate_allocation_at(span, alloc, ty, rty, 0)
    }

    pub fn translate_allocation_at(
        &mut self,
        span: Span,
        alloc: &ty::Allocation,
        ty: &TyKind,
        rty: &ty::Ty,
        offset: usize,
    ) -> Result<ConstantExpr, Error> {
        let size = rty.layout()?.shape().size.bytes();
        if size == 0 {
            return self.translate_zst_constant(span, ty, rty);
        }
        let bytes = &alloc.bytes.as_slice()[offset..offset + size];
        let value = match ty {
            TyKind::Literal(lit) => match lit {
                LiteralTy::Int(it) => {
                    RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Signed(
                        it.clone(),
                        self.read_target_int(Self::as_init(bytes)?.as_slice())?,
                    )))
                }
                LiteralTy::UInt(uit) => {
                    RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Unsigned(
                        uit.clone(),
                        self.read_target_uint(Self::as_init(bytes)?.as_slice())?,
                    )))
                }
                LiteralTy::Bool => {
                    let bool = self.read_target_int(Self::as_init(bytes)?.as_slice())?;
                    let res = match bool {
                        0 => false,
                        1 => true,
                        _ => {
                            raise_error!(self, span, "Invalid boolean value in constant: {bool}")
                        }
                    };
                    RawConstantExpr::Literal(Literal::Bool(res))
                }
                LiteralTy::Char => RawConstantExpr::Literal(Literal::Char(
                    char::from_u32(self.read_target_uint(Self::as_init(bytes)?.as_slice())? as u32)
                        .unwrap(),
                )),
                LiteralTy::Float(f) => {
                    let bits = self.read_target_uint(Self::as_init(bytes)?.as_slice())?;
                    let value = match f {
                        FloatTy::F16 => ieee::Half::from_bits(bits).to_string(),
                        FloatTy::F32 => ieee::Single::from_bits(bits).to_string(),
                        FloatTy::F64 => ieee::Double::from_bits(bits).to_string(),
                        FloatTy::F128 => ieee::Quad::from_bits(bits).to_string(),
                    };
                    RawConstantExpr::Literal(Literal::Float(FloatValue {
                        value,
                        ty: f.clone(),
                    }))
                }
            },
            TyKind::Ref(_, subty, _) | TyKind::RawPtr(subty, _) => 'ptr_case: {
                let Some((_, alloc)) = alloc.provenance.ptrs.iter().find(|(o, _)| *o == offset)
                else {
                    let value = self.read_target_int(Self::as_init(bytes)?.as_slice())?;
                    break 'ptr_case RawConstantExpr::Literal(Literal::Scalar(
                        ScalarValue::Signed(IntTy::Isize, value),
                    ));
                };
                use mir::alloc::GlobalAlloc;
                let glob_alloc: GlobalAlloc = alloc.0.into();
                match glob_alloc {
                    GlobalAlloc::Memory(suballoc)
                        if subty
                            .kind()
                            .as_adt()
                            .is_some_and(|a| a.id == TypeId::Builtin(BuiltinTy::Str)) =>
                    {
                        let as_str =
                            unsafe { String::from_utf8_unchecked(suballoc.raw_bytes().unwrap()) };
                        RawConstantExpr::Literal(Literal::Str(as_str))
                    }
                    GlobalAlloc::Memory(suballoc) => {
                        let rtyk = rty.kind();
                        let rsubty = match rtyk.rigid().unwrap() {
                            ty::RigidTy::RawPtr(rsubty, _) => rsubty,
                            ty::RigidTy::Ref(_, rsubty, _) => rsubty,
                            _ => unreachable!(
                                "Unexpected rigid type for raw pointer/reference: {rty:?}"
                            ),
                        };
                        let sub_constant =
                            self.translate_allocation(span, &suballoc, subty, rsubty)?;
                        if let TyKind::RawPtr(_, rk) = ty {
                            RawConstantExpr::Ptr(*rk, Box::new(sub_constant))
                        } else {
                            RawConstantExpr::Ref(Box::new(sub_constant))
                        }
                    }
                    GlobalAlloc::Static(stt) => {
                        let id = self.register_global_decl_id(span, stt);
                        let instance: mir::mono::Instance = stt.into();
                        let generics = self.translate_generic_args(span, &instance.args())?;
                        let sub_constant = RawConstantExpr::Global(GlobalDeclRef {
                            id,
                            generics: Box::new(generics),
                        });
                        let sub_constant = ConstantExpr {
                            value: sub_constant,
                            ty: subty.clone(),
                        };

                        if let TyKind::RawPtr(_, rk) = ty {
                            RawConstantExpr::Ptr(*rk, Box::new(sub_constant))
                        } else {
                            RawConstantExpr::Ref(Box::new(sub_constant))
                        }
                    }
                    _ => unreachable!("Unhandled global: {glob_alloc:?} for type {ty:?}"),
                }
            }
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Tuple,
                generics,
            }) => {
                let rtyk = rty.kind();
                let ty::RigidTy::Tuple(rtys) = rtyk.rigid().unwrap() else {
                    unreachable!("Unexpected rigid type for tuple: {rty:?}");
                };
                let layout = rty.layout()?.shape();
                let abi::FieldsShape::Arbitrary { offsets } = &layout.fields else {
                    unreachable!("Unexpected layout for tuple: {layout:?}");
                };
                let fields = (0..generics.types.elem_count())
                    .map(|i| {
                        let field_offset = offsets[i].bytes();
                        let field_rty = rtys[i];
                        let field_ty = generics.types.get(TypeVarId::from_usize(i)).unwrap();
                        self.translate_allocation_at(
                            span,
                            alloc,
                            field_ty.kind(),
                            &field_rty,
                            field_offset + offset,
                        )
                    })
                    .try_collect()?;
                RawConstantExpr::Adt(None, fields)
            }
            TyKind::Adt(_) if rty.kind().is_adt() => {
                let rtyk = rty.kind();
                let ty::RigidTy::Adt(adt, generics) = rtyk.rigid().unwrap() else {
                    unreachable!("Unexpected rigid type for adt: {rty:?}");
                };
                let layout = rty.layout()?.shape();
                let (variant, rfields, offsets) = match adt.kind() {
                    ty::AdtKind::Struct => {
                        let variant = adt.variants()[0];
                        let rfields = variant
                            .fields()
                            .iter()
                            .map(|f| f.ty_with_args(generics))
                            .collect::<Vec<ty::Ty>>();
                        let abi::FieldsShape::Arbitrary { offsets } = &layout.fields else {
                            unreachable!("Unexpected layout for struct: {layout:?}");
                        };
                        (None, rfields, offsets.clone())
                    }
                    ty::AdtKind::Enum => 'enum_case: {
                        if let abi::VariantsShape::Single { index } = layout.variants {
                            let variant = VariantId::new(index.to_index());
                            let variant_data = adt.variant(index).unwrap();
                            let rfields = variant_data
                                .fields()
                                .iter()
                                .map(|f| f.ty_with_args(generics))
                                .collect::<Vec<ty::Ty>>();
                            let abi::FieldsShape::Arbitrary { offsets } = &layout.fields else {
                                unreachable!("Unexpected layout for struct: {layout:?}");
                            };
                            break 'enum_case (Some(variant), rfields, offsets.clone());
                        };
                        let abi::VariantsShape::Multiple {
                            tag,
                            tag_encoding,
                            tag_field,
                            variants,
                        } = &layout.variants
                        else {
                            unreachable!("Unexpected layout for enum: {layout:?}");
                        };
                        assert!(layout.fields.count() == 1, "Enum with non-1 shared field?");
                        let abi::FieldsShape::Arbitrary { offsets } = &layout.fields else {
                            unreachable!("Unexpected layout for enum: {layout:?}");
                        };
                        let abi::Scalar::Initialized { value: tag_ty, .. } = &tag else {
                            unreachable!("Unexpected tag encoding for enum: {tag:?}");
                        };
                        let (length_bytes, _) = match tag_ty {
                            abi::Primitive::Int { length, signed } => (length.bits() / 8, *signed),
                            abi::Primitive::Pointer(_) => (
                                self.t_ctx.tcx.data_layout.pointer_size().bytes() as usize,
                                false,
                            ),
                            abi::Primitive::Float { .. } => unreachable!("Float tag?"),
                        };
                        let tag_offset = offsets[*tag_field].bytes();
                        let tag_bytes = &bytes[tag_offset..tag_offset + length_bytes];
                        let tag_value =
                            self.read_target_uint(Self::as_init(tag_bytes)?.as_slice())?;

                        let variant_idx = match tag_encoding {
                            abi::TagEncoding::Direct => adt
                                .variants_iter()
                                .find_map(|v| {
                                    let discr = adt.discriminant_for_variant(v.idx);
                                    if discr.val != tag_value {
                                        return None;
                                    };
                                    Some(v.idx)
                                })
                                .unwrap(),
                            abi::TagEncoding::Niche {
                                untagged_variant,
                                niche_variants,
                                niche_start,
                            } => adt
                                .variants_iter()
                                .find_map(|v| {
                                    let discr = adt.discriminant_for_variant(v.idx);
                                    let niche_variants_start =
                                        niche_variants.start().to_index() as u128;

                                    if matches!(tag_ty, abi::Primitive::Int { .. }) {
                                        let tag = (discr.val - niche_variants_start)
                                            .wrapping_add(*niche_start);
                                        (tag_value == tag).then_some(v.idx)
                                    } else {
                                        // pointer niche: if 0, then niche variant, otherwise untagged variant
                                        assert!(
                                            niche_variants.start() == niche_variants.end(),
                                            ">1 niche in ptr niche?"
                                        );
                                        (tag_value == 0).then_some(*niche_variants.start())
                                    }
                                })
                                .unwrap_or_else(|| *untagged_variant),
                        };
                        let variant = adt.variant(variant_idx).unwrap();
                        let fields = variant
                            .fields()
                            .iter()
                            .map(|f| f.ty_with_args(generics))
                            .collect::<Vec<ty::Ty>>();
                        let variant_idx_charon = self.translate_variant_id(variant_idx);
                        let variant_layout = variants.get(variant_idx.to_index()).unwrap();
                        let abi::FieldsShape::Arbitrary { offsets } = &variant_layout.fields else {
                            unreachable!("Unexpected layout for enum: {layout:?}");
                        };
                        (Some(variant_idx_charon), fields, offsets.clone())
                    }
                    ty::AdtKind::Union => {
                        trace!("Gave up for union raw memory of type {ty:?} with alloc {alloc:?}");
                        return Ok(ConstantExpr {
                            value: RawConstantExpr::RawMemory(Self::as_init(bytes)?),
                            ty: ty.clone().into_ty(),
                        });
                    }
                };

                let consts = (0..offsets.len())
                    .map(|field| {
                        let field_offset = offsets[field].bytes();
                        let field_rty = rfields[field];
                        let field_ty = self.translate_ty(span, field_rty)?;
                        self.translate_allocation_at(
                            span,
                            alloc,
                            field_ty.kind(),
                            &field_rty,
                            field_offset + offset,
                        )
                    })
                    .try_collect()?;
                RawConstantExpr::Adt(variant.clone(), consts)
            }
            TyKind::Adt(TypeDeclRef { generics, .. }) if rty.kind().is_array() => {
                let subty = generics.types.get(TypeVarId::ZERO).unwrap();
                let rtyk = rty.kind();
                let ty::RigidTy::Array(subrty, _) = rtyk.rigid().unwrap() else {
                    unreachable!();
                };
                let layout = rty.layout()?.shape();
                let abi::FieldsShape::Array { stride, count } = layout.fields else {
                    unreachable!("Unexpected layout for array: {layout:?}");
                };
                let stride = stride.bytes();
                let elems = (0..count as usize)
                    .map(|i| {
                        let elem_off = stride * i + offset;
                        self.translate_allocation_at(span, alloc, subty, subrty, elem_off)
                    })
                    .try_collect()?;
                RawConstantExpr::Array(elems)
            }
            TyKind::FnPtr(_) => 'fnptr_case: {
                let Some((_, alloc)) = alloc.provenance.ptrs.iter().find(|(o, _)| *o == offset)
                else {
                    let value = self.read_target_int(Self::as_init(bytes)?.as_slice())?;
                    break 'fnptr_case RawConstantExpr::Literal(Literal::Scalar(
                        ScalarValue::Signed(IntTy::Isize, value),
                    ));
                };
                use mir::alloc::GlobalAlloc;
                let glob_alloc: GlobalAlloc = alloc.0.into();
                match glob_alloc {
                    GlobalAlloc::Function(instance) => {
                        // This may be wrong... I think we need a new ConstantExpr::FnPtr;
                        // a FnPtr is not a pointer to a FnDef :p
                        let id = self.register_fun_decl_id(span, instance);
                        let generics = self.translate_generic_args(span, &instance.args())?;
                        let fn_ptr = FnPtr {
                            generics: Box::new(generics),
                            func: Box::new(FunIdOrTraitMethodRef::Fun(FunId::Regular(id))),
                        };
                        let sub_const = ConstantExpr {
                            value: RawConstantExpr::FnPtr(fn_ptr.clone()),
                            ty: TyKind::FnDef(RegionBinder::empty(fn_ptr)).into_ty(),
                        };
                        RawConstantExpr::Ptr(RefKind::Shared, Box::new(sub_const))
                    }
                    _ => {
                        println!("Gave up for raw memory of fndef with alloc {glob_alloc:?}");
                        RawConstantExpr::RawMemory(Self::as_init(bytes)?)
                    }
                }
            }
            _ => {
                println!("Gave up for raw memory of type {ty:?} with alloc {alloc:?}");
                RawConstantExpr::RawMemory(Self::as_init(bytes)?)
            }
        };
        Ok(ConstantExpr {
            value,
            ty: ty.clone().into_ty(),
        })
    }

    pub fn translate_zst_constant(
        &mut self,
        span: Span,
        ty: &TyKind,
        rty: &ty::Ty,
    ) -> Result<ConstantExpr, Error> {
        let value = match ty {
            TyKind::FnDef(fnptr) => RawConstantExpr::FnPtr(fnptr.skip_binder.clone()),
            TyKind::Adt(_) if rty.kind().is_array() => {
                let rtyk = rty.kind();
                let ty::RigidTy::Array(rty, len) = rtyk.rigid().unwrap() else {
                    unreachable!();
                };
                let len = len.eval_target_usize()?;
                if len > 32 {
                    // FIXME: temporary safeguard for large arrays; ideally we should have some
                    // sort of RawConstantExpr::ArrayRepeat...
                    RawConstantExpr::RawMemory(vec![])
                } else if len == 0 {
                    RawConstantExpr::Array(vec![])
                } else {
                    let cexpr = self.translate_zst_constant(span, ty, rty)?;
                    RawConstantExpr::Array(vec![cexpr; len as usize])
                }
            }
            TyKind::Adt(_) => {
                let rtyk = rty.kind();
                let (variant, rtys) = match rtyk.rigid().unwrap() {
                    ty::RigidTy::Tuple(rtys) => (None, rtys.clone()),
                    ty::RigidTy::Closure(_, generics) => {
                        let tupled_upvars = generics.0.last().unwrap().expect_ty().kind();
                        let Some(ty::RigidTy::Tuple(state_tys)) = tupled_upvars.rigid() else {
                            raise_error!(self, span, "Closure state argument is not a tuple?");
                        };
                        (None, state_tys.clone())
                    }
                    ty::RigidTy::Adt(adt, generics) => {
                        let layout = rty.layout()?.shape();
                        let variant_r = match adt.kind() {
                            ty::AdtKind::Struct => None,
                            ty::AdtKind::Enum => {
                                let abi::VariantsShape::Single { index } = layout.variants else {
                                    println!(
                                        "Unexpected layout for ZST enum\n- Layout: {layout:?}\n- Ty: {rty:?}"
                                    );
                                    return Ok(ConstantExpr {
                                        value: RawConstantExpr::RawMemory(vec![]),
                                        ty: ty.clone().into_ty(),
                                    });
                                };
                                Some(index)
                            }
                            ty::AdtKind::Union => {
                                raise_error!(self, span, "Unhandled: ZST union type {rty:?}");
                            }
                        };
                        let variant = variant_r.map(|v| self.translate_variant_id(v));
                        let variant_r = variant_r.unwrap_or(ty::VariantIdx::to_val(0));
                        let fields = adt
                            .variant(variant_r)
                            .unwrap()
                            .fields()
                            .iter()
                            .map(|f| f.ty_with_args(generics))
                            .collect();
                        (variant, fields)
                    }
                    _ => unreachable!("Unexpected rigid type for adt: {rty:?} with kind {rtyk:?}"),
                };
                let fields = rtys
                    .into_iter()
                    .map(|field_rty| {
                        let field_ty = self.translate_ty(span, field_rty)?;
                        self.translate_zst_constant(span, field_ty.kind(), &field_rty)
                    })
                    .try_collect()?;
                RawConstantExpr::Adt(variant, fields)
            }
            _ => {
                println!("Gave up on const for ZST type: {:?}", ty);
                RawConstantExpr::RawMemory(vec![])
            }
        };
        Ok(ConstantExpr {
            value,
            ty: ty.clone().into_ty(),
        })
    }

    pub(crate) fn translate_constant_expr_to_const_generic(
        &mut self,
        span: Span,
        value: ConstantExpr,
    ) -> Result<ConstGeneric, Error> {
        match value.value {
            RawConstantExpr::Var(v) => Ok(ConstGeneric::Var(v)),
            RawConstantExpr::Literal(v) => Ok(ConstGeneric::Value(v)),
            RawConstantExpr::Global(global_ref) => {
                // TODO: handle constant arguments with generics (this can likely only happen with
                // a feature gate).
                error_assert!(self, span, global_ref.generics.is_empty());
                Ok(ConstGeneric::Global(global_ref.id))
            }
            RawConstantExpr::Adt(..)
            | RawConstantExpr::Array { .. }
            | RawConstantExpr::RawMemory { .. }
            | RawConstantExpr::TraitConst { .. }
            | RawConstantExpr::Ref(_)
            | RawConstantExpr::Ptr(..)
            | RawConstantExpr::FnPtr { .. }
            | RawConstantExpr::Opaque(_) => {
                raise_error!(self, span, "Unexpected constant generic: {:?}", value)
            }
        }
    }

    pub fn translate_tyconst_to_const_generic(
        &mut self,
        span: Span,
        v: &ty::TyConst,
    ) -> Result<ConstGeneric, Error> {
        match v.kind() {
            ty::TyConstKind::Value(rty, alloc) => {
                let ty = self.translate_ty(span, *rty)?;
                let alloc = self.translate_allocation(span, alloc, ty.kind(), rty)?;
                self.translate_constant_expr_to_const_generic(span, alloc)
            }
            _ => {
                raise_error!(
                    self,
                    span,
                    "Unexpected constant expression kind: {:?}",
                    v.kind()
                )
            }
        }
    }
}
