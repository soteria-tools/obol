extern crate rustc_abi;
extern crate rustc_apfloat;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_public_bridge;

use charon_lib::{ast::*, raise_error, register_error};
use itertools::Itertools;
use rustc_apfloat::{Float, ieee};
use rustc_middle::mir::interpret::PointerArithmetic;
use rustc_public::{abi, mir, ty};
use rustc_public_bridge::IndexedVal;
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
            .ok_or_else(|| format!("Found uninitialized bytes when reading {bytes:?}").into())
    }

    pub fn as_charon_bytes(
        &mut self,
        span: Span,
        alloc: &ty::Allocation,
        offset: usize,
        size: usize,
    ) -> Vec<Byte> {
        let mut bytes: Vec<Byte> = alloc.bytes.as_slice()[offset..offset + size]
            .iter()
            .map(|b| match b {
                None => Byte::Uninit,
                Some(v) => Byte::Value(*v),
            })
            .collect();

        let ptr_size = self.t_ctx.tcx.pointer_size().bytes_usize();
        for (prov_ofs, prov) in alloc.provenance.ptrs.iter() {
            let prov_alloc: mir::alloc::GlobalAlloc = prov.0.into();
            let prov = match prov_alloc {
                mir::alloc::GlobalAlloc::Function(fun) => {
                    let id = self.register_fun_decl_id(span, fun);
                    Provenance::Function(FunDeclRef {
                        id,
                        generics: Box::new(GenericArgs::empty()),
                    })
                }
                _ => {
                    let id = self.register_global_decl_id(span, prov.0, None);
                    Provenance::Global(GlobalDeclRef {
                        id,
                        generics: Box::new(GenericArgs::empty()),
                    })
                }
            };
            let prov_ofs = *prov_ofs;
            for ptr_i in 0..ptr_size {
                let alloc_i = prov_ofs + ptr_i;
                if offset <= alloc_i && alloc_i < offset + size {
                    bytes[alloc_i] = Byte::Provenance(prov.clone(), ptr_i as u8);
                }
            }
        }

        bytes
    }

    fn provenance_at<'a>(
        &mut self,
        alloc: &'a ty::Allocation,
        offset: usize,
    ) -> Option<&'a ty::Prov> {
        alloc
            .provenance
            .ptrs
            .iter()
            .find(|(o, _)| *o == offset)
            .map(|(_, p)| p)
    }

    pub fn translate_allocation(
        &mut self,
        span: Span,
        alloc: &ty::Allocation,
        ty: &TyKind,
        rty: ty::Ty,
    ) -> Result<ConstantExpr, Error> {
        self.translate_allocation_at(span, alloc, ty, rty, 0, None)
    }

    /// Translate a value out of an allocation, starting at byte `offset`.
    ///
    /// `unsized_len` is the number of trailing bytes that make up the unsized data of an unsized
    /// value (`str`, `[T]`, or a struct whose last field is unsized, such as `CStr`). It is only
    /// relevant when `ty` is unsized, since in that case the layout only describes the sized
    /// prefix and the length of the data can't be recovered from the type. For a top-level
    /// unsized constant the caller can pass `None`, in which case we use the rest of the
    /// allocation.
    pub fn translate_allocation_at(
        &mut self,
        span: Span,
        alloc: &ty::Allocation,
        ty: &TyKind,
        rty: ty::Ty,
        offset: usize,
        unsized_len: Option<usize>,
    ) -> Result<ConstantExpr, Error> {
        let layout = rty.layout()?.shape();
        let size = layout.size.bytes();
        // For an unsized value the trailing data extends to the end of the allocation unless the
        // caller told us where it stops (e.g. when it is a field of a larger unsized value).
        let unsized_len = layout
            .is_unsized()
            .then(|| unsized_len.unwrap_or(alloc.bytes.len() - offset));
        if size == 0 && unsized_len.is_none() {
            return self.translate_zst_constant(span, ty, rty);
        }
        let bytes = &alloc.bytes.as_slice()[offset..offset + size];
        let kind = match ty {
            TyKind::Literal(lit) => match lit {
                LiteralTy::Int(it) => {
                    ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Signed(
                        it.clone(),
                        self.read_target_int(Self::as_init(bytes)?.as_slice())?,
                    )))
                }
                LiteralTy::UInt(uit) => {
                    ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Unsigned(
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
                    ConstantExprKind::Literal(Literal::Bool(res))
                }
                LiteralTy::Char => ConstantExprKind::Literal(Literal::Char(
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
                    ConstantExprKind::Literal(Literal::Float(FloatValue {
                        value,
                        ty: f.clone(),
                    }))
                }
            },
            TyKind::Ref(_, subty, _) | TyKind::RawPtr(subty, _) => 'ptr_case: {
                let Some(suballoc) = self.provenance_at(alloc, offset) else {
                    let value = self.read_target_uint(Self::as_init(bytes)?.as_slice())?;
                    break 'ptr_case ConstantExprKind::PtrNoProvenance(value);
                };
                use mir::alloc::GlobalAlloc;
                let alloc_id = suballoc.0;
                let glob_alloc: GlobalAlloc = alloc_id.into();
                match glob_alloc {
                    GlobalAlloc::Memory(suballoc) if subty.is_str() => {
                        let as_str =
                            unsafe { String::from_utf8_unchecked(suballoc.raw_bytes().unwrap()) };
                        ConstantExprKind::Literal(Literal::Str(as_str))
                    }
                    GlobalAlloc::Memory(suballoc) if subty.is_slice() => {
                        let meta_bytes = &alloc.bytes.as_slice()[offset + size / 2..offset + size];
                        let len = self.read_target_uint(Self::as_init(meta_bytes)?.as_slice())?;
                        let subty = subty.as_array_or_slice().unwrap();
                        let rtyk = rty.kind().builtin_deref(true).unwrap().ty.kind();
                        let ty::RigidTy::Slice(rsubty) = rtyk.rigid().unwrap() else {
                            unreachable!("Unexpected rigid type for slice: {rty:?}");
                        };
                        let elem_size = rsubty.layout().unwrap().shape().size.bytes();
                        let sub_constants = (0..len as usize)
                            .map(|i| {
                                let elem_off = elem_size * i;
                                self.translate_allocation_at(
                                    span,
                                    &suballoc,
                                    subty.kind(),
                                    *rsubty,
                                    elem_off,
                                    None,
                                )
                            })
                            .try_collect()?;
                        let len = ConstantExpr::mk_usize(ScalarValue::Unsigned(UIntTy::Usize, len));
                        let sub_constant = ConstantExpr {
                            kind: ConstantExprKind::Array(sub_constants),
                            ty: Ty::mk_array(subty.clone(), len.clone()),
                        };
                        let metadata = Some(UnsizingMetadata::Length(Box::new(len)));

                        if let TyKind::RawPtr(_, rk) = ty {
                            ConstantExprKind::Ptr(*rk, Box::new(sub_constant), metadata)
                        } else {
                            ConstantExprKind::Ref(Box::new(sub_constant), metadata)
                        }
                    }
                    // The pointer points directly at a function (e.g. `f as *mut ()`
                    GlobalAlloc::Function(instance) => {
                        let id = self.register_fun_decl_id(span, instance);
                        let generics = self.translate_generic_args(span, &instance.args())?;
                        ConstantExprKind::FnPtr(FnPtr {
                            generics: Box::new(generics),
                            kind: Box::new(FnPtrKind::Fun(FunId::Regular(id))),
                        })
                    }
                    _ => {
                        let (metadata, dyn_self_ty) = match subty.kind() {
                            TyKind::Slice(_) => {
                                let meta_bytes =
                                    &alloc.bytes.as_slice()[offset + size / 2..offset + size];
                                let len =
                                    self.read_target_uint(Self::as_init(meta_bytes)?.as_slice())?;
                                let meta = UnsizingMetadata::Length(Box::new(
                                    ScalarValue::Unsigned(UIntTy::Usize, len).to_constant(),
                                ));
                                (Some(meta), None)
                            }
                            TyKind::DynTrait(_) => {
                                let Some(vtable_prov) =
                                    self.provenance_at(alloc, offset + size / 2)
                                else {
                                    unreachable!("&dyn constant with no vtable provenance?");
                                };
                                let alloc: mir::alloc::GlobalAlloc = vtable_prov.0.into();
                                let mir::alloc::GlobalAlloc::VTable(self_ty, trait_ref) = alloc
                                else {
                                    unreachable!("&dyn constant with non-vtable provenance?");
                                };
                                let trait_ref = trait_ref.map(|t| {
                                    let t =
                                        rustc_public::rustc_internal::internal(self.t_ctx.tcx, t);
                                    let t = self.t_ctx.tcx.instantiate_bound_regions_with_erased(t);
                                    let t = rustc_public::rustc_internal::stable(t);
                                    t.with_self_ty(self_ty)
                                });
                                let vtable_global = self.register_vtable(span, self_ty, trait_ref);

                                let global_ref = GlobalDeclRef {
                                    id: vtable_global,
                                    generics: Box::new(GenericArgs::empty()),
                                };
                                let meta = ConstantExpr {
                                    kind: ConstantExprKind::Global(global_ref),
                                    ty: TyKind::RawPtr(Ty::mk_unit(), RefKind::Shared).into_ty(),
                                };
                                let meta = UnsizingMetadata::VTable(
                                    self.dummy_trait_ref(),
                                    Box::new(meta),
                                );
                                (Some(meta), Some(self_ty))
                            }
                            _ => (None, None),
                        };

                        let glob_ty = match (&glob_alloc, dyn_self_ty) {
                            // we try checking if there's a static we can use the type of,
                            // to avoid registering unsized globals (a static is always sized)
                            (GlobalAlloc::Static(stt), _) => stt.ty(),
                            // for a `&dyn Trait` the pointee type is unsized; use the concrete
                            // type recovered from the vtable so we register a sized global.
                            (_, Some(dyn_self_ty)) => dyn_self_ty,
                            // if we don't know the exact type, we create a dummy type
                            // that should match
                            (GlobalAlloc::Memory(mem), _)
                                if let Some(inner) =
                                    rty.kind().builtin_deref(true).map(|d| d.ty)
                                    && let Ok(layout) = inner.layout()
                                    && !layout.shape().is_unsized()
                                    && mem.bytes.len() > layout.shape().size.bytes() as usize =>
                            {
                                self.raw_alloc_ty(mem.bytes.len(), mem.align as usize)?
                            }
                            _ => rty.kind().builtin_deref(true).unwrap().ty,
                        };

                        let id = self.register_global_decl_id(span, alloc_id, Some(glob_ty));
                        let glob_ty = self.translate_ty(span, glob_ty)?;
                        let generics = match glob_alloc {
                            GlobalAlloc::Static(stt) => {
                                let instance: mir::mono::Instance = stt.into();
                                self.translate_generic_args(span, &instance.args())?
                            }
                            _ => GenericArgs::empty(),
                        };
                        let sub_constant = ConstantExpr {
                            kind: ConstantExprKind::Global(GlobalDeclRef {
                                id,
                                generics: Box::new(generics),
                            }),
                            ty: glob_ty,
                        };

                        if let TyKind::RawPtr(_, rk) = ty {
                            ConstantExprKind::Ptr(*rk, Box::new(sub_constant), metadata)
                        } else {
                            ConstantExprKind::Ref(Box::new(sub_constant), metadata)
                        }
                    }
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
                let fields = (0..generics.types.len())
                    .map(|i| {
                        let field_offset = offsets[i].bytes() as usize;
                        let field_rty = rtys[i];
                        let field_ty = generics.types.get(TypeVarId::from_usize(i)).unwrap();
                        // Only the last field of an unsized tuple is itself unsized.
                        let field_len = unsized_len
                            .filter(|_| i + 1 == generics.types.len())
                            .map(|l| l - field_offset);
                        self.translate_allocation_at(
                            span,
                            alloc,
                            field_ty.kind(),
                            field_rty,
                            field_offset + offset,
                            field_len,
                        )
                    })
                    .try_collect()?;
                ConstantExprKind::Adt(None, fields)
            }
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Adt(..),
                ..
            }) => {
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
                        let mask = if length_bytes * 8 == 128 {
                            u128::MAX
                        } else {
                            (1u128 << (length_bytes * 8)) - 1
                        };
                        let variant_idx = match tag_encoding {
                            abi::TagEncoding::Direct => (0..adt.num_variants())
                                .find_map(|idx| {
                                    let idx = ty::VariantIdx::to_val(idx);
                                    let discr = adt.discriminant_for_variant(idx);
                                    ((discr.val & mask) == tag_value).then_some(idx)
                                })
                                .unwrap(),
                            abi::TagEncoding::Niche {
                                untagged_variant,
                                niche_variants,
                                niche_start,
                            } => (0..adt.num_variants())
                                .find_map(|idx| {
                                    let idx = ty::VariantIdx::to_val(idx);
                                    let discr = adt.discriminant_for_variant(idx);
                                    let niche_variants_start =
                                        niche_variants.start().to_index() as u128;

                                    if matches!(tag_ty, abi::Primitive::Int { .. }) {
                                        if discr.val < niche_variants_start {
                                            // The variant is before the niche variants, so it is not tagged.
                                            // Could e.g. be the case if it is uninhabited.
                                            return None;
                                        }
                                        let tag = (discr.val - niche_variants_start)
                                            .wrapping_add(*niche_start);
                                        (tag_value == tag).then_some(idx)
                                    } else {
                                        // pointer niche: if no provenance, then niche variant,
                                        // otherwise untagged variant
                                        assert!(
                                            niche_variants.start() == niche_variants.end(),
                                            ">1 niche in ptr niche?"
                                        );
                                        self.provenance_at(alloc, offset)
                                            .is_none()
                                            .then_some(*niche_variants.start())
                                    }
                                })
                                .unwrap_or(*untagged_variant),
                        };
                        let variant = adt.variant(variant_idx).unwrap();
                        let fields = variant
                            .fields()
                            .iter()
                            .map(|f| f.ty_with_args(generics))
                            .collect::<Vec<ty::Ty>>();
                        let variant_idx_charon = self.translate_variant_id(variant_idx);
                        let variant_layout = variants.get(variant_idx.to_index()).unwrap();
                        (
                            Some(variant_idx_charon),
                            fields,
                            variant_layout.offsets.clone(),
                        )
                    }
                    ty::AdtKind::Union => {
                        return Ok(ConstantExpr {
                            kind: ConstantExprKind::RawMemory(
                                self.as_charon_bytes(span, alloc, offset, size),
                            ),
                            ty: ty.clone().into_ty(),
                        });
                    }
                };

                let consts = (0..offsets.len())
                    .map(|field| {
                        let field_offset = offsets[field].bytes() as usize;
                        let field_rty = rfields[field];
                        let field_ty = self.translate_ty(span, field_rty)?;
                        // Only an unsized struct's last field is itself unsized; enums are
                        // always sized so `unsized_len` is `None` for them.
                        let field_len = unsized_len
                            .filter(|_| field + 1 == offsets.len())
                            .map(|l| l - field_offset);
                        self.translate_allocation_at(
                            span,
                            alloc,
                            field_ty.kind(),
                            field_rty,
                            field_offset + offset,
                            field_len,
                        )
                    })
                    .try_collect()?;
                ConstantExprKind::Adt(variant.clone(), consts)
            }
            TyKind::Array(subty, _) => {
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
                        self.translate_allocation_at(span, alloc, subty, *subrty, elem_off, None)
                    })
                    .try_collect()?;
                ConstantExprKind::Array(elems)
            }
            TyKind::FnPtr(_) => 'fnptr_case: {
                let Some(prov) = self.provenance_at(alloc, offset) else {
                    let value = self.read_target_uint(Self::as_init(bytes)?.as_slice())?;
                    break 'fnptr_case ConstantExprKind::PtrNoProvenance(value);
                };
                use mir::alloc::GlobalAlloc;
                let glob_alloc: GlobalAlloc = prov.0.into();
                match glob_alloc {
                    GlobalAlloc::Function(instance) => {
                        let TyKind::FnPtr(sig) = ty else {
                            unreachable!("Unexpected type for fn ptr: {ty:?}");
                        };

                        // special-case: if the first argument is ignored, because the signature
                        // is shorter, we do a closure_as_fn conversion
                        let abi = instance.fn_abi()?;
                        let id = if abi.args.len() == sig.skip_binder.inputs.len() + 1
                            && let Some(closure_arg) = abi.args.get(0)
                            && closure_arg.mode == rustc_public::abi::PassMode::Ignore
                            && let ty::TyKind::RigidTy(ty::RigidTy::Closure(closure, args)) =
                                closure_arg.ty.kind()
                        {
                            self.register_closure_as_fn_id(span, closure, args)
                        } else {
                            self.register_fun_decl_id(span, instance)
                        };

                        let generics = self.translate_generic_args(span, &instance.args())?;
                        let fn_ptr = FnPtr {
                            generics: Box::new(generics),
                            kind: Box::new(FnPtrKind::Fun(FunId::Regular(id))),
                        };
                        ConstantExprKind::FnPtr(fn_ptr)
                    }
                    _ => {
                        println!("Gave up for raw memory of fndef with alloc {glob_alloc:?}");
                        ConstantExprKind::RawMemory(self.as_charon_bytes(span, alloc, offset, size))
                    }
                }
            }
            TyKind::Pattern(inner, _) => {
                let rtyk = rty.kind();
                let Some(ty::RigidTy::Pat(rty, _)) = rtyk.rigid() else {
                    unreachable!("Pattern type should be a rigid pattern type");
                };
                self.translate_allocation_at(span, alloc, inner, *rty, offset, unsized_len)?
                    .kind
            }

            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Box),
                ..
            }) => {
                unreachable!("We never create builtin boxes");
            }
            // An unsized `str` held directly in a constant: its data is the raw UTF-8 bytes.
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Str),
                ..
            }) => {
                let len = unsized_len.expect("str constant without a length");
                let data = &alloc.bytes.as_slice()[offset..offset + len];
                let as_str = unsafe { String::from_utf8_unchecked(Self::as_init(data)?) };
                ConstantExprKind::Literal(Literal::Str(as_str))
            }
            // An unsized `[T]` held directly in a constant.
            TyKind::Slice(subty) => {
                let len = unsized_len.expect("slice constant without a length");
                let rtyk = rty.kind();
                let ty::RigidTy::Slice(subrty) = rtyk.rigid().unwrap() else {
                    unreachable!("Unexpected rigid type for slice: {rty:?}");
                };
                let elem_size = subrty.layout()?.shape().size.bytes() as usize;
                let count = if elem_size == 0 { 0 } else { len / elem_size };
                let elems = (0..count)
                    .map(|i| {
                        let elem_off = offset + elem_size * i;
                        self.translate_allocation_at(span, alloc, subty, *subrty, elem_off, None)
                    })
                    .try_collect()?;
                ConstantExprKind::Array(elems)
            }
            // A bare `dyn Trait` value can't be held by-value in a constant.
            TyKind::DynTrait(..) => {
                unreachable!("Translating unsized dyn constant?");
            }
            TyKind::Error(..)
            | TyKind::Never
            | TyKind::TypeVar(..)
            | TyKind::TraitType(..)
            | TyKind::FnDef(..)
            | TyKind::PtrMetadata(..) => {
                println!("Gave up for raw memory of type {ty:?} with alloc {alloc:?}");
                ConstantExprKind::RawMemory(self.as_charon_bytes(span, alloc, offset, size))
            }
        };
        Ok(ConstantExpr {
            kind,
            ty: ty.clone().into_ty(),
        })
    }

    pub fn translate_zst_constant(
        &mut self,
        span: Span,
        ty: &TyKind,
        rty: ty::Ty,
    ) -> Result<ConstantExpr, Error> {
        let kind = match ty {
            TyKind::FnDef(fnptr) => ConstantExprKind::FnDef(fnptr.skip_binder.clone()),
            TyKind::Array(subty, _) => {
                let rtyk = rty.kind();
                let ty::RigidTy::Array(rty, len) = rtyk.rigid().unwrap() else {
                    unreachable!();
                };
                let len = len.eval_target_usize()?;
                if len > 32 {
                    // FIXME: temporary safeguard for large arrays; ideally we should have some
                    // sort of ConstantExprKind::ArrayRepeat...
                    ConstantExprKind::RawMemory(vec![])
                } else if len == 0 {
                    ConstantExprKind::Array(vec![])
                } else {
                    let cexpr = self.translate_zst_constant(span, subty, *rty)?;
                    ConstantExprKind::Array(vec![cexpr; len as usize])
                }
            }
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Adt(..) | TypeId::Tuple,
                ..
            }) => {
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
                                        kind: ConstantExprKind::RawMemory(vec![]),
                                        ty: ty.clone().into_ty(),
                                    });
                                };
                                Some(index)
                            }
                            ty::AdtKind::Union => {
                                return Ok(ConstantExpr {
                                    kind: ConstantExprKind::RawMemory(vec![]),
                                    ty: ty.clone().into_ty(),
                                });
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
                        self.translate_zst_constant(span, field_ty.kind(), field_rty)
                    })
                    .try_collect()?;
                ConstantExprKind::Adt(variant, fields)
            }
            _ => {
                raise_error!(self, span, "Unsupported ZST constant type: {:?}", ty)
            }
        };
        Ok(ConstantExpr {
            kind,
            ty: ty.clone().into_ty(),
        })
    }

    pub fn translate_tyconst_to_const_expr(
        &mut self,
        span: Span,
        v: &ty::TyConst,
    ) -> Result<ConstantExpr, Error> {
        match v.kind() {
            ty::TyConstKind::Value(rty, alloc) => {
                let ty = self.translate_ty(span, *rty)?;
                self.translate_allocation(span, alloc, ty.kind(), *rty)
            }
            ty::TyConstKind::ZSTValue(rty) => {
                let ty = self.translate_ty(span, *rty)?;
                self.translate_zst_constant(span, ty.kind(), *rty)
            }
            ty::TyConstKind::Unevaluated(..) => {
                // An unevaluated const (e.g. an array length or const-generic argument that
                // refers to another `const` item). We evaluate it by normalizing the internal
                // `ty::Const` (which triggers const evaluation), then translate the resulting
                // value.
                let internal = rustc_public::rustc_internal::internal(self.t_ctx.tcx, v);
                let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
                // We use the `try_` variant since `normalize_erasing_regions` ICEs if
                // normalization fails (e.g. when the const is too generic to evaluate). obol
                // only ever sees monomorphic code, so this should always succeed in practice,
                // but we degrade to a translation error rather than crashing if it doesn't.
                let Ok(normalized) = self.t_ctx.tcx.try_normalize_erasing_regions(
                    typing_env,
                    rustc_middle::ty::Unnormalized::new_wip(internal),
                ) else {
                    raise_error!(self, span, "Could not evaluate constant: {:?}", v.kind())
                };
                let evaluated = rustc_public::rustc_internal::stable(normalized);
                if matches!(evaluated.kind(), ty::TyConstKind::Unevaluated(..)) {
                    // Normalization made no progress; bail out to avoid looping.
                    raise_error!(self, span, "Could not evaluate constant: {:?}", v.kind())
                }
                self.translate_tyconst_to_const_expr(span, &evaluated)
            }
            ty::TyConstKind::Param(..) => {
                raise_error!(self, span, "Unsupported constant kind: {:?}", v.kind())
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

    pub fn translate_alloc_to_const(
        &mut self,
        span: Span,
        alloc: &ty::Allocation,
        ty: Option<ty::Ty>,
    ) -> Result<(ConstantExpr, Ty), Error> {
        match ty {
            Some(ty) => {
                let output = self.translate_ty(span, ty)?;
                let const_val = self.translate_allocation(span, &alloc, &output, ty)?;
                Ok((const_val, output))
            }
            None => {
                let size = alloc.bytes.len();
                let maybe_uninit = self.maybe_uninit_bytes(span, size)?;
                let bytes = self.as_charon_bytes(span, &alloc, 0, size);
                let const_val = ConstantExpr {
                    kind: ConstantExprKind::RawMemory(bytes),
                    ty: maybe_uninit.clone(),
                };
                Ok((const_val, maybe_uninit))
            }
        }
    }

    pub(crate) fn translate_const_value(
        &mut self,
        span: Span,
        const_: &ty::MirConst,
    ) -> Result<ConstantExpr, Error> {
        let ty = self.translate_ty(span, const_.ty())?;
        match const_.kind() {
            ty::ConstantKind::Allocated(alloc) => {
                self.translate_allocation(span, alloc, ty.kind(), const_.ty())
            }
            ty::ConstantKind::ZeroSized => {
                self.translate_zst_constant(span, ty.kind(), const_.ty())
            }
            other => {
                raise_error!(self, span, "Unexpected evaluated const kind: {:?}", other)
            }
        }
    }
}
