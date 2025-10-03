extern crate rustc_abi;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_public_bridge;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::ids::Vector;
use charon_lib::{raise_error, register_error};
use core::convert::*;
use log::trace;
use rustc_public::{abi, mir, ty};
use rustc_public_bridge::IndexedVal;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    // Translate a region
    pub(crate) fn translate_region(
        &mut self,
        span: Span,
        region: &ty::Region,
    ) -> Result<Region, Error> {
        use ty::RegionKind::*;
        match &region.kind {
            ReErased => Ok(Region::Erased),
            ReStatic => Ok(Region::Static),
            ReBound(..) | ReEarlyParam(..) => Ok(Region::Erased),
            RePlaceholder(..) => {
                // Shouldn't exist outside of type inference.
                raise_error!(
                    self,
                    span,
                    "Should not exist outside of type inference: {region:?}"
                )
            }
        }
    }

    pub(crate) fn translate_int_ty(&mut self, it: &ty::IntTy) -> IntTy {
        match it {
            ty::IntTy::I8 => IntTy::I8,
            ty::IntTy::I16 => IntTy::I16,
            ty::IntTy::I32 => IntTy::I32,
            ty::IntTy::I64 => IntTy::I64,
            ty::IntTy::I128 => IntTy::I128,
            ty::IntTy::Isize => IntTy::Isize,
        }
    }

    pub(crate) fn translate_uint_ty(&mut self, it: &ty::UintTy) -> UIntTy {
        match it {
            ty::UintTy::U8 => UIntTy::U8,
            ty::UintTy::U16 => UIntTy::U16,
            ty::UintTy::U32 => UIntTy::U32,
            ty::UintTy::U64 => UIntTy::U64,
            ty::UintTy::U128 => UIntTy::U128,
            ty::UintTy::Usize => UIntTy::Usize,
        }
    }

    /// Translate a Ty.
    ///
    /// Typically used in this module to translate the fields of a structure/
    /// enumeration definition, or later to translate the type of a variable.
    ///
    /// Note that we take as parameter a function to translate regions, because
    /// regions can be translated in several manners (non-erased region or erased
    /// regions), in which case the return type is different.
    pub(crate) fn translate_ty(&mut self, span: Span, mir_ty: ty::Ty) -> Result<Ty, Error> {
        trace!("{:?}", mir_ty);
        if let Some(ty) = self.t_ctx.type_trans_cache.get(&mir_ty).cloned() {
            return Ok(ty.clone());
        }

        let kind = mir_ty.kind();
        let Some(ty) = kind.rigid() else {
            raise_error!(
                self,
                span,
                "Expected a rigid type, got: {:?}\nTrace: {}",
                kind,
                std::backtrace::Backtrace::force_capture()
            );
        };

        let kind = match ty {
            ty::RigidTy::Bool => TyKind::Literal(LiteralTy::Bool),
            ty::RigidTy::Char => TyKind::Literal(LiteralTy::Char),
            ty::RigidTy::Int(int_ty) => {
                TyKind::Literal(LiteralTy::Int(self.translate_int_ty(int_ty)))
            }
            ty::RigidTy::Uint(int_ty) => {
                TyKind::Literal(LiteralTy::UInt(self.translate_uint_ty(int_ty)))
            }
            ty::RigidTy::Float(float_ty) => {
                use ty::FloatTy;
                TyKind::Literal(LiteralTy::Float(match float_ty {
                    FloatTy::F16 => charon_lib::ast::types::FloatTy::F16,
                    FloatTy::F32 => charon_lib::ast::types::FloatTy::F32,
                    FloatTy::F64 => charon_lib::ast::types::FloatTy::F64,
                    FloatTy::F128 => charon_lib::ast::types::FloatTy::F128,
                }))
            }
            ty::RigidTy::Never => TyKind::Never,

            ty::RigidTy::Adt(item, generics) => {
                // FIXME: generics?
                trace!("Adt: {:?}", item.0);
                let id = self.register_type_decl_id(span, *item, generics.clone());
                // no generics since it's monomorphic
                let tref = TypeDeclRef {
                    id: TypeId::Adt(id),
                    generics: Box::new(GenericArgs::empty()),
                };

                // Return the instantiated ADT
                TyKind::Adt(tref)
            }
            ty::RigidTy::Str => {
                let tref = TypeDeclRef::new(TypeId::Builtin(BuiltinTy::Str), GenericArgs::empty());
                TyKind::Adt(tref)
            }
            ty::RigidTy::Array(ty, const_param) => {
                let c = self.translate_tyconst_to_const_generic(span, const_param)?;
                let ty = self.translate_ty(span, *ty)?;
                let tref = TypeDeclRef::new(
                    TypeId::Builtin(BuiltinTy::Array),
                    GenericArgs::new(Vector::new(), [ty].into(), [c].into(), Vector::new()),
                );
                TyKind::Adt(tref)
            }
            ty::RigidTy::Slice(ty) => {
                let ty = self.translate_ty(span, *ty)?;
                let tref = TypeDeclRef::new(
                    TypeId::Builtin(BuiltinTy::Slice),
                    GenericArgs::new_for_builtin([ty].into()),
                );
                TyKind::Adt(tref)
            }
            ty::RigidTy::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = self.translate_region(span, region)?;
                let ty = self.translate_ty(span, *ty)?;
                let kind = RefKind::mutable(matches!(mutability, mir::Mutability::Mut));
                TyKind::Ref(region, ty, kind)
            }
            ty::RigidTy::RawPtr(ty, mutability) => {
                trace!("RawPtr: {:?}", (ty, mutability));
                let ty = self.translate_ty(span, *ty)?;
                let kind = RefKind::mutable(matches!(mutability, mir::Mutability::Mut));
                TyKind::RawPtr(ty, kind)
            }
            ty::RigidTy::Tuple(substs) => {
                let params = substs
                    .iter()
                    .map(|ty| self.translate_ty(span, *ty))
                    .try_collect()?;
                let tref = TypeDeclRef::new(TypeId::Tuple, GenericArgs::new_for_builtin(params));
                TyKind::Adt(tref)
            }

            ty::RigidTy::Foreign(fdef) => {
                let type_id = self.register_foreign_type_decl_id(span, *fdef);
                TyKind::Adt(TypeDeclRef {
                    id: TypeId::Adt(type_id),
                    generics: Box::new(GenericArgs::empty()),
                })
            }

            ty::RigidTy::FnPtr(bsig) => {
                trace!("Arrow");
                trace!("bound vars: {:?}", bsig.bound_vars);
                let sig = &bsig.value;
                let inputs = sig
                    .inputs()
                    .iter()
                    .map(|x| self.translate_ty(span, *x))
                    .try_collect()?;
                let output = self.translate_ty(span, sig.output())?;

                // let sig =
                //     RegionBinder::
                //     self.translate_region_binder(span, sig, |ctx, sig| {
                //     let inputs = sig
                //         .inputs
                //         .iter()
                //         .map(|x| ctx.translate_ty(span, x))
                //         .try_collect()?;
                //     let output = ctx.translate_ty(span, &sig.output)?;
                //     Ok((inputs, output))
                // })?;
                TyKind::FnPtr(RegionBinder::empty((inputs, output)))
            }
            ty::RigidTy::FnDef(item, args) => {
                let instance = mir::mono::Instance::resolve(*item, args)?;
                let fn_id = self.register_fun_decl_id(span, instance);
                let fnref = RegionBinder::empty(FnPtr {
                    kind: Box::new(FnPtrKind::Fun(FunId::Regular(fn_id))),
                    generics: Box::new(GenericArgs::empty()),
                });
                TyKind::FnDef(fnref)
            }
            ty::RigidTy::Closure(def, gargs) => {
                let id = self.register_closure_type_decl_id(span, *def, gargs.clone());
                let tref = TypeDeclRef {
                    id: TypeId::Adt(id),
                    generics: Box::new(GenericArgs::empty()),
                };

                // Return the instantiated ADT
                TyKind::Adt(tref)
            }

            ty::RigidTy::Dynamic(_existential_preds, _region, _) => {
                // TODO: we don't translate the predicates yet because our machinery can't handle
                // it.
                TyKind::DynTrait(DynPredicate {
                    binder: Binder::new(
                        BinderKind::Dyn,
                        GenericParams::empty(),
                        TyKind::Never.into_ty(),
                    ),
                })
            }

            ty::RigidTy::Coroutine(..) => {
                raise_error!(self, span, "Coroutine types are not supported yet")
            }
            ty::RigidTy::Pat(..) => {
                raise_error!(self, span, "Pat types are not supported yet")
            }
            ty::RigidTy::CoroutineClosure(..) => {
                raise_error!(self, span, "Coroutine closure types are not supported yet")
            }
            ty::RigidTy::CoroutineWitness(..) => {
                raise_error!(self, span, "Coroutine witness types are not supported yet")
            }
        };
        let ty = kind.into_ty();
        self.t_ctx.type_trans_cache.insert(mir_ty, ty.clone());
        Ok(ty)
    }

    /// Translate generic args. Don't call directly; use `translate_xxx_ref` as much as possible.
    // pub fn translate_generic_args(
    //     &mut self,
    //     span: Span,
    //     substs: &[ty::GenericArgKind],
    // ) -> Result<GenericArgs, Error> {
    //     use ty::GenericArgKind::*;
    //     trace!("{:?}", substs);

    //     let mut regions = Vector::new();
    //     let mut types = Vector::new();
    //     let mut const_generics = Vector::new();
    //     for param in substs {
    //         match param {
    //             Type(param_ty) => {
    //                 types.push(self.translate_ty(span, *param_ty)?);
    //             }
    //             Lifetime(region) => {
    //                 regions.push(self.translate_region(span, region)?);
    //             }
    //             Const(c) => {
    //                 const_generics.push(self.translate_tyconst_to_const_generic(span, c)?);
    //             }
    //         }
    //     }

    //     Ok(GenericArgs {
    //         regions,
    //         types,
    //         const_generics,
    //         trait_refs: vec![].into(),
    //     })
    // }

    /// Translate a Dynamically Sized Type metadata kind.
    ///
    /// Returns `None` if the type is generic, or if it is not a DST.
    pub fn translate_ptr_metadata(&self) -> PtrMetadata {
        PtrMetadata::None
        // // prepare the call to the method
        // use rustc_middle::ty;
        // let tcx = self.t_ctx.tcx;
        // let rdefid = self.def_id.as_rust_def_id().unwrap();
        // let ty_env = mir::State::new_from_state_and_id(&self.t_ctx.hax_state, rdefid).typing_env();
        // // This `skip_binder` is ok because it's an `EarlyBinder`.
        // let ty = tcx.type_of(rdefid).skip_binder();

        // // call the key method
        // match tcx
        //     .struct_tail_raw(
        //         ty,
        //         |ty| tcx.try_normalize_erasing_regions(ty_env, ty).unwrap_or(ty),
        //         || {},
        //     )
        //     .kind()
        // {
        //     ty::Foreign(..) => Some(PtrMetadata::None),
        //     ty::Str | ty::Slice(..) => Some(PtrMetadata::Length),
        //     ty::Dynamic(..) => Some(PtrMetadata::VTable(VTable)),
        //     // This is NOT accurate -- if there is no generic clause that states `?Sized`
        //     // Then it will be safe to return `Some(PtrMetadata::None)`.
        //     // TODO: inquire the generic clause to get the accurate info.
        //     ty::Placeholder(..) | ty::Infer(..) | ty::Param(..) | ty::Bound(..) => None,
        //     _ => Some(PtrMetadata::None),
        // }
    }

    /// Translate a type layout.
    ///
    /// Translates the layout as queried from rustc into
    /// the more restricted [`Layout`].
    pub fn translate_layout(
        &mut self,
        def: &ty::AdtDef,
        genargs: &ty::GenericArgs,
        kind: &TypeDeclKind,
    ) -> Option<Layout> {
        use rustc_public::abi as r_abi;
        // Panics if the fields layout is not `Arbitrary`.
        fn translate_variant_layout(
            variant_layout: &r_abi::LayoutShape,
            tag: Option<ScalarValue>,
        ) -> VariantLayout {
            match &variant_layout.fields {
                r_abi::FieldsShape::Arbitrary { offsets, .. } => {
                    let mut v = Vector::with_capacity(offsets.len());
                    for o in offsets.iter() {
                        v.push(o.bytes() as u64);
                    }
                    VariantLayout {
                        field_offsets: v,
                        uninhabited: false,
                        tag,
                    }
                }
                r_abi::FieldsShape::Union(fields) => VariantLayout {
                    field_offsets: (0..fields.get()).map(|_| 0).collect::<Vec<_>>().into(),
                    uninhabited: false,
                    tag: None,
                },
                r_abi::FieldsShape::Primitive | r_abi::FieldsShape::Array { .. } => {
                    panic!("Unexpected layout shape: {:?}", variant_layout.fields)
                }
            }
        }

        fn translate_primitive_int(int_ty: &r_abi::IntegerLength, signed: bool) -> IntegerTy {
            if signed {
                match int_ty {
                    r_abi::IntegerLength::I8 => IntegerTy::Signed(IntTy::I8),
                    r_abi::IntegerLength::I16 => IntegerTy::Signed(IntTy::I16),
                    r_abi::IntegerLength::I32 => IntegerTy::Signed(IntTy::I32),
                    r_abi::IntegerLength::I64 => IntegerTy::Signed(IntTy::I64),
                    r_abi::IntegerLength::I128 => IntegerTy::Signed(IntTy::I128),
                }
            } else {
                match int_ty {
                    r_abi::IntegerLength::I8 => IntegerTy::Unsigned(UIntTy::U8),
                    r_abi::IntegerLength::I16 => IntegerTy::Unsigned(UIntTy::U16),
                    r_abi::IntegerLength::I32 => IntegerTy::Unsigned(UIntTy::U32),
                    r_abi::IntegerLength::I64 => IntegerTy::Unsigned(UIntTy::U64),
                    r_abi::IntegerLength::I128 => IntegerTy::Unsigned(UIntTy::U128),
                }
            }
        }

        fn translate_variant_id(r_id: &ty::VariantIdx) -> VariantId {
            VariantId::from_usize(r_id.to_index())
        }

        // Computes the tag representation of the variant's discriminant if possible.
        //
        // If the discriminant is encoded as a niche the following holds:
        // If discriminant != self.discriminant_layout.untagged_variant
        // then tag = (d-self.discriminant_layout.tagged_variants_start).wrapping_add(self.discriminant_layout.niche_start)
        //
        // Note: it is possible that the tag is stored in the niche of a pointer type, but will
        // be returned as an integer instead. This is supposed to be a different interpretation of the same bytes.
        fn translate_discr_to_tag(
            discr: Literal,
            variant: ty::VariantIdx,
            tag_ty: IntegerTy,
            encoding: &r_abi::TagEncoding,
        ) -> Option<ScalarValue> {
            match &encoding {
                // The direct encoding is just a cast.
                r_abi::TagEncoding::Direct => {
                    // FIXME: this is not the most accurate; really we should query rustc
                    Some(ScalarValue::from_bits(tag_ty, discr.as_scalar()?.to_bits()))
                }
                r_abi::TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                } => {
                    if variant == *untagged_variant {
                        None // This variant does not have a tag.
                    } else if variant.to_index() < niche_variants.start().to_index() {
                        // The variant is before the niche variants, so it is not tagged.
                        // Could e.g. be the case if it is uninhabited.
                        None
                    } else {
                        let discr_rel = variant.to_index() - niche_variants.start().to_index();
                        // In theory we need to do a wrapping_add in the tag type,
                        // but we follow the approach of the rustc backends, that
                        // simply does the addition in `u128` and cuts off the uninteresting bits.
                        let tag_bits = (discr_rel as u128).wrapping_add(*niche_start);
                        Some(ScalarValue::from_bits(tag_ty, tag_bits))
                    }
                }
            }
        }

        let Ok(layout) = def.ty_with_args(genargs).layout().map(abi::Layout::shape) else {
            return None;
        };

        let (size, align) = if layout.is_sized() {
            (
                Some(layout.size.bytes() as u64),
                Some(layout.abi_align as u64),
            )
        } else {
            (None, None)
        };

        // Get the layout of the discriminant when there is one (even if it is encoded in a niche).
        let discriminant_layout = match &layout.variants {
            r_abi::VariantsShape::Multiple {
                tag,
                tag_encoding,
                tag_field,
                ..
            } => {
                // The tag_field is the index into the `offsets` vector.
                let r_abi::FieldsShape::Arbitrary { offsets, .. } = &layout.fields else {
                    unreachable!()
                };
                let abi::Scalar::Initialized { value, .. } = tag else {
                    return None;
                };

                let tag_ty = match value {
                    r_abi::Primitive::Int { length, signed } => {
                        translate_primitive_int(length, *signed)
                    }
                    // Try to handle pointer as integers of the same size.
                    r_abi::Primitive::Pointer(_) => IntegerTy::Signed(IntTy::Isize),
                    r_abi::Primitive::Float { .. } => {
                        unreachable!()
                    }
                };

                let encoding = match tag_encoding {
                    r_abi::TagEncoding::Direct => TagEncoding::Direct,
                    r_abi::TagEncoding::Niche {
                        untagged_variant, ..
                    } => TagEncoding::Niche {
                        untagged_variant: translate_variant_id(untagged_variant),
                    },
                };
                offsets.get(*tag_field).map(|s| DiscriminantLayout {
                    offset: s.bytes() as u64,
                    tag_ty,
                    encoding,
                })
            }
            r_abi::VariantsShape::Single { .. } | r_abi::VariantsShape::Empty => None,
        };

        // Try to find the variants even through an alias.
        fn get_variants_from_kind<'a>(
            ty_decls: &'a Vector<TypeDeclId, TypeDecl>,
            ty_decl_kind: &'a TypeDeclKind,
        ) -> Option<&'a Vector<VariantId, Variant>> {
            match ty_decl_kind {
                TypeDeclKind::Enum(variants) => Some(variants),
                TypeDeclKind::Alias(ty) => match ty.kind() {
                    TyKind::Adt(r) => match r.id {
                        TypeId::Adt(td_id) => ty_decls
                            .get(td_id)
                            .and_then(|td| get_variants_from_kind(ty_decls, &td.kind)),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None, // Sometimes, multiple variants can occur for aliases etc.
            }
        }

        let variant_layouts: Vector<VariantId, VariantLayout> = match layout.variants {
            r_abi::VariantsShape::Multiple {
                tag_encoding,
                variants,
                ..
            } => {
                let tag_ty = discriminant_layout
                    .as_ref()
                    .expect("No discriminant layout for enum?")
                    .tag_ty;

                let type_decls = &self.t_ctx.translated.type_decls;
                let variants_from_kind = get_variants_from_kind(type_decls, kind);
                variants
                    .iter()
                    .enumerate()
                    .map(|(id, variant_layout)| {
                        let variant = ty::VariantIdx::to_val(id);
                        let discr = variants_from_kind.map(|variants_from_kind| {
                            variants_from_kind
                                .get(translate_variant_id(&variant))
                                .expect("Variant index out of bounds while getting discr")
                                .discriminant
                                .clone()
                        });

                        let tag = discr.and_then(|discr| {
                            translate_discr_to_tag(discr, variant, tag_ty, &tag_encoding)
                        });
                        translate_variant_layout(variant_layout, tag)
                    })
                    .collect()
            }
            r_abi::VariantsShape::Single { index } => {
                // For structs we add a single variant that has the field offsets. Unions don't
                // have field offsets.
                let tag = kind.is_enum().then(|| {
                    let discr = def.discriminant_for_variant(index);
                    match &discr.ty.kind().rigid() {
                        Some(ty::RigidTy::Int(intty)) => {
                            let intty = self.translate_int_ty(intty);
                            ScalarValue::Signed(intty, discr.val as i128)
                        }
                        Some(ty::RigidTy::Uint(intty)) => {
                            let intty = self.translate_uint_ty(intty);
                            ScalarValue::Unsigned(intty, discr.val as u128)
                        }
                        Some(ty::RigidTy::Ref(..) | ty::RigidTy::RawPtr(..)) => {
                            // This is a niche optimization where the discriminant is stored in the
                            // niche of a pointer. We represent it as an integer instead.
                            ScalarValue::Unsigned(UIntTy::Usize, discr.val as u128)
                        }
                        Some(ty) => {
                            panic!("Expected an integer literal for the discriminant, got {ty:?}")
                        }
                        None => {
                            panic!("Expected a rigid type for the discriminant, got None")
                        }
                    }
                });

                let type_decls = &self.t_ctx.translated.type_decls;
                if let Some(variants) = get_variants_from_kind(type_decls, kind) {
                    variants.map_ref_indexed(|i, _| {
                        if i.index() == index.to_index() {
                            translate_variant_layout(&layout, tag)
                        } else {
                            VariantLayout {
                                uninhabited: true,
                                field_offsets: Vector::new(),
                                tag: None,
                            }
                        }
                    })
                } else {
                    vec![translate_variant_layout(&layout, tag)].into()
                }
            }
            r_abi::VariantsShape::Empty => Vector::new(),
        };

        Some(Layout {
            size,
            align,
            discriminant_layout,
            uninhabited: true,
            variant_layouts,
        })
    }

    /// Translate the body of a type declaration.
    ///
    /// Note that the type may be external, in which case we translate the body
    /// only if it is public (i.e., it is a public enumeration, or it is a
    /// struct with only public fields).
    pub(crate) fn translate_adt_def(
        &mut self,
        trans_id: TypeDeclId,
        def_span: Span,
        item_meta: &ItemMeta,
        adt: &ty::AdtDef,
        generics: &ty::GenericArgs,
    ) -> Result<TypeDeclKind, Error> {
        use ty::AdtKind;

        if item_meta.opacity.is_opaque() {
            return Ok(TypeDeclKind::Opaque);
        }

        trace!("{}", trans_id);

        // In case the type is external, check if we should consider the type as
        // transparent (i.e., extract its body). If it is an enumeration, then yes
        // (because the variants of public enumerations are public, together with their
        // fields). If it is a structure, we check if all the fields are public.
        let contents_are_public = match adt.kind() {
            AdtKind::Enum => true,
            AdtKind::Struct | AdtKind::Union => {
                true
                // // Check the unique variant
                // error_assert!(self, def_span, adt.variants.len() == 1);
                // adt.variants[0]
                //     .fields
                //     .iter()
                //     .all(|f| matches!(f.vis, Visibility::Public))
            }
        };

        if item_meta
            .opacity
            .with_content_visibility(contents_are_public)
            .is_opaque()
        {
            return Ok(TypeDeclKind::Opaque);
        }

        // The type is transparent: explore the variants
        let mut variants: Vector<VariantId, Variant> = Default::default();
        for (i, var_def) in adt.variants_iter().enumerate() {
            trace!("variant {i}: {var_def:?}");

            let mut fields: Vector<FieldId, Field> = Default::default();
            for (j, field_def) in var_def.fields().iter().enumerate() {
                trace!("variant {i}: field {j}: {field_def:?}");
                // Translate the field type
                let ty = field_def.ty_with_args(&generics);
                let ty = self.translate_ty(def_span, ty)?;
                // let field_full_def = self.hax_def(&field_def.did)?;
                // let field_attrs = self.t_ctx.translate_attr_info(&field_full_def);

                // Retrieve the field name.
                let field_name = field_def.name.clone();

                // Store the field
                let field = Field {
                    span: def_span,
                    attr_info: AttrInfo::default(),
                    name: Some(field_name),
                    ty,
                };
                fields.push(field);
            }

            let variant_name = var_def.name().clone();
            let discriminant = {
                let discr = adt.discriminant_for_variant(var_def.idx);

                let ty = self.translate_ty(def_span, discr.ty)?;
                let lit_ty = ty.kind().as_literal().unwrap();
                match Literal::from_bits(lit_ty, discr.val) {
                    Some(lit) => lit,
                    None => raise_error!(self, def_span, "unexpected discriminant type: {ty:?}",),
                }
            };

            let mut variant = Variant {
                span: def_span,
                attr_info: AttrInfo::default(),
                name: variant_name,
                fields,
                discriminant,
            };
            // Propagate a `#[charon::variants_prefix(..)]` or `#[charon::variants_suffix(..)]` attribute to the variants.
            if variant.attr_info.rename.is_none() {
                let prefix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .filter_map(|a| a.as_variants_prefix())
                    .next()
                    .map(|attr| attr.as_str());
                let suffix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .filter_map(|a| a.as_variants_suffix())
                    .next()
                    .map(|attr| attr.as_str());
                if prefix.is_some() || suffix.is_some() {
                    let prefix = prefix.unwrap_or_default();
                    let suffix = suffix.unwrap_or_default();
                    let name = &variant.name;
                    variant.attr_info.rename = Some(format!("{prefix}{name}{suffix}"));
                }
            }
            variants.push(variant);
        }

        // Register the type
        let type_def_kind: TypeDeclKind = match adt.kind() {
            AdtKind::Struct => TypeDeclKind::Struct(variants[0].fields.clone()),
            AdtKind::Enum => TypeDeclKind::Enum(variants),
            AdtKind::Union => TypeDeclKind::Union(variants[0].fields.clone()),
        };

        Ok(type_def_kind)
    }

    pub fn translate_generic_args(
        &mut self,
        span: Span,
        mir_generics: &ty::GenericArgs,
    ) -> Result<GenericArgs, Error> {
        let mut generics = GenericArgs::empty();
        mir_generics
            .0
            .iter()
            .try_for_each(|kind| -> Result<(), Error> {
                match kind {
                    ty::GenericArgKind::Type(ty) => {
                        let ty = self.translate_ty(span, *ty)?;
                        generics.types.push(ty);
                        Ok(())
                    }
                    ty::GenericArgKind::Const(c) => {
                        let c = self.translate_tyconst_to_const_generic(span, c)?;
                        generics.const_generics.push(c);
                        Ok(())
                    }
                    ty::GenericArgKind::Lifetime(region) => {
                        let r = self.translate_region(span, region)?;
                        generics.regions.push(r);
                        Ok(())
                    }
                }
            })?;
        Ok(generics)
    }
}
