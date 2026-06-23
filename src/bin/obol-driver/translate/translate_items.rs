extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_span;

use log::trace;
use rustc_public::{CrateDef, mir, ty};

use charon_lib::{ast::*, raise_error, register_error};

use crate::translate::{
    my_gen_args::MyGenericArgs,
    translate_body::BodyTransCtx,
    translate_crate::TransItemSource,
    translate_ctx::{ItemTransCtx, TranslateCtx},
};

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    pub(crate) fn translate_item(&mut self, item_src: &TransItemSource) {
        let trans_id = self.id_map.get(&item_src).copied();
        self.with_item_id(trans_id, |mut ctx| {
            let (name, span) = if let Some(def_id) = item_src.as_def_id() {
                let def_id_internal = rustc_public::rustc_internal::internal(ctx.tcx, def_id);
                let span = ctx.tcx.def_span(def_id_internal);
                let span = rustc_public::rustc_internal::stable(span);
                let span = ctx.translate_span_from_smir(&span);
                (def_id.name(), span)
            } else {
                (format!("{:?}", item_src), Span::dummy())
            };
            // Catch cycles
            let res = {
                // Stopgap measure because there are still many panics in charon and hax.
                let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
                std::panic::catch_unwind(move || ctx.translate_item_aux(item_src, trans_id))
            };
            // Strip PathElem::Instantiated from the name before error reporting, since those
            // reference types that may not yet be in item_names, causing a panic in
            // report_external_dep_error. The name is always inserted first in translate_item_aux.
            let sanitize_name = |ctx: &mut TranslateCtx<'_>| {
                if let Some(trans_id) = trans_id
                    && let Some(n) = ctx.translated.item_names.get(&trans_id)
                {
                    let safe_name = Name {
                        name: n
                            .name
                            .iter()
                            .filter(|e| !matches!(e, PathElem::Instantiated(_)))
                            .cloned()
                            .collect(),
                    };
                    ctx.translated.item_names.insert(trans_id, safe_name);
                }
            };
            match res {
                Ok(Ok(())) => return,
                // Translation error
                Ok(Err(msg)) => {
                    trace!("Item {name} caused errors; ignoring. {msg:?}");
                    sanitize_name(&mut ctx);
                    register_error!(ctx, span, "Item `{name}` caused errors; ignoring.")
                }
                // Panic
                Err(msg) => {
                    trace!("Item {name} caused errors; ignoring. {msg:?}");
                    sanitize_name(&mut ctx);
                    register_error!(ctx, span, "Thread panicked when extracting item `{name}`.")
                }
            };
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        item_src: &TransItemSource,
        trans_id: Option<ItemId>,
    ) -> Result<(), Error> {
        // Pre-insert a single-segment fallback name so that if register_error! fires inside
        // translate_name (e.g. while translating generic args), charon's error formatting can
        // look up item_names without panicking. The real name overwrites it below.
        if let (Some(trans_id), Some(def_id)) = (trans_id, item_src.as_def_id()) {
            self.translated
                .item_names
                .entry(trans_id)
                .or_insert_with(|| Name {
                    name: vec![PathElem::Ident(def_id.name().into(), Disambiguator::ZERO)],
                });
        }

        // Translate the meta information
        let name = self.translate_name(item_src)?;
        if let Some(trans_id) = trans_id {
            self.translated.item_names.insert(trans_id, name.clone());
        }
        let item_meta = self.translate_item_meta(item_src, name);

        // Initialize the item translation context

        let bt_ctx = ItemTransCtx::new(trans_id, self);
        match item_src {
            TransItemSource::Type(adt, generics) => {
                let Some(ItemId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let generics = generics.clone().into();
                let ty = bt_ctx.translate_type_decl(id, item_meta, &adt, &generics)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::Fun(instance) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_function(id, item_meta, *instance)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSource::Global(def, ty) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let global_decl = bt_ctx.translate_global(id, item_meta, &def, ty.0)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            TransItemSource::Closure(def, generics) => {
                let Some(ItemId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let generics: ty::GenericArgs = generics.clone().into();
                let ty = bt_ctx.translate_closure_adt(id, item_meta, &def, &generics)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::ClosureAsFn(def, generics) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let generics: ty::GenericArgs = generics.clone().into();
                let fun_decl =
                    bt_ctx.translate_stateless_closure_as_fn(id, item_meta, &def, &generics)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSource::ForeignType(def) => {
                let Some(ItemId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let ty = bt_ctx.translate_foreign_type_decl(id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::VTable(ty, tref) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let tref = tref
                    .clone()
                    .map(|(def_id, args)| ty::TraitRef::try_new(def_id, args.into()).unwrap());
                let decl = bt_ctx.translate_vtable(id, item_meta, *ty, tref)?;
                self.translated.global_decls.set_slot(id, decl);
            }
            TransItemSource::VTableInit(ty, tref) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let tref = tref
                    .clone()
                    .map(|(def_id, args)| ty::TraitRef::try_new(def_id, args.into()).unwrap());
                let decl = bt_ctx.translate_vtable_init(id, item_meta, *ty, tref)?;
                self.translated.fun_decls.set_slot(id, decl);
            }
            TransItemSource::Static(stt) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let decl = bt_ctx.translate_global_from_static(id, item_meta, *stt)?;
                self.translated.global_decls.set_slot(id, decl);
            }
            TransItemSource::NamedConst(def, args) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let decl = bt_ctx.translate_named_const(id, item_meta, *def, args.clone())?;
                self.translated.global_decls.set_slot(id, decl);
            }
            TransItemSource::TraitDecl(_) => {
                let Some(ItemId::TraitDecl(id)) = trans_id else {
                    unreachable!()
                };
                let decl = bt_ctx.translate_trait_decl(id, item_meta)?;
                self.translated.trait_decls.set_slot(id, decl);
            }
            TransItemSource::TraitImpl(impl_def_id) => {
                let Some(ItemId::TraitImpl(id)) = trans_id else {
                    unreachable!()
                };
                let decl = bt_ctx.translate_trait_impl(id, item_meta, *impl_def_id)?;
                self.translated.trait_impls.set_slot(id, decl);
            }
        }
        Ok(())
    }

    pub fn translate_fake_dyn_trait(&mut self) {
        let fake_name = Name {
            name: vec![PathElem::Ident("FakeTrait".into(), Disambiguator::ZERO)],
        };
        self.translated
            .item_names
            .insert(ItemId::TraitDecl(TraitDeclId::ZERO), fake_name.clone());
        // Add this dummy file just in case nothing translate, so all dummy spans still have a file to point to.
        self.translated.files.push(File {
            id: FileId::ZERO,
            name: FileName::NotReal("dummy".into()),
            crate_name: "dummy".into(),
            contents: None,
        });
        self.translated.trait_decls.push(TraitDecl {
            def_id: TraitDeclId::ZERO,
            item_meta: ItemMeta {
                name: fake_name,
                span: Span::dummy(),
                source_text: None,
                attr_info: AttrInfo::default(),
                is_local: false,
                opacity: ItemOpacity::Transparent,
                lang_item: None,
            },
            generics: GenericParams::empty(),
            implied_clauses: vec![].into(),
            consts: IndexMap::new(),
            types: IndexMap::new(),
            methods: IndexMap::new(),
            vtable: Some(TypeDeclRef {
                id: TypeId::Tuple,
                generics: Box::new(GenericArgs::empty()),
            }),
        });
    }
}

impl ItemTransCtx<'_, '_> {
    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    pub fn translate_type_decl(
        mut self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        def: &ty::AdtDef,
        genargs: &ty::GenericArgs,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;

        // Translate generics and predicates
        // self.translate_def_generics(span, def)?;

        // Translate type body
        let kind = match &def.kind() {
            _ if item_meta.opacity.is_opaque() => Ok(TypeDeclKind::Opaque),
            ty::AdtKind::Struct | ty::AdtKind::Enum | ty::AdtKind::Union => {
                self.translate_adt_def(trans_id, span, &item_meta, def, genargs)
            }
        };

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => TypeDeclKind::Error(err.msg),
        };
        let layout = self
            .translate_layout(def, genargs)
            .into_iter()
            .map(|l| (self.t_ctx.get_target_triple(), l))
            .collect();
        let ptr_metadata = self.translate_ptr_metadata();
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            kind,
            src: ItemSource::TopLevel,
            layout,
            ptr_metadata,
        };

        Ok(type_def)
    }

    pub fn translate_foreign_type_decl(
        self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        _def: &ty::ForeignDef,
    ) -> Result<TypeDecl, Error> {
        // Translate generics and predicates
        // self.translate_def_generics(span, def)?;

        // Translate type body
        let kind = TypeDeclKind::Opaque;
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            kind,
            src: ItemSource::TopLevel,
            layout: Default::default(),
            ptr_metadata: PtrMetadata::None,
        };

        Ok(type_def)
    }

    /// Translate one function.
    pub fn translate_function(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: mir::mono::Instance,
    ) -> Result<FunDecl, Error> {
        trace!("About to translate function:\n{:?}", def);
        let span = item_meta.span;

        // Translate the function signature
        trace!("Translating function signature");
        let mut signature = self.translate_function_signature(def, span)?;

        let body = if let Some(name) = def.intrinsic_name() {
            let arg_names = self.translate_argument_names(def, signature.inputs.len());
            Body::Intrinsic { name, arg_names }
        } else if let Some(name) = self.as_extern_name(def) {
            Body::Extern(name)
        } else if item_meta.opacity.with_private_contents().is_opaque()
            || matches!(def.kind, mir::mono::InstanceKind::Virtual { .. })
            || matches!(def.kind, mir::mono::InstanceKind::Intrinsic)
        {
            Body::Opaque
        } else if let Some(body) = self.get_body(def) {
            let mut bt_ctx = BodyTransCtx::new(&mut self, body.locals(), &mut signature);
            bt_ctx.translate_body(span, def, &body)
        } else {
            trace!("Instance {} has no body -- left opaque.", def.name(),);
            Body::Missing
        };

        let internal = rustc_public::rustc_internal::internal(self.t_ctx.tcx, def.def.def_id());
        let src = if self.t_ctx.tcx.is_closure_like(internal) {
            let closure_ty = self
                .t_ctx
                .tcx
                .type_of(internal)
                .instantiate_identity()
                .skip_normalization();
            let closure_ty = rustc_public::rustc_internal::stable(closure_ty).kind();
            let Some(ty::RigidTy::Closure(def, args)) = closure_ty.rigid() else {
                panic!("Closure-like instance has non-closure type: {closure_ty:?}")
            };
            self.translate_closure_src_info(span, def, args)?
        } else {
            ItemSource::TopLevel
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature: Box::new(signature),
            generics: GenericParams::empty(),
            src,
            is_global_initializer: None,
            body,
        })
    }

    /// Build a global's `value` as a call to its (separately-translated) initializer function.
    /// Used for globals whose value we don't compute directly (statics with a body, vtables).
    pub(crate) fn call_initializer(&self, init: FunDeclId, ty: Ty) -> ConstantExpr {
        ConstantExpr {
            kind: ConstantExprKind::Call(
                FnPtr {
                    kind: Box::new(FnPtrKind::Fun(FunId::Regular(init))),
                    generics: Box::new(GenericArgs::empty()),
                },
                vec![],
            ),
            ty,
        }
    }

    /// Evaluate the value of a global identified by its allocation id.
    fn translate_global_alloc_value(
        &mut self,
        def: &mir::alloc::AllocId,
        rty: Option<ty::Ty>,
    ) -> Result<ConstantExpr, Error> {
        let alloc: mir::alloc::GlobalAlloc = def.clone().into();
        let (const_expr, _ty) = match alloc {
            mir::alloc::GlobalAlloc::Static(def) => {
                let span = self.translate_span_from_smir(&def.span());
                let alloc = def.eval_initializer()?;
                self.translate_alloc_to_const(span, &alloc, rty)?
            }
            mir::alloc::GlobalAlloc::Memory(mem) => {
                self.translate_alloc_to_const(Span::dummy(), &mem, rty)?
            }
            mir::alloc::GlobalAlloc::TypeId { ty: type_id_ty } => {
                let span = Span::dummy();
                let Some(output_ty) = rty else {
                    raise_error!(self, span, "TypeId global missing type annotation")
                };
                let output = self.translate_ty(span, output_ty)?;
                let translated_ty = self.translate_ty(span, type_id_ty)?;
                let const_val = ConstantExpr {
                    kind: ConstantExprKind::TypeId(translated_ty),
                    ty: output.clone(),
                };
                (const_val, output)
            }
            _ => {
                panic!("Cannot translate global value: {def:?}")
            }
        };
        Ok(const_expr)
    }

    // Translate one global.
    pub fn translate_global(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &mir::alloc::AllocId,
        ty: Option<ty::Ty>,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global:\n{:?}", def);
        let span = item_meta.span;

        // Retrieve the kind
        let item_kind = ItemSource::TopLevel;
        trace!("Translating global type");
        let translated_ty = match ty {
            Some(ty) => self.translate_ty(span, ty)?,
            None => TyKind::Error("Untype global".into()).into_ty(),
        };
        let alloc: mir::alloc::GlobalAlloc = def.clone().into();
        let (global_kind, value) = match alloc {
            mir::alloc::GlobalAlloc::Static(static_def) => {
                let instance: mir::mono::Instance = static_def.into();

                // Some statics don't have a body, such as non-generics in the sysroot. For those
                // we evaluate the value directly; otherwise we call the initializer function.
                // Foreign/extern statics have no in-crate initializer to evaluate either, so we likewise
                // call a body-less extern initializer function.
                let value = if instance.has_body() || instance.is_foreign_item() {
                    let init = self.register_fun_decl_id(span, instance);
                    self.call_initializer(init, translated_ty.clone())
                } else {
                    self.translate_global_alloc_value(def, ty)?
                };
                (GlobalKind::Static, value)
            }
            mir::alloc::GlobalAlloc::Memory(..) | mir::alloc::GlobalAlloc::TypeId { .. } => {
                let value = self.translate_global_alloc_value(def, ty)?;
                (GlobalKind::AnonConst, value)
            }
            mir::alloc::GlobalAlloc::VTable(..) => {
                panic!("Shouldn't reach a VTable global")
            }
            mir::alloc::GlobalAlloc::Function(..) => {
                unreachable!("Shouldn't reach a global function")
            }
        };

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: GenericParams::empty(),
            ty: translated_ty,
            src: item_kind,
            global_kind,
            value,
        })
    }

    pub fn translate_closure_adt(
        mut self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        def: &ty::ClosureDef,
        genargs: &ty::GenericArgs,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;

        // Translate generics and predicates
        // self.translate_def_generics(span, def)?;

        let src = self.translate_closure_src_info(span, def, genargs)?;

        // Translate type body
        let kind = self.translate_closure_as_adt_def(trans_id, span, &item_meta, def, genargs);

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => TypeDeclKind::Error(err.msg),
        };
        let ptr_metadata = self.translate_ptr_metadata();
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            kind,
            src,
            layout: Default::default(),
            ptr_metadata,
        };

        Ok(type_def)
    }

    pub fn translate_global_from_static(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: mir::mono::StaticDef,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global from static:\n{:?}", def);
        let item_kind = ItemSource::TopLevel;
        trace!("Translating global type");

        let span = self.translate_span_from_smir(&def.span());
        let internal_def_id = rustc_public::rustc_internal::internal(self.t_ctx.tcx, def.def_id());
        let (value, ty) = if self.t_ctx.tcx.is_foreign_item(internal_def_id) {
            // Foreign/extern statics have no in-crate initializer to evaluate.
            // Emit a call to a body-less extern initializer function.
            let ty = self.translate_ty(span, def.ty())?;
            let instance: mir::mono::Instance = def.into();
            let init = self.register_fun_decl_id(span, instance);
            (self.call_initializer(init, ty.clone()), ty)
        } else {
            // Evaluate the static's initializer directly into the global's value.
            let alloc = def.eval_initializer()?;
            self.translate_alloc_to_const(span, &alloc, Some(def.ty()))?
        };

        // Distinguish thread-local statics (`#[thread_local]`) from regular ones.
        let global_kind = if self.t_ctx.tcx.is_thread_local_static(internal_def_id) {
            GlobalKind::ThreadLocal
        } else {
            GlobalKind::Static
        };

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: GenericParams::empty(),
            ty,
            src: item_kind,
            global_kind,
            value,
        })
    }

    pub fn translate_named_const(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        const_def: ty::ConstDef,
        args: MyGenericArgs,
    ) -> Result<GlobalDecl, Error> {
        let span = item_meta.span;
        let tcx = self.t_ctx.tcx;
        let internal_def = rustc_public::rustc_internal::internal(tcx, const_def.def_id());
        let gargs: ty::GenericArgs = args.clone().into();
        let internal_args = rustc_public::rustc_internal::internal(tcx, gargs);
        let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
        // Normalize so that e.g. array-length consts in the type get evaluated.
        let unnorm_ty = tcx.type_of(internal_def).instantiate(tcx, internal_args);
        let internal_ty = tcx
            .try_normalize_erasing_regions(typing_env, unnorm_ty)
            .unwrap_or_else(|_| unnorm_ty.skip_normalization());
        let ty = self.translate_ty(span, rustc_public::rustc_internal::stable(internal_ty))?;

        // Evaluate the const directly into the global's value.
        let uneval = rustc_middle::mir::UnevaluatedConst::new(internal_def, internal_args);
        let cnst = rustc_middle::mir::Const::Unevaluated(uneval, internal_ty);
        let eval_span = tcx.def_span(internal_def);
        let value = match cnst.eval(tcx, typing_env, eval_span) {
            Ok(val) => {
                let evaluated = rustc_middle::mir::Const::Val(val, internal_ty);
                let stable_const = rustc_public::rustc_internal::stable(evaluated);
                self.translate_const_value(span, &stable_const)?
            }
            Err(e) => {
                raise_error!(self, span, "Could not evaluate named const: {:?}", e)
            }
        };

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: GenericParams::empty(),
            ty,
            src: ItemSource::TopLevel,
            global_kind: GlobalKind::NamedConst,
            value,
        })
    }

    /// Build a definition's generic parameters so the variables in its name render with their
    /// source names rather than as `missing(@TypeN)`.
    ///
    /// `translate_ty`/`translate_tyconst` map a `Param` to a free var whose id is rustc's *combined*
    /// index over all generic parameters. Charon stores each kind in its own (`Vec`-backed) vector,
    /// so we place each param at that combined index in the relevant vector, padding the slots that
    /// belong to other-kind params (never looked up there) to keep the indexing dense.
    pub(crate) fn translate_def_generic_params(
        &mut self,
        def_id: rustc_public::DefId,
    ) -> GenericParams {
        use rustc_middle::ty::GenericParamDefKind;
        let internal = rustc_public::rustc_internal::internal(self.t_ctx.tcx, def_id);
        let generics = self.t_ctx.tcx.generics_of(internal);
        // Const generic params need a type, but we only use these params for naming and never
        // inspect it; use an error type so it can't be mistaken for a real one.
        let placeholder_ty = || TyKind::Error("const generic param type".to_string()).into_ty();
        let mut params = GenericParams::empty();
        for param in &generics.own_params {
            let index = param.index as usize;
            let name = param.name.to_string();
            match param.kind {
                GenericParamDefKind::Lifetime => {
                    while params.regions.len() < index {
                        let i = RegionId::from_raw(params.regions.len());
                        params.regions.push(RegionParam {
                            index: i,
                            name: None,
                            mutability: LifetimeMutability::Unknown,
                        });
                    }
                    params.regions.push(RegionParam {
                        index: RegionId::from_raw(index),
                        name: Some(name),
                        mutability: LifetimeMutability::Unknown,
                    });
                }
                GenericParamDefKind::Type { .. } => {
                    while params.types.len() < index {
                        let i = TypeVarId::from_raw(params.types.len());
                        params.types.push(TypeParam {
                            index: i,
                            name: "_".to_string(),
                        });
                    }
                    params.types.push(TypeParam {
                        index: TypeVarId::from_raw(index),
                        name,
                    });
                }
                GenericParamDefKind::Const { .. } => {
                    while params.const_generics.len() < index {
                        let i = ConstGenericVarId::from_raw(params.const_generics.len());
                        params.const_generics.push(ConstGenericParam {
                            index: i,
                            name: "_".to_string(),
                            ty: placeholder_ty(),
                        });
                    }
                    params.const_generics.push(ConstGenericParam {
                        index: ConstGenericVarId::from_raw(index),
                        name,
                        ty: placeholder_ty(),
                    });
                }
            }
        }
        params
    }

    /// Barebones trait declaration: just enough for its name to be referenced from a
    /// `PathElem::Impl`. We omit the trait's contents, which we never use.
    pub fn translate_trait_decl(
        self,
        trans_id: TraitDeclId,
        item_meta: ItemMeta,
    ) -> Result<TraitDecl, Error> {
        Ok(TraitDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            implied_clauses: vec![].into(),
            consts: IndexMap::new(),
            types: IndexMap::new(),
            methods: IndexMap::new(),
            vtable: None,
        })
    }

    /// Barebones trait implementation: records which trait is implemented and its arguments (so the
    /// impl renders as `{impl Trait for Ty}`), but omits the implemented items.
    pub fn translate_trait_impl(
        mut self,
        trans_id: TraitImplId,
        item_meta: ItemMeta,
        impl_def_id: rustc_public::DefId,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;
        let internal = rustc_public::rustc_internal::internal(self.t_ctx.tcx, impl_def_id);
        let trait_ref = self.t_ctx.tcx.impl_trait_ref(internal).skip_binder();
        let trait_ref = rustc_public::rustc_internal::stable(trait_ref);

        let trait_decl_id = self.register_trait_decl_id(span, trait_ref.def_id);
        // The args only feed the impl's name; degrade to empty rather than failing the item if some
        // argument can't be translated.
        let generics = self
            .translate_generic_args(span, &trait_ref.args())
            .unwrap_or_else(|_| GenericArgs::empty());

        Ok(TraitImpl {
            def_id: trans_id,
            item_meta,
            impl_trait: TraitDeclRef {
                id: trait_decl_id,
                generics: Box::new(generics),
            },
            generics: self.translate_def_generic_params(impl_def_id),
            implied_trait_refs: vec![].into(),
            consts: IndexMap::new(),
            types: IndexMap::new(),
            methods: IndexMap::new(),
            vtable: None,
        })
    }
}
