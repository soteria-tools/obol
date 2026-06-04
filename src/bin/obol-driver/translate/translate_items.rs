extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_span;

use log::trace;
use rustc_public::{CrateDef, mir, ty};

use charon_lib::{ast::*, raise_error, register_error};

use crate::translate::{
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
                    println!("Item {name} caused errors; ignoring. {msg:?}");
                    sanitize_name(&mut ctx);
                    register_error!(ctx, span, "Item `{name}` caused errors; ignoring.")
                }
                // Panic
                Err(msg) => {
                    println!("Item {name} caused errors; ignoring. {msg:?}");
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
                let global_decl = bt_ctx.translate_global(id, item_meta, &def, *ty)?;
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
            TransItemSource::GlobalConstFn(stt, ty) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_global_const_fn(id, item_meta, stt.clone(), *ty)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSource::Static(stt) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let decl = bt_ctx.translate_global_from_static(id, item_meta, *stt)?;
                self.translated.global_decls.set_slot(id, decl);
            }
            TransItemSource::StaticFn(stt) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let decl = bt_ctx.translate_global_from_static_fn(id, item_meta, *stt)?;
                self.translated.fun_decls.set_slot(id, decl);
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
        } else if let Some((is_polymorphic, body)) = self.get_body(def) {
            let generics = if is_polymorphic {
                Some(def.args())
            } else {
                None
            };
            let mut bt_ctx = BodyTransCtx::new(&mut self, body.locals(), &mut signature, generics);
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
        let alloc: mir::alloc::GlobalAlloc = def.clone().into();
        let (global_kind, init) = match alloc {
            mir::alloc::GlobalAlloc::Static(static_def) => {
                let instance: mir::mono::Instance = static_def.into();

                // Some statics don't have a body, such as non-generics in the sysroot.
                let initializer = if instance.has_body() {
                    self.register_fun_decl_id(span, instance)
                } else {
                    self.register_global_const_fn(span, def.clone(), ty)
                };

                (GlobalKind::Static, initializer)
            }
            mir::alloc::GlobalAlloc::Memory(..) => {
                let initializer = self.register_global_const_fn(span, def.clone(), ty);
                (GlobalKind::AnonConst, initializer)
            }
            mir::alloc::GlobalAlloc::TypeId { .. } => {
                let initializer = self.register_global_const_fn(span, def.clone(), ty);
                (GlobalKind::AnonConst, initializer)
            }
            mir::alloc::GlobalAlloc::VTable(..) => {
                panic!("Shouldn't reach a VTable global")
            }
            mir::alloc::GlobalAlloc::Function(..) => {
                unreachable!("Shouldn't reach a global function")
            }
        };
        let ty = match ty {
            Some(ty) => self.translate_ty(span, ty)?,
            None => TyKind::Error("Untype global".into()).into_ty(),
        };

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: GenericParams::empty(),
            ty,
            src: item_kind,
            global_kind,
            init,
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

    fn make_trivial_return_function(
        self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        span: Span,
        const_expr: ConstantExpr,
        output: Ty,
        global_id: GlobalDeclId,
    ) -> Result<FunDecl, Error> {
        let signature = FunSig {
            is_unsafe: false,
            inputs: vec![],
            output: output.clone(),
            abi: Abi::rust(),
        };

        use ullbc_ast::*;

        let mut locals = Locals::new(0);
        locals.locals.push_with(|index| Local {
            index,
            name: None,
            ty: output.clone(),
            span,
        });
        let body = Body::Unstructured(GExprBody {
            body: vec![BlockData {
                statements: vec![Statement::new(
                    span,
                    StatementKind::Assign(
                        locals.return_place(),
                        Rvalue::Use(Operand::Const(Box::new(const_expr)), WithRetag::No),
                    ),
                )],
                terminator: Terminator::new(span, ullbc_ast::TerminatorKind::Return),
            }]
            .into(),
            bound_body_regions: 0,
            span,
            locals,
            comments: vec![],
        });

        Ok(FunDecl {
            def_id,
            item_meta,
            signature: Box::new(signature),
            generics: GenericParams::empty(),
            src: ItemSource::TopLevel,
            is_global_initializer: Some(global_id),
            body,
        })
    }

    pub fn translate_global_const_fn(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: mir::alloc::AllocId,
        rty: Option<ty::Ty>,
    ) -> Result<FunDecl, Error> {
        let alloc: mir::alloc::GlobalAlloc = def.clone().into();

        let (span, const_expr, ty) = match alloc {
            mir::alloc::GlobalAlloc::Static(def) => {
                let span = self.translate_span_from_smir(&def.span());
                let alloc = def.eval_initializer()?;
                let (const_expr, ty) = self.translate_alloc_to_const(span, &alloc, rty)?;
                (span, const_expr, ty)
            }
            mir::alloc::GlobalAlloc::Memory(mem) => {
                let span = Span::dummy();
                let (const_expr, ty) = self.translate_alloc_to_const(span, &mem, rty)?;
                (span, const_expr, ty)
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
                (span, const_val, output)
            }
            _ => {
                panic!("Cannot translate global const fn: {def:?}")
            }
        };
        let global_id = self.register_global_decl_id(span, def, rty);

        self.make_trivial_return_function(def_id, item_meta, span, const_expr, ty, global_id)
    }

    pub fn translate_global_from_static(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: mir::mono::StaticDef,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global from static:\n{:?}", def);
        let span = item_meta.span;

        // Retrieve the kind
        let item_kind = ItemSource::TopLevel;
        trace!("Translating global type");
        let initializer = self.register_global_from_static_fn(span, def);
        let ty = self.translate_ty(span, def.ty())?;

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: GenericParams::empty(),
            ty,
            src: item_kind,
            global_kind: GlobalKind::Static,
            init: initializer,
        })
    }

    pub fn translate_global_from_static_fn(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: mir::mono::StaticDef,
    ) -> Result<FunDecl, Error> {
        let span = def.span();
        let span = self.translate_span_from_smir(&span);
        let alloc = def.eval_initializer()?;
        let (const_expr, ty) = self.translate_alloc_to_const(span, &alloc, Some(def.ty()))?;
        let global_id = self.register_global_from_static(span, def);
        self.make_trivial_return_function(def_id, item_meta, span, const_expr, ty, global_id)
    }
}
