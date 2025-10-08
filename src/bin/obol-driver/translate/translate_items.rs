extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_span;

use log::trace;
use rustc_public::{CrateDef, mir, ty};

use charon_lib::{ast::*, register_error};

use crate::translate::{
    translate_body::BodyTransCtx,
    translate_crate::TransItemSource,
    translate_ctx::{ItemTransCtx, TranslateCtx},
};

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    pub(crate) fn translate_item(&mut self, item_src: &TransItemSource) {
        let trans_id = self.id_map.get(&item_src).copied();
        let def_id = item_src.as_def_id();
        self.with_def_id(&def_id, trans_id, |mut ctx| {
            let def_id_internal = rustc_public::rustc_internal::internal(ctx.tcx, def_id);
            let span = ctx.tcx.def_span(def_id_internal);
            let span = rustc_public::rustc_internal::stable(span);
            let span = ctx.translate_span_from_smir(&span);
            // Catch cycles
            let res = {
                // Stopgap measure because there are still many panics in charon and hax.
                let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
                std::panic::catch_unwind(move || ctx.translate_item_aux(item_src, trans_id))
            };
            match res {
                Ok(Ok(())) => return,
                // Translation error
                Ok(Err(_)) => {
                    println!("Item {def_id:?} caused errors; ignoring.");
                    register_error!(ctx, span, "Item `{def_id:?}` caused errors; ignoring.")
                }
                // Panic
                Err(_) => {
                    println!("Item {def_id:?} caused errors; ignoring.");
                    register_error!(
                        ctx,
                        span,
                        "Thread panicked when extracting item `{def_id:?}`."
                    )
                }
            };
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        item_src: &TransItemSource,
        trans_id: Option<ItemId>,
    ) -> Result<(), Error> {
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
            TransItemSource::Global(def) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let global_decl = bt_ctx.translate_global(id, item_meta, &def)?;
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
        }
        Ok(())
    }

    /// Add a `const UNIT: () = ();` const, used as metadata for thin pointers/references.
    pub fn translate_unit_metadata_const(&mut self) {
        use charon_lib::ullbc_ast::*;
        let name = Name::from_path(&["UNIT_METADATA"]);
        let file_id = self.translated.files.push(File {
            name: FileName::Virtual("dummy file".into()),
            crate_name: "dummy".into(),
            contents: None,
        });
        let span = {
            let mut span = Span::dummy();
            span.data.file_id = file_id;
            span
        };
        let item_meta = ItemMeta {
            name,
            span,
            source_text: None,
            attr_info: AttrInfo::default(),
            is_local: false,
            opacity: ItemOpacity::Foreign,
            lang_item: None,
        };

        let body = {
            let mut body = GExprBody {
                span,
                locals: Locals::new(0),
                comments: Default::default(),
                body: Vector::default(),
            };
            let _ = body.locals.new_var(None, Ty::mk_unit());
            body.body.push(BlockData {
                statements: Default::default(),
                terminator: Terminator::new(Span::dummy(), TerminatorKind::Return),
            });
            body
        };

        let global_id = self.translated.global_decls.reserve_slot();

        let initializer = self.translated.fun_decls.push_with(|def_id| FunDecl {
            def_id,
            item_meta: item_meta.clone(),
            src: ItemSource::TopLevel,
            is_global_initializer: Some(global_id),
            signature: FunSig {
                is_unsafe: false,
                generics: Default::default(),
                inputs: vec![],
                output: Ty::mk_unit(),
            },
            body: Ok(Body::Unstructured(body)),
        });
        self.translated.global_decls.set_slot(
            global_id,
            GlobalDecl {
                def_id: global_id,
                item_meta,
                generics: Default::default(),
                ty: Ty::mk_unit(),
                src: ItemSource::TopLevel,
                global_kind: GlobalKind::NamedConst,
                init: initializer,
            },
        );
        self.translated.unit_metadata = Some(GlobalDeclRef {
            id: global_id,
            generics: Box::new(GenericArgs::empty()),
        });
    }
}

impl ItemTransCtx<'_, '_> {
    pub(crate) fn get_item_kind(
        &mut self,
        _span: Span,
        _def: &rustc_public::DefId,
    ) -> Result<ItemSource, Error> {
        Ok(ItemSource::TopLevel)
    }

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

        // Get the kind of the type decl -- is it a closure?
        let src = self.get_item_kind(span, &def.0)?;

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
        let layout = self.translate_layout(def, genargs, &kind);
        let ptr_metadata = self.translate_ptr_metadata();
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            kind,
            src,
            layout,
            repr: None,
            ptr_metadata,
        };

        Ok(type_def)
    }

    pub fn translate_foreign_type_decl(
        mut self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        def: &ty::ForeignDef,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;

        // Translate generics and predicates
        // self.translate_def_generics(span, def)?;

        // Get the kind of the type decl -- is it a closure?
        let src = self.get_item_kind(span, &def.0)?;

        // Translate type body
        let kind = TypeDeclKind::Opaque;
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            kind,
            src,
            layout: None,
            repr: None,
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
        // let span = item_meta.span;

        // Translate the function signature
        trace!("Translating function signature");
        let signature = self.translate_function_signature(def, &item_meta)?;

        // Check whether this function is a method declaration for a trait definition.
        // If this is the case, it shouldn't contain a body.

        // let is_global_initializer = matches!(
        //     def.kind(),
        //     rustc_hir::def::DefKind::Const { .. }
        //         | rustc_hir::def::DefKind::AssocConst { .. }
        //         | rustc_hir::def::DefKind::AnonConst { .. }
        //         | rustc_hir::def::DefKind::InlineConst { .. }
        //         | rustc_hir::def::DefKind::PromotedConst { .. }
        //         | rustc_hir::def::DefKind::Static { .. }
        // );
        // let is_global_initializer =
        //     is_global_initializer.then(|| self.register_global_decl_id(span, &def.def_id));

        let body = if item_meta.opacity.with_private_contents().is_opaque()
            || matches!(def.kind, mir::mono::InstanceKind::Virtual { .. })
            || matches!(def.kind, mir::mono::InstanceKind::Intrinsic)
        {
            None
        } else if def.has_body() {
            def.body()
        } else {
            let inner_id = rustc_public::rustc_internal::internal(self.t_ctx.tcx, def.def.def_id());
            let body_internal = if self.t_ctx.tcx.is_mir_available(inner_id) {
                Some(self.t_ctx.tcx.optimized_mir(inner_id))
            } else if self.t_ctx.tcx.is_ctfe_mir_available(inner_id) {
                Some(self.t_ctx.tcx.mir_for_ctfe(inner_id))
            } else {
                println!("No body for function {:?}", def);
                None
            };
            body_internal.map(rustc_public::rustc_internal::stable)
        };

        let body = if let Some(body) = body {
            let mut bt_ctx = BodyTransCtx::new(&mut self, body.locals());
            match bt_ctx.translate_body(item_meta.span, def, &body) {
                Ok(Ok(body)) => Ok(body),
                // Opaque declaration
                Ok(Err(Opaque)) => Err(Opaque),
                // Translation error.
                // FIXME: handle error cases more explicitly.
                Err(_) => Err(Opaque),
            }
        } else {
            trace!("Instance {} has no body -- left opaque.", def.name(),);
            Err(Opaque)
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            src: ItemSource::TopLevel,
            is_global_initializer: None,
            body,
        })
    }

    // Translate one global.
    pub fn translate_global(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &mir::mono::StaticDef,
    ) -> Result<GlobalDecl, Error> {
        trace!("About to translate global:\n{:?}", def.0);
        let span = item_meta.span;

        // Translate the generics and predicates - globals *can* have generics
        // Ex.:
        // ```
        // impl<const N : usize> Foo<N> {
        //   const LEN : usize = N;
        // }
        // ```
        // self.translate_def_generics(span, def)?;

        // Retrieve the kind
        let item_kind = self.get_item_kind(span, &def.0)?;

        trace!("Translating global type");
        // let ty = match &def.kind {
        //     rustc_hir::def::DefKind::Const { ty, .. }
        //     | rustc_hir::def::DefKind::AssocConst { ty, .. }
        //     | rustc_hir::def::DefKind::AnonConst { ty, .. }
        //     | rustc_hir::def::DefKind::InlineConst { ty, .. }
        //     | rustc_hir::def::DefKind::PromotedConst { ty, .. }
        //     | rustc_hir::def::DefKind::Static { ty, .. } => ty,
        //     _ => panic!("Unexpected def for constant: {def:?}"),
        // };
        let ty = self.translate_ty(span, def.ty())?;

        // let global_kind = match &def. {
        //     rustc_hir::def::DefKind::Static { .. } => GlobalKind::Static,
        //     rustc_hir::def::DefKind::Const { .. } | rustc_hir::def::DefKind::AssocConst { .. } => {
        //         GlobalKind::NamedConst
        //     }
        //     rustc_hir::def::DefKind::AnonConst { .. }
        //     | rustc_hir::def::DefKind::InlineConst { .. }
        //     | rustc_hir::def::DefKind::PromotedConst { .. } => GlobalKind::AnonConst,
        //     _ => panic!("Unexpected def for constant: {def:?}"),
        // };
        let global_kind = GlobalKind::Static; // For now, we only support statics.

        let instance: mir::mono::Instance = (*def).into();
        let initializer = self.register_fun_decl_id(span, instance);

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: GenericParams::empty(),
            ty,
            src: item_kind,
            global_kind,
            init: initializer,
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

        // Get the kind of the type decl -- is it a closure?
        let src = self.get_item_kind(span, &def.0)?;

        // Translate type body
        let kind = self.translate_closure_as_adt_def(trans_id, span, &item_meta, def, genargs);

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => TypeDeclKind::Error(err.msg),
        };
        let layout = None;
        let ptr_metadata = self.translate_ptr_metadata();
        let type_def = TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: GenericParams::empty(),
            kind,
            src,
            layout,
            repr: None,
            ptr_metadata,
        };

        Ok(type_def)
    }
}
