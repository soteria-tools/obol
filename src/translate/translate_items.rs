extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate stable_mir;

use log::trace;
use stable_mir::{mir, ty};

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
            let span = Span::dummy();
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
                    register_error!(ctx, span, "Item `{def_id:?}` caused errors; ignoring.")
                }
                // Panic
                Err(_) => register_error!(
                    ctx,
                    span,
                    "Thread panicked when extracting item `{def_id:?}`."
                ),
            };
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        item_src: &TransItemSource,
        trans_id: Option<AnyTransId>,
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
                let Some(AnyTransId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let generics = generics.clone().into();
                let ty = bt_ctx.translate_type_decl(id, item_meta, &adt, &generics)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::Fun(instance) => {
                let Some(AnyTransId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_function(id, item_meta, *instance)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSource::Global(def) => {
                let Some(AnyTransId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let global_decl = bt_ctx.translate_global(id, item_meta, &def)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            TransItemSource::Closure(def, generics) => {
                let Some(AnyTransId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let generics: ty::GenericArgs = generics.clone().into();
                let ty = bt_ctx.translate_closure_adt(id, item_meta, &def, &generics)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::ClosureAsFn(def, generics) => {
                let Some(AnyTransId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let generics: ty::GenericArgs = generics.clone().into();
                let fun_decl =
                    bt_ctx.translate_stateless_closure_as_fn(id, item_meta, &def, &generics)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
        }
        Ok(())
    }
}

impl ItemTransCtx<'_, '_> {
    pub(crate) fn get_item_kind(
        &mut self,
        _span: Span,
        _def: &stable_mir::DefId,
    ) -> Result<ItemKind, Error> {
        Ok(ItemKind::TopLevel)
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
            ptr_metadata,
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

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else if let Some(body) = def.body() {
            // Translate the body. This doesn't store anything if we can't/decide not to translate
            // this body.
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
            Err(Opaque)
        };
        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind: ItemKind::TopLevel,
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
            kind: item_kind,
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
            ptr_metadata,
        };

        Ok(type_def)
    }
}
