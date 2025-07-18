extern crate rustc_abi;
extern crate rustc_middle;
extern crate rustc_smir;
extern crate stable_mir;

use crate::translate::my_gen_args::MyGenericArgs;

use super::translate_ctx::*;

use charon_lib::ast::*;
use charon_lib::errors::ErrorCtx;
use charon_lib::options::{CliOpts, TranslateOptions};
use charon_lib::transform::TransformCtx;
use log::trace;
use rustc_middle::ty::TyCtxt;
use rustc_smir::IndexedVal;
use stable_mir::rustc_internal::{self};
use stable_mir::{CrateDef, DefId};
use stable_mir::{mir, ty};
use std::cell::RefCell;
use std::hash::Hash;

/// The id of an untranslated item. Note that a given `DefId` may show up as multiple different
/// item sources, e.g. a constant will have both a `Global` version (for the constant itself) and a
/// `FunDecl` one (for its initializer function).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TransItemSource {
    Global(DefId),
    Fun(mir::mono::Instance),
    Type(ty::AdtDef, MyGenericArgs),
    Closure(ty::ClosureDef, MyGenericArgs),
}

impl TransItemSource {
    pub(crate) fn as_def_id(&self) -> DefId {
        match self {
            TransItemSource::Global(id) => id.clone(),
            TransItemSource::Fun(instance) => instance.def.def_id(),
            TransItemSource::Type(id, _) => id.0,
            TransItemSource::Closure(def, _) => def.def_id(),
        }
    }

    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord {
        match self {
            TransItemSource::Global(id) => (0, id.to_index(), 0),
            TransItemSource::Fun(instance) => (1, instance.def.def_id().to_index(), 0),
            TransItemSource::Type(id, gargs) => (2, id.0.to_index(), gargs.sort_key()),
            TransItemSource::Closure(def, gargs) => (3, def.def_id().to_index(), gargs.sort_key()),
        }
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for TransItemSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TransItemSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    pub(crate) fn register_id_no_enqueue(
        &mut self,
        src: &Option<DepSource>,
        id: TransItemSource,
    ) -> AnyTransId {
        let item_id = match self.id_map.get(&id) {
            Some(tid) => *tid,
            None => {
                let trans_id = match id {
                    TransItemSource::Type(..) | TransItemSource::Closure(..) => {
                        AnyTransId::Type(self.translated.type_decls.reserve_slot())
                    }
                    TransItemSource::Global(_) => {
                        AnyTransId::Global(self.translated.global_decls.reserve_slot())
                    }
                    TransItemSource::Fun(..) => {
                        AnyTransId::Fun(self.translated.fun_decls.reserve_slot())
                    }
                };
                // Add the id to the queue of declarations to translate
                self.id_map.insert(id.clone(), trans_id);
                self.reverse_id_map.insert(trans_id, id.clone());
                trans_id
            }
        };
        self.errors
            .borrow_mut()
            .register_dep_source(src, item_id, true);
        item_id
    }

    /// Register this id and enqueue it for translation.
    pub(crate) fn register_and_enqueue_id(
        &mut self,
        src: &Option<DepSource>,
        id: TransItemSource,
    ) -> AnyTransId {
        self.items_to_translate.insert(id.clone());
        self.register_id_no_enqueue(src, id)
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &ty::AdtDef,
        genargs: &ty::GenericArgs,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(
                src,
                TransItemSource::Type(id.clone(), genargs.clone().into()),
            )
            .as_type()
            .unwrap()
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: &mir::mono::Instance,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Fun(id.clone()))
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_closure_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        closure: &ty::ClosureDef,
        args: &ty::GenericArgs,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(
                src,
                TransItemSource::Closure(closure.clone(), args.clone().into()),
            )
            .as_type()
            .unwrap()
    }

    // pub(crate) fn register_global_decl_id(
    //     &mut self,
    //     src: &Option<DepSource>,
    //     id: &stable_mir::DefId,
    // ) -> GlobalDeclId {
    //     *self
    //         .register_and_enqueue_id(src, TransItemSource::Global(id.clone()))
    //         .as_global()
    //         .unwrap()
    // }
}

// Id and item reference registration.
impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub(crate) fn make_dep_source(&self, span: Span) -> Option<DepSource> {
        Some(DepSource {
            src_id: self.item_id?,
            span: Some(span),
        })
    }

    // pub(crate) fn register_id_no_enqueue(&mut self, span: Span, id: TransItemSource) -> AnyTransId {
    //     let src = self.make_dep_source(span);
    //     self.t_ctx.register_id_no_enqueue(&src, id)
    // }

    pub(crate) fn register_type_decl_id(
        &mut self,
        span: Span,
        id: &ty::AdtDef,
        genargs: &ty::GenericArgs,
    ) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_type_decl_id(&src, id, genargs)
    }

    /// Translate a type def id
    // pub(crate) fn translate_type_id(
    //     &mut self,
    //     span: Span,
    //     def_id: &ty::AdtDef,
    // ) -> Result<TypeId, Error> {
    //     Ok(TypeId::Adt(self.register_type_decl_id(span, def_id)))
    // }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        span: Span,
        id: &mir::mono::Instance,
    ) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_fun_decl_id(&src, id)
    }

    pub(crate) fn register_closure_type_decl_id(
        &mut self,
        span: Span,
        closure: &ty::ClosureDef,
        args: &ty::GenericArgs,
    ) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx
            .register_closure_type_decl_id(&src, closure, args)
    }

    // pub(crate) fn register_fun_decl_id_no_enqueue(
    //     &mut self,
    //     span: Span,
    //     id: &mir::mono::Instance,
    // ) -> FunDeclId {
    //     self.register_id_no_enqueue(span, TransItemSource::Fun(id.clone()))
    //         .as_fun()
    //         .copied()
    //         .unwrap()
    // }

    // /// Translate a function def id
    // pub(crate) fn translate_fun_id(
    //     &mut self,
    //     span: Span,
    //     instance: &mir::mono::Instance,
    // ) -> Result<FunId, Error> {
    //     Ok(FunId::Regular(self.register_fun_decl_id(span, instance)))
    // }

    // pub(crate) fn register_global_decl_id(
    //     &mut self,
    //     span: Span,
    //     id: &stable_mir::DefId,
    // ) -> GlobalDeclId {
    //     let src = self.make_dep_source(span);
    //     self.t_ctx.register_global_decl_id(&src, id)
    // }
}

pub fn translate<'tcx, 'ctx>(options: &CliOpts, tcx: TyCtxt<'tcx>) -> TransformCtx {
    // Retrieve the crate name: if the user specified a custom name, use it, otherwise retrieve it
    // from hax.
    let krate = stable_mir::local_crate();

    let mut error_ctx = ErrorCtx::new(!options.abort_on_error, options.error_on_warnings);
    let translate_options = TranslateOptions::new(&mut error_ctx, options);
    let mut ctx = TranslateCtx {
        tcx,
        options: translate_options,
        errors: RefCell::new(error_ctx),
        translated: TranslatedCrate {
            crate_name: krate.name,
            options: options.clone(),
            target_information: TargetInfo {
                target_pointer_size: tcx.data_layout.pointer_size().bytes(),
                is_little_endian: matches!(tcx.data_layout.endian, rustc_abi::Endian::Little),
            },
            ..TranslatedCrate::default()
        },
        id_map: Default::default(),
        reverse_id_map: Default::default(),
        file_to_id: Default::default(),
        items_to_translate: Default::default(),
        processed: Default::default(),
        cached_item_metas: Default::default(),
        cached_names: Default::default(),
        type_trans_cache: Default::default(),
    };

    let units = tcx.collect_and_partition_mono_items(()).codegen_units;
    units.iter().for_each(|unit| {
        unit.items_in_deterministic_order(tcx)
            .iter()
            .for_each(|(internal_item, _)| {
                let item = rustc_internal::stable(internal_item);
                match item {
                    mir::mono::MonoItem::Fn(instance) => {
                        ctx.register_fun_decl_id(&None, &instance);
                    }
                    mir::mono::MonoItem::GlobalAsm(_) => {}
                    mir::mono::MonoItem::Static(_) => {}
                }
            })
    });

    // Translate.
    //
    // For as long as the queue of items to translate is not empty, we pop the top item and
    // translate it. If an item refers to non-translated (potentially external) items, we add them
    // to the queue.
    //
    // Note that the order in which we translate the definitions doesn't matter:
    // we never need to lookup a translated definition, and only use the map
    // from Rust ids to translated ids.
    while let Some(item_src) = ctx.items_to_translate.pop_first() {
        trace!("About to translate item: {:?}", item_src);
        if ctx.processed.insert(item_src.clone()) {
            ctx.translate_item(&item_src);
        }
    }

    // Return the context, dropping the hax state and rustc `tcx`.
    TransformCtx {
        options: ctx.options,
        translated: ctx.translated,
        errors: ctx.errors,
    }
}
