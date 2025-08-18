extern crate rustc_abi;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_smir;
extern crate stable_mir;

use crate::translate::my_gen_args::MyGenericArgs;
use obol_lib::args::CliOpts;

use super::translate_ctx::*;

use charon_lib::ast::*;
use charon_lib::errors::ErrorCtx;
use charon_lib::options::{CliOpts as CharonCliOpts, TranslateOptions};
use charon_lib::transform::TransformCtx;
use itertools::Itertools;
use log::trace;
use rustc_middle::ty::TyCtxt;
use rustc_smir::IndexedVal;
use stable_mir::mir::mono::Instance;
use stable_mir::rustc_internal::{self};
use stable_mir::{CrateDef, DefId};
use stable_mir::{mir, ty};
use std::cell::RefCell;
use std::fmt::Debug;
use std::hash::Hash;

/// The id of an untranslated item. Note that a given `DefId` may show up as multiple different
/// item sources, e.g. a constant will have both a `Global` version (for the constant itself) and a
/// `FunDecl` one (for its initializer function).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TransItemSource {
    Global(mir::mono::StaticDef),
    Fun(mir::mono::Instance),
    Type(ty::AdtDef, MyGenericArgs),
    Closure(ty::ClosureDef, MyGenericArgs),
    ClosureAsFn(ty::ClosureDef, MyGenericArgs),
    ForeignType(ty::ForeignDef),
}

impl TransItemSource {
    pub(crate) fn as_def_id(&self) -> DefId {
        match self {
            TransItemSource::Global(id) => id.0.clone(),
            TransItemSource::Fun(instance) => instance.def.def_id(),
            TransItemSource::Type(id, _) => id.0,
            TransItemSource::Closure(def, _) => def.def_id(),
            TransItemSource::ClosureAsFn(def, _) => def.def_id(),
            TransItemSource::ForeignType(def) => def.def_id(),
        }
    }

    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord + Debug {
        fn key(k: &mir::mono::InstanceKind) -> isize {
            match k {
                mir::mono::InstanceKind::Intrinsic => 0,
                mir::mono::InstanceKind::Item => 1,
                mir::mono::InstanceKind::Shim => 2,
                mir::mono::InstanceKind::Virtual { idx } => 3 + (*idx as isize),
            }
        }

        match self {
            TransItemSource::Global(id) => (0, id.0.to_index(), 0),
            TransItemSource::Fun(instance) => (1, instance.def.to_index(), key(&instance.kind)),
            TransItemSource::Type(id, gargs) => (2, id.0.to_index(), gargs.sort_key()),
            TransItemSource::Closure(def, gargs) => (3, def.def_id().to_index(), gargs.sort_key()),
            TransItemSource::ClosureAsFn(def, gargs) => {
                (4, def.def_id().to_index(), gargs.sort_key())
            }
            TransItemSource::ForeignType(def) => (5, def.def_id().to_index(), 0),
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
                    TransItemSource::Type(..)
                    | TransItemSource::Closure(..)
                    | TransItemSource::ForeignType(..) => {
                        AnyTransId::Type(self.translated.type_decls.reserve_slot())
                    }
                    TransItemSource::Global(_) => {
                        AnyTransId::Global(self.translated.global_decls.reserve_slot())
                    }
                    TransItemSource::Fun(..) | TransItemSource::ClosureAsFn(..) => {
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
        id: ty::AdtDef,
        genargs: ty::GenericArgs,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Type(id, genargs.into()))
            .as_type()
            .unwrap()
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        id: mir::mono::Instance,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Fun(id))
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_closure_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        closure: ty::ClosureDef,
        args: ty::GenericArgs,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Closure(closure, args.into()))
            .as_type()
            .unwrap()
    }

    pub(crate) fn register_closure_as_fn_id(
        &mut self,
        src: &Option<DepSource>,
        closure: ty::ClosureDef,
        args: ty::GenericArgs,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::ClosureAsFn(closure, args.into()))
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        stt: mir::mono::StaticDef,
    ) -> GlobalDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::Global(stt))
            .as_global()
            .unwrap()
    }

    pub(crate) fn register_foreign_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def: ty::ForeignDef,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(src, TransItemSource::ForeignType(def))
            .as_type()
            .unwrap()
    }
}

// Id and item reference registration.
impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub(crate) fn make_dep_source(&self, span: Span) -> Option<DepSource> {
        Some(DepSource {
            src_id: self.item_id?,
            span: Some(span),
        })
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        span: Span,
        id: ty::AdtDef,
        genargs: ty::GenericArgs,
    ) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_type_decl_id(&src, id, genargs)
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        span: Span,
        id: mir::mono::Instance,
    ) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_fun_decl_id(&src, id)
    }

    pub(crate) fn register_closure_type_decl_id(
        &mut self,
        span: Span,
        closure: ty::ClosureDef,
        args: ty::GenericArgs,
    ) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx
            .register_closure_type_decl_id(&src, closure, args)
    }

    pub(crate) fn register_closure_as_fn_id(
        &mut self,
        span: Span,
        closure: ty::ClosureDef,
        args: ty::GenericArgs,
    ) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_closure_as_fn_id(&src, closure, args)
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        span: Span,
        stt: mir::mono::StaticDef,
    ) -> GlobalDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_global_decl_id(&src, stt)
    }

    pub(crate) fn register_foreign_type_decl_id(
        &mut self,
        span: Span,
        def: ty::ForeignDef,
    ) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_foreign_type_decl_id(&src, def)
    }
}

fn collect_entrypoints<'tcx>(options: &CliOpts, tcx: TyCtxt<'tcx>) -> Vec<Instance> {
    stable_mir::all_local_items()
        .iter()
        .filter_map(|item| {
            let Ok(instance) = Instance::try_from(*item) else {
                return None;
            };
            let int_def_id = rustc_internal::internal(tcx, instance.def.def_id());
            if matches!(tcx.def_kind(int_def_id), rustc_hir::def::DefKind::GlobalAsm) {
                return None;
            }
            // Only collect monomorphic items.
            if !matches!(item.kind(), stable_mir::ItemKind::Fn) {
                return None;
            }

            let instance_name = instance.name();
            let name_split = instance_name.split("::").last().unwrap();
            if options.entry_names.contains(&name_split.to_string()) {
                return Some(instance);
            }

            let def_id = stable_mir::rustc_internal::internal(tcx, instance.def.def_id());
            let attrib_match = tcx.get_all_attrs(def_id).any(|a| match a {
                rustc_hir::Attribute::Parsed(..) => false,
                rustc_hir::Attribute::Unparsed(attr) => {
                    let path = attr.path.segments.iter().map(|i| i.to_string()).join("::");
                    options.entry_attribs.contains(&path)
                }
            });

            attrib_match.then_some(instance)
        })
        .collect()
}

pub fn translate<'tcx, 'ctx>(options: &CliOpts, tcx: TyCtxt<'tcx>) -> TransformCtx {
    // Retrieve the crate name: if the user specified a custom name, use it, otherwise retrieve it
    // from hax.
    let krate = stable_mir::local_crate();

    let charon_opts = CharonCliOpts::default();
    let mut error_ctx = ErrorCtx::new(!charon_opts.abort_on_error, charon_opts.error_on_warnings);
    let translate_options = TranslateOptions::new(&mut error_ctx, &charon_opts);
    let mut ctx = TranslateCtx {
        tcx,
        options: translate_options,
        errors: RefCell::new(error_ctx),
        translated: TranslatedCrate {
            crate_name: krate.name,
            options: charon_opts.clone(),
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

    let units = collect_entrypoints(options, tcx);
    units
        .into_iter()
        .sorted_by_key(|i| i.def.def_id().to_index())
        .for_each(|instance| {
            ctx.register_fun_decl_id(&None, instance);
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
