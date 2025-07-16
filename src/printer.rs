extern crate rustc_middle;
extern crate rustc_monomorphize;
extern crate rustc_session;
extern crate rustc_smir;
extern crate rustc_span;
extern crate stable_mir;
// HACK: typically, we would source serde/serde_json separately from the compiler
//       However, due to issues matching crate versions when we have our own serde
//       in addition to the rustc serde, we force ourselves to use rustc serde
extern crate serde;
extern crate serde_json;
use charon_lib::{export::CrateData, transform::Pass};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::{OutFileName, OutputType};

use crate::translate::translate_crate::translate;

// Structs for serializing extra details about mono items
// ======================================================

// #[derive(Serialize, Clone)]
// struct BodyDetails {
//     pp: String,
// }

// fn get_body_details(body: &Body) -> BodyDetails {
//     let mut v = Vec::new();
//     let _ = body.dump(&mut v, "<omitted>");
//     BodyDetails {
//         pp: str::from_utf8(&v).unwrap().into(),
//     }
// }

// #[derive(Serialize, Clone)]
// struct GenericData(Vec<(String, String)>); // Alternatively, GenericData<'a>(Vec<(&'a Generics,GenericPredicates<'a>)>);

// fn generic_data(tcx: TyCtxt<'_>, id: DefId) -> GenericData {
//     let mut v = Vec::new();
//     let mut next_id = Some(id);
//     while let Some(curr_id) = next_id {
//         let params = tcx.generics_of(curr_id);
//         let preds = tcx.predicates_of(curr_id);
//         if params.parent != preds.parent {
//             panic!("Generics and predicates parent ids are distinct");
//         }
//         v.push((format!("{:#?}", params), format!("{:#?}", preds)));
//         next_id = params.parent;
//     }
//     v.reverse();
//     GenericData(v)
// }

// #[derive(Serialize, Clone)]
// struct ItemDetails {
//     // these fields only defined for fn items
//     fn_instance_kind: Option<InstanceKind>,
//     fn_item_kind: Option<ItemKind>,
//     fn_body_details: Option<BodyDetails>,
//     // these fields defined for all items
//     internal_kind: String,
//     path: String,
//     internal_ty: String,
//     generic_data: GenericData,
// }

// // unwrap early binder in a default manner; panic on error
// fn default_unwrap_early_binder<'tcx, T>(tcx: TyCtxt<'tcx>, id: DefId, v: EarlyBinder<'tcx, T>) -> T
// where
//     T: TypeFoldable<TyCtxt<'tcx>>,
// {
//     let v_copy = v.clone();
//     let body = tcx.optimized_mir(id);
//     match tcx.try_instantiate_and_normalize_erasing_regions(
//         GenericArgs::identity_for_item(tcx, id),
//         body.typing_env(tcx),
//         v,
//     ) {
//         Ok(res) => res,
//         Err(err) => {
//             println!("{:?}", err);
//             v_copy.skip_binder()
//         }
//     }
// }

// fn print_type<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, ty: EarlyBinder<'tcx, Ty<'tcx>>) -> String {
//     // lookup type kind in order to perform case analysis
//     let kind: &middle::ty::TyKind = ty.skip_binder().kind();
//     if let middle::ty::TyKind::FnDef(fun_id, args) = kind {
//         // since FnDef doesn't contain signature, lookup actual function type
//         // via getting fn signature with parameters and resolving those parameters
//         let sig0 = tcx.fn_sig(fun_id);
//         let body = tcx.optimized_mir(id);
//         let sig1 = match tcx.try_instantiate_and_normalize_erasing_regions(
//             args,
//             body.typing_env(tcx),
//             sig0,
//         ) {
//             Ok(res) => res,
//             Err(err) => {
//                 println!("{:?}", err);
//                 sig0.skip_binder()
//             }
//         };
//         let sig2: FnSig<'_> = tcx.instantiate_bound_regions_with_erased(sig1);
//         format!("\nTyKind(FnDef): {:#?}", sig2)
//     } else {
//         let kind = default_unwrap_early_binder(tcx, id, ty);
//         format!("\nTyKind: {:#?}", kind)
//     }
// }

// fn get_item_details(tcx: TyCtxt<'_>, id: DefId, fn_inst: Option<Instance>) -> Option<ItemDetails> {
//     if debug_enabled() {
//         Some(ItemDetails {
//             fn_instance_kind: fn_inst.map(|i| i.kind),
//             fn_item_kind: fn_inst
//                 .and_then(|i| CrateItem::try_from(i).ok())
//                 .map(|i| i.kind()),
//             fn_body_details: if let Some(fn_inst) = fn_inst {
//                 fn_inst.body().map(|body| get_body_details(&body))
//             } else {
//                 None
//             },
//             internal_kind: format!("{:#?}", tcx.def_kind(id)),
//             path: tcx.def_path_str(id), // NOTE: underlying data from tcx.def_path(id);
//             internal_ty: print_type(tcx, id, tcx.type_of(id)),
//             generic_data: generic_data(tcx, id),
//             // TODO: let layout = tcx.layout_of(id);
//         })
//     } else {
//         None
//     }
// }

// #[derive(Serialize)]
// struct ForeignItem {
//     name: String,
//     kind: ForeignItemKind,
// }
// #[derive(Serialize)]
// struct ForeignModule {
//     name: String,
//     items: Vec<ForeignItem>,
// }

// fn get_foreign_module_details() -> Vec<(String, Vec<ForeignModule>)> {
//     let mut crates = vec![stable_mir::local_crate()];
//     crates.append(&mut stable_mir::external_crates());
//     crates
//         .into_iter()
//         .map(|krate| {
//             (
//                 krate.name.clone(),
//                 krate
//                     .foreign_modules()
//                     .into_iter()
//                     .map(|mod_def| {
//                         let fmod = mod_def.module();
//                         ForeignModule {
//                             name: mod_def.name(),
//                             items: fmod
//                                 .items()
//                                 .into_iter()
//                                 .map(|def| ForeignItem {
//                                     name: def.name(),
//                                     kind: def.kind(),
//                                 })
//                                 .collect(),
//                         }
//                     })
//                     .collect::<Vec<_>>(),
//             )
//         })
//         .collect()
// }

// // Miscellaneous helper functions
// // ==============================

// macro_rules! def_env_var {
//     ($fn_name:ident, $var_name:ident) => {
//         fn $fn_name() -> bool {
//             use std::sync::OnceLock;
//             static VAR: OnceLock<bool> = OnceLock::new();
//             *VAR.get_or_init(|| std::env::var(stringify!($var_name)).is_ok())
//         }
//     };
// }

// def_env_var!(debug_enabled, DEBUG);
// def_env_var!(link_items_enabled, LINK_ITEMS);
// def_env_var!(link_instance_enabled, LINK_INST);

// // Possible input: sym::test
// pub fn has_attr(tcx: TyCtxt<'_>, item: &stable_mir::CrateItem, attr: symbol::Symbol) -> bool {
//     tcx.has_attr(rustc_internal::internal(tcx, item), attr)
// }

// fn mono_item_name(tcx: TyCtxt<'_>, item: &MonoItem) -> String {
//     if let MonoItem::GlobalAsm(data) = item {
//         hash(data).to_string()
//     } else {
//         mono_item_name_int(tcx, &rustc_internal::internal(tcx, item))
//     }
// }

// fn mono_item_name_int<'a>(tcx: TyCtxt<'a>, item: &rustc_middle::mir::mono::MonoItem<'a>) -> String {
//     item.symbol_name(tcx).name.into()
// }

// fn fn_inst_for_ty(ty: stable_mir::ty::Ty, direct_call: bool) -> Option<Instance> {
//     ty.kind().fn_def().and_then(|(fn_def, args)| {
//         if direct_call {
//             Instance::resolve(fn_def, args)
//         } else {
//             Instance::resolve_for_fn_ptr(fn_def, args)
//         }
//         .ok()
//     })
// }

// fn def_id_to_inst(tcx: TyCtxt<'_>, id: stable_mir::DefId) -> Instance {
//     let internal_id = rustc_internal::internal(tcx, id);
//     let internal_inst = rustc_middle::ty::Instance::mono(tcx, internal_id);
//     rustc_internal::stable(internal_inst)
// }

// fn take_any<K: Clone + std::hash::Hash + std::cmp::Eq, V>(
//     map: &mut HashMap<K, V>,
// ) -> Option<(K, V)> {
//     let key = map.keys().next()?.clone();
//     map.remove(&key).map(|val| (key, val))
// }

// fn hash<T: std::hash::Hash>(obj: T) -> u64 {
//     use std::hash::Hasher;
//     let mut hasher = std::hash::DefaultHasher::new();
//     obj.hash(&mut hasher);
//     hasher.finish()
// }

// // Structs for serializing critical details about mono items
// // =========================================================

// #[derive(Serialize, Clone)]
// pub enum MonoItemKind {
//     MonoItemFn {
//         name: String,
//         id: stable_mir::DefId,
//         body: Option<Body>,
//     },
//     MonoItemStatic {
//         name: String,
//         id: stable_mir::DefId,
//         allocation: Option<Allocation>,
//     },
//     MonoItemGlobalAsm {
//         asm: String,
//     },
// }
// #[derive(Serialize, Clone)]
// pub struct Item {
//     #[serde(skip)]
//     mono_item: MonoItem,
//     pub symbol_name: String,
//     pub mono_item_kind: MonoItemKind,
//     details: Option<ItemDetails>,
// }

// impl PartialEq for Item {
//     fn eq(&self, other: &Item) -> bool {
//         self.mono_item.eq(&other.mono_item)
//     }
// }
// impl Eq for Item {}

// impl PartialOrd for Item {
//     fn partial_cmp(&self, other: &Item) -> Option<std::cmp::Ordering> {
//         Some(self.cmp(other))
//     }
// }

// impl Ord for Item {
//     fn cmp(&self, other: &Item) -> std::cmp::Ordering {
//         use MonoItemKind::*;
//         let sort_key = |i: &Item| {
//             format!(
//                 "{}!{}",
//                 i.symbol_name,
//                 match &i.mono_item_kind {
//                     MonoItemFn {
//                         name,
//                         id: _,
//                         body: _,
//                     } => name,
//                     MonoItemStatic {
//                         name,
//                         id: _,
//                         allocation: _,
//                     } => name,
//                     MonoItemGlobalAsm { asm } => asm,
//                 }
//             )
//         };
//         sort_key(self).cmp(&sort_key(other))
//     }
// }

// fn mk_item(tcx: TyCtxt<'_>, item: MonoItem, sym_name: String) -> Item {
//     match item {
//         MonoItem::Fn(inst) => {
//             let id = inst.def.def_id();
//             let name = inst.name();
//             let internal_id = rustc_internal::internal(tcx, id);
//             Item {
//                 mono_item: item,
//                 symbol_name: sym_name.clone(),
//                 mono_item_kind: MonoItemKind::MonoItemFn {
//                     name: name.clone(),
//                     id,
//                     body: inst.body(),
//                 },
//                 details: get_item_details(tcx, internal_id, Some(inst)),
//             }
//         }
//         MonoItem::Static(static_def) => {
//             let internal_id = rustc_internal::internal(tcx, static_def.def_id());
//             let alloc = match static_def.eval_initializer() {
//                 Ok(alloc) => Some(alloc),
//                 err => {
//                     println!(
//                         "StaticDef({:#?}).eval_initializer() failed with: {:#?}",
//                         static_def, err
//                     );
//                     None
//                 }
//             };
//             Item {
//                 mono_item: item,
//                 symbol_name: sym_name,
//                 mono_item_kind: MonoItemKind::MonoItemStatic {
//                     name: static_def.name(),
//                     id: static_def.def_id(),
//                     allocation: alloc,
//                 },
//                 details: get_item_details(tcx, internal_id, None),
//             }
//         }
//         MonoItem::GlobalAsm(ref asm) => {
//             let asm = format!("{:#?}", asm);
//             Item {
//                 mono_item: item,
//                 symbol_name: sym_name,
//                 mono_item_kind: MonoItemKind::MonoItemGlobalAsm { asm },
//                 details: None,
//             }
//         }
//     }
// }

// // Link-time resolution logic
// // ==========================

// #[derive(Debug, Clone, Serialize, PartialEq, Eq)]
// pub enum FnSymType {
//     NoOpSym(String),
//     IntrinsicSym(String),
//     NormalSym(String),
// }

// type FnSymInfo<'tcx> = (
//     stable_mir::ty::Ty,
//     middle::ty::InstanceKind<'tcx>,
//     FnSymType,
// );

// fn fn_inst_sym<'tcx>(
//     tcx: TyCtxt<'tcx>,
//     ty: Option<stable_mir::ty::Ty>,
//     inst: Option<&Instance>,
// ) -> Option<FnSymInfo<'tcx>> {
//     use FnSymType::*;
//     inst.and_then(|inst| {
//         let ty = if let Some(ty) = ty { ty } else { inst.ty() };
//         let kind = ty.kind();
//         if kind.fn_def().is_some() {
//             let internal_inst = rustc_internal::internal(tcx, inst);
//             let sym_type = if inst.is_empty_shim() {
//                 NoOpSym(String::from(""))
//             } else if let Some(intrinsic_name) = inst.intrinsic_name() {
//                 IntrinsicSym(intrinsic_name)
//             } else {
//                 NormalSym(inst.mangled_name())
//             };
//             Some((ty, internal_inst.def, sym_type))
//         } else {
//             None
//         }
//     })
// }

// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
// pub struct LinkMapKey<'tcx>(
//     pub stable_mir::ty::Ty,
//     Option<middle::ty::InstanceKind<'tcx>>,
// );

// impl Serialize for LinkMapKey<'_> {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//     where
//         S: Serializer,
//     {
//         use serde::ser::SerializeTuple;
//         if link_instance_enabled() {
//             let mut tup = serializer.serialize_tuple(2)?;
//             tup.serialize_element(&self.0)?;
//             tup.serialize_element(&format!("{:?}", self.1).as_str())?;
//             tup.end()
//         } else {
//             <stable_mir::ty::Ty as Serialize>::serialize(&self.0, serializer)
//         }
//     }
// }

// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
// struct ItemSource(u8);
// const ITEM: u8 = 1 << 0;
// const TERM: u8 = 1 << 1;
// const FPTR: u8 = 1 << 2;

// impl Serialize for ItemSource {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//     where
//         S: Serializer,
//     {
//         use serde::ser::SerializeSeq;
//         let mut seq = serializer.serialize_seq(None)?;
//         if self.0 & ITEM != 0u8 {
//             seq.serialize_element(&"Item")?
//         };
//         if self.0 & TERM != 0u8 {
//             seq.serialize_element(&"Term")?
//         };
//         if self.0 & FPTR != 0u8 {
//             seq.serialize_element(&"Fptr")?
//         };
//         seq.end()
//     }
// }

// #[derive(Serialize)]
// pub enum AllocInfo {
//     Function(stable_mir::mir::mono::Instance),
//     VTable(
//         stable_mir::ty::Ty,
//         Option<stable_mir::ty::Binder<stable_mir::ty::ExistentialTraitRef>>,
//     ),
//     Static(stable_mir::mir::mono::StaticDef),
//     Memory(stable_mir::ty::Allocation), // TODO include stable_mir::ty::TyKind?
// }
// type LinkMap<'tcx> = HashMap<LinkMapKey<'tcx>, (ItemSource, FnSymType)>;
// type AllocMap = HashMap<stable_mir::mir::alloc::AllocId, AllocInfo>;
// type TyMap =
//     HashMap<stable_mir::ty::Ty, (stable_mir::ty::TyKind, Option<stable_mir::abi::LayoutShape>)>;
// type SpanMap = HashMap<usize, (String, usize, usize, usize, usize)>;

// struct TyCollector<'tcx> {
//     tcx: TyCtxt<'tcx>,
//     types: TyMap,
//     resolved: HashSet<stable_mir::ty::Ty>,
// }

// impl TyCollector<'_> {
//     fn new(tcx: TyCtxt<'_>) -> TyCollector {
//         TyCollector {
//             tcx,
//             types: HashMap::new(),
//             resolved: HashSet::new(),
//         }
//     }
// }

// impl TyCollector<'_> {
//     #[inline(always)]
//     fn visit_instance(&mut self, instance: Instance) -> ControlFlow<<Self as Visitor>::Break> {
//         let fn_abi = instance.fn_abi().unwrap();
//         let mut inputs_outputs: Vec<stable_mir::ty::Ty> =
//             fn_abi.args.iter().map(|arg_abi| arg_abi.ty).collect();
//         inputs_outputs.push(fn_abi.ret.ty);
//         inputs_outputs.super_visit(self)
//     }
// }

// impl Visitor for TyCollector<'_> {
//     type Break = ();

//     fn visit_ty(&mut self, ty: &stable_mir::ty::Ty) -> ControlFlow<Self::Break> {
//         if self.types.contains_key(ty) || self.resolved.contains(ty) {
//             return ControlFlow::Continue(());
//         }

//         match ty.kind() {
//             TyKind::RigidTy(RigidTy::Closure(def, ref args)) => {
//                 self.resolved.insert(*ty);
//                 let instance =
//                     Instance::resolve_closure(def, args, stable_mir::ty::ClosureKind::Fn).unwrap();
//                 self.visit_instance(instance)
//             }
//             // Break on CoroutineWitnesses, because they aren't expected when getting the layout
//             TyKind::RigidTy(RigidTy::CoroutineWitness(..)) => ControlFlow::Break(()),
//             TyKind::RigidTy(RigidTy::FnDef(def, ref args)) => {
//                 self.resolved.insert(*ty);
//                 let instance = Instance::resolve(def, args).unwrap();
//                 self.visit_instance(instance)
//             }
//             TyKind::RigidTy(RigidTy::FnPtr(binder_stable)) => {
//                 self.resolved.insert(*ty);
//                 let binder_internal = internal(self.tcx, binder_stable);
//                 let sig_stable = rustc_internal::stable(
//                     self.tcx
//                         .fn_abi_of_fn_ptr(
//                             TypingEnv::fully_monomorphized()
//                                 .as_query_input((binder_internal, List::empty())),
//                         )
//                         .unwrap(),
//                 );
//                 let mut inputs_outputs: Vec<stable_mir::ty::Ty> =
//                     sig_stable.args.iter().map(|arg_abi| arg_abi.ty).collect();
//                 inputs_outputs.push(sig_stable.ret.ty);
//                 inputs_outputs.super_visit(self)
//             }
//             _ => {
//                 let control = ty.super_visit(self);
//                 match control {
//                     ControlFlow::Continue(_) => {
//                         let maybe_layout_shape = ty.layout().ok().map(|layout| layout.shape());
//                         self.types.insert(*ty, (ty.kind(), maybe_layout_shape));
//                         control
//                     }
//                     _ => control,
//                 }
//             }
//         }
//     }
// }

// struct InternedValueCollector<'tcx, 'local> {
//     tcx: TyCtxt<'tcx>,
//     _sym: String,
//     locals: &'local [LocalDecl],
//     link_map: &'local mut LinkMap<'tcx>,
//     visited_allocs: &'local mut AllocMap,
//     ty_visitor: &'local mut TyCollector<'tcx>,
//     spans: &'local mut SpanMap,
// }

// type InternedValues<'tcx> = (LinkMap<'tcx>, AllocMap, TyMap, SpanMap);

// fn update_link_map<'tcx>(
//     link_map: &mut LinkMap<'tcx>,
//     fn_sym: Option<FnSymInfo<'tcx>>,
//     source: ItemSource,
// ) {
//     if fn_sym.is_none() {
//         return;
//     }
//     let (ty, kind, name) = fn_sym.unwrap();
//     let new_val = (source, name);
//     let key = if link_instance_enabled() {
//         LinkMapKey(ty, Some(kind))
//     } else {
//         LinkMapKey(ty, None)
//     };
//     if let Some(curr_val) = link_map.get_mut(&key.clone()) {
//         if curr_val.1 != new_val.1 {
//             panic!(
//                 "Added inconsistent entries into link map! {:?} -> {:?}, {:?}",
//                 (ty, ty.kind().fn_def(), &kind),
//                 curr_val.1,
//                 new_val.1
//             );
//         }
//         curr_val.0.0 |= new_val.0.0;
//         if debug_enabled() {
//             println!(
//                 "Regenerated link map entry: {:?}:{:?} -> {:?}",
//                 &key,
//                 key.0.kind().fn_def(),
//                 new_val
//             );
//         }
//     } else {
//         if debug_enabled() {
//             println!(
//                 "Generated link map entry from call: {:?}:{:?} -> {:?}",
//                 &key,
//                 key.0.kind().fn_def(),
//                 new_val
//             );
//         }
//         link_map.insert(key.clone(), new_val);
//     }
// }

// fn get_prov_type(maybe_kind: Option<stable_mir::ty::TyKind>) -> Option<stable_mir::ty::TyKind> {
//     use stable_mir::ty::RigidTy;
//     // check for pointers
//     let kind = maybe_kind?;
//     if let Some(ty) = kind.builtin_deref(true) {
//         return ty.ty.kind().into();
//     }
//     match kind.rigid().expect("Non-rigid-ty allocation found!") {
//         RigidTy::Array(ty, _) | RigidTy::Slice(ty) | RigidTy::Ref(_, ty, _) => ty.kind().into(),
//         RigidTy::FnPtr(_) | RigidTy::Adt(..) => None, // TODO: Check for Adt if the GenericArgs are related to prov
//         unimplemented => {
//             todo!("Unimplemented RigidTy allocation: {:?}", unimplemented);
//         }
//     }
// }

// fn collect_alloc(
//     val_collector: &mut InternedValueCollector,
//     kind: Option<stable_mir::ty::TyKind>,
//     val: stable_mir::mir::alloc::AllocId,
// ) {
//     use stable_mir::mir::alloc::GlobalAlloc;
//     let entry = val_collector.visited_allocs.entry(val);
//     if matches!(entry, std::collections::hash_map::Entry::Occupied(_)) {
//         return;
//     }
//     let global_alloc = GlobalAlloc::from(val);
//     match global_alloc {
//         GlobalAlloc::Memory(ref alloc) => {
//             let pointed_kind = get_prov_type(kind);
//             if debug_enabled() {
//                 println!(
//                     "DEBUG: called collect_alloc: {:?}:{:?}:{:?}",
//                     val, pointed_kind, global_alloc
//                 );
//             }
//             entry.or_insert(AllocInfo::Memory(alloc.clone())); // TODO: include pointed_kind.clone().unwrap() ?
//             alloc.provenance.ptrs.iter().for_each(|(_, prov)| {
//                 collect_alloc(val_collector, pointed_kind.clone(), prov.0);
//             });
//         }
//         GlobalAlloc::Static(def) => {
//             assert!(
//                 kind.clone().unwrap().builtin_deref(true).is_some(),
//                 "Allocated pointer is not a built-in pointer type: {:?}",
//                 kind
//             );
//             entry.or_insert(AllocInfo::Static(def));
//         }
//         GlobalAlloc::VTable(ty, traitref) => {
//             assert!(
//                 kind.clone().unwrap().builtin_deref(true).is_some(),
//                 "Allocated pointer is not a built-in pointer type: {:?}",
//                 kind
//             );
//             entry.or_insert(AllocInfo::VTable(ty, traitref));
//         }
//         GlobalAlloc::Function(inst) => {
//             assert!(kind.unwrap().is_fn_ptr());
//             entry.or_insert(AllocInfo::Function(inst));
//         }
//     };
// }

// impl MirVisitor for InternedValueCollector<'_, '_> {
//     fn visit_span(&mut self, span: &stable_mir::ty::Span) {
//         let span_internal = internal(self.tcx, span);
//         let (source_file, lo_line, lo_col, hi_line, hi_col) = self
//             .tcx
//             .sess
//             .source_map()
//             .span_to_location_info(span_internal);
//         let file_name = match source_file {
//             Some(sf) => sf
//                 .name
//                 .display(rustc_span::FileNameDisplayPreference::Remapped)
//                 .to_string(),
//             None => "no-location".to_string(),
//         };
//         self.spans.insert(
//             span.to_index(),
//             (file_name, lo_line, lo_col, hi_line, hi_col),
//         );
//     }

//     fn visit_terminator(&mut self, term: &Terminator, loc: stable_mir::mir::visit::Location) {
//         use TerminatorKind::*;
//         use stable_mir::mir::{ConstOperand, Operand::Constant};
//         let fn_sym = match &term.kind {
//             Call {
//                 func: Constant(ConstOperand { const_: cnst, .. }),
//                 args: _,
//                 ..
//             } => {
//                 if *cnst.kind() != stable_mir::ty::ConstantKind::ZeroSized {
//                     return;
//                 }
//                 let inst = fn_inst_for_ty(cnst.ty(), true)
//                     .expect("Direct calls to functions must resolve to an instance");
//                 fn_inst_sym(self.tcx, Some(cnst.ty()), Some(&inst))
//             }
//             Drop { place, .. } => {
//                 let drop_ty = place.ty(self.locals).unwrap();
//                 let inst = Instance::resolve_drop_in_place(drop_ty);
//                 fn_inst_sym(self.tcx, None, Some(&inst))
//             }
//             _ => None,
//         };
//         update_link_map(self.link_map, fn_sym, ItemSource(TERM));
//         self.super_terminator(term, loc);
//     }

//     fn visit_rvalue(&mut self, rval: &Rvalue, loc: stable_mir::mir::visit::Location) {
//         use stable_mir::mir::{CastKind, PointerCoercion};

//         #[allow(clippy::single_match)] // TODO: Unsure if we need to fill these out
//         match rval {
//             Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer), op, _) => {
//                 let inst = fn_inst_for_ty(op.ty(self.locals).unwrap(), false)
//                     .expect("ReifyFnPointer Cast operand type does not resolve to an instance");
//                 let fn_sym = fn_inst_sym(self.tcx, None, Some(&inst));
//                 update_link_map(self.link_map, fn_sym, ItemSource(FPTR));
//             }
//             _ => {}
//         };
//         self.super_rvalue(rval, loc);
//     }

//     fn visit_mir_const(
//         &mut self,
//         constant: &stable_mir::ty::MirConst,
//         loc: stable_mir::mir::visit::Location,
//     ) {
//         use stable_mir::ty::{ConstantKind, TyConstKind}; // TyConst
//         match constant.kind() {
//             ConstantKind::Allocated(alloc) => {
//                 if debug_enabled() {
//                     println!(
//                         "visited_mir_const::Allocated({:?}) as {:?}",
//                         alloc,
//                         constant.ty().kind()
//                     );
//                 }
//                 alloc.provenance.ptrs.iter().for_each(|(_offset, prov)| {
//                     collect_alloc(self, Some(constant.ty().kind()), prov.0)
//                 });
//             }
//             ConstantKind::Ty(ty_const) => {
//                 if let TyConstKind::Value(..) = ty_const.kind() {
//                     panic!("TyConstKind::Value");
//                 }
//             }
//             ConstantKind::Unevaluated(_) | ConstantKind::Param(_) | ConstantKind::ZeroSized => {}
//         }
//         self.super_mir_const(constant, loc);
//     }

//     fn visit_ty(&mut self, ty: &stable_mir::ty::Ty, _location: stable_mir::mir::visit::Location) {
//         let _ = ty.visit(self.ty_visitor);
//         self.super_ty(ty);
//     }
// }

// fn collect_interned_values<'tcx>(tcx: TyCtxt<'tcx>, items: Vec<&MonoItem>) -> InternedValues<'tcx> {
//     let mut calls_map = HashMap::new();
//     let mut visited_allocs = HashMap::new();
//     let mut ty_visitor = TyCollector::new(tcx);
//     let mut span_map = HashMap::new();
//     if link_items_enabled() {
//         for item in items.iter() {
//             if let MonoItem::Fn(inst) = item {
//                 update_link_map(
//                     &mut calls_map,
//                     fn_inst_sym(tcx, None, Some(inst)),
//                     ItemSource(ITEM),
//                 )
//             }
//         }
//     }
//     for item in items.iter() {
//         match &item {
//             MonoItem::Fn(inst) => {
//                 if let Some(body) = inst.body() {
//                     InternedValueCollector {
//                         tcx,
//                         _sym: inst.mangled_name(),
//                         locals: body.locals(),
//                         link_map: &mut calls_map,
//                         visited_allocs: &mut visited_allocs,
//                         ty_visitor: &mut ty_visitor,
//                         spans: &mut span_map,
//                     }
//                     .visit_body(&body)
//                 } else {
//                     eprintln!(
//                         "Failed to retrive body for Instance of MonoItem::Fn {}",
//                         inst.name()
//                     )
//                 }
//             }
//             MonoItem::Static(def) => {
//                 let inst = def_id_to_inst(tcx, def.def_id());
//                 if let Some(body) = inst.body() {
//                     InternedValueCollector {
//                         tcx,
//                         _sym: inst.mangled_name(),
//                         locals: &[],
//                         link_map: &mut calls_map,
//                         visited_allocs: &mut visited_allocs,
//                         ty_visitor: &mut ty_visitor,
//                         spans: &mut span_map,
//                     }
//                     .visit_body(&body)
//                 } else {
//                     eprintln!(
//                         "Failed to retrive body for Instance of MonoItem::Static {}",
//                         inst.name()
//                     )
//                 }
//             }
//             MonoItem::GlobalAsm(_) => {}
//         }
//     }
//     (calls_map, visited_allocs, ty_visitor.types, span_map)
// }

// // Collection Transitive Closure
// // =============================

// struct UnevaluatedConstCollector<'tcx, 'local> {
//     tcx: TyCtxt<'tcx>,
//     unevaluated_consts: &'local mut HashMap<stable_mir::ty::ConstDef, String>,
//     processed_items: &'local mut HashMap<String, Item>,
//     pending_items: &'local mut HashMap<String, Item>,
//     current_item: u64,
// }

// impl MirVisitor for UnevaluatedConstCollector<'_, '_> {
//     fn visit_mir_const(
//         &mut self,
//         constant: &stable_mir::ty::MirConst,
//         _location: stable_mir::mir::visit::Location,
//     ) {
//         if let stable_mir::ty::ConstantKind::Unevaluated(uconst) = constant.kind() {
//             let internal_def = rustc_internal::internal(self.tcx, uconst.def.def_id());
//             let internal_args = rustc_internal::internal(self.tcx, uconst.args.clone());
//             let maybe_inst = rustc_middle::ty::Instance::try_resolve(
//                 self.tcx,
//                 TypingEnv::post_analysis(self.tcx, internal_def),
//                 internal_def,
//                 internal_args,
//             );
//             let inst = maybe_inst
//                 .ok()
//                 .flatten()
//                 .unwrap_or_else(|| panic!("Failed to resolve mono item for {:?}", uconst));
//             let internal_mono_item = rustc_middle::mir::mono::MonoItem::Fn(inst);
//             let item_name = mono_item_name_int(self.tcx, &internal_mono_item);
//             if !(self.processed_items.contains_key(&item_name)
//                 || self.pending_items.contains_key(&item_name)
//                 || self.current_item == hash(&item_name))
//             {
//                 if debug_enabled() {
//                     println!("Adding unevaluated const body for: {}", item_name);
//                 }
//                 self.unevaluated_consts
//                     .insert(uconst.def, item_name.clone());
//                 self.pending_items.insert(
//                     item_name.clone(),
//                     mk_item(
//                         self.tcx,
//                         rustc_internal::stable(internal_mono_item),
//                         item_name,
//                     ),
//                 );
//             }
//         }
//     }
// }

// fn collect_unevaluated_constant_items(
//     tcx: TyCtxt<'_>,
//     items: HashMap<String, Item>,
// ) -> (HashMap<stable_mir::ty::ConstDef, String>, Vec<Item>) {
//     // setup collector prerequisites
//     let mut unevaluated_consts = HashMap::new();
//     let mut processed_items = HashMap::new();
//     let mut pending_items = items;

//     while let Some((curr_name, value)) = take_any(&mut pending_items) {
//         // skip item if it isn't a function
//         let body = match value.mono_item_kind {
//             MonoItemKind::MonoItemFn { ref body, .. } => body,
//             _ => continue,
//         };

//         // create new collector for function body
//         let mut collector = UnevaluatedConstCollector {
//             tcx,
//             unevaluated_consts: &mut unevaluated_consts,
//             processed_items: &mut processed_items,
//             pending_items: &mut pending_items,
//             current_item: hash(&curr_name),
//         };

//         if let Some(body) = body {
//             collector.visit_body(body);
//         }

//         // move processed item into seen items
//         processed_items.insert(curr_name.to_string(), value);
//     }

//     (
//         unevaluated_consts,
//         processed_items.drain().map(|(_name, item)| item).collect(),
//     )
// }

// // Core item collection logic
// // ==========================

// fn mono_collect(tcx: TyCtxt<'_>) -> Vec<MonoItem> {
//     let units = tcx.collect_and_partition_mono_items(()).codegen_units;
//     units
//         .iter()
//         .flat_map(|unit| {
//             unit.items_in_deterministic_order(tcx)
//                 .iter()
//                 .map(|(internal_item, _)| rustc_internal::stable(internal_item))
//                 .collect::<Vec<_>>()
//         })
//         .collect()
// }

// struct TranslationCtx<'tcx> {
//     ctx: TyCtxt<'tcx>,
//     type_id_map: HashMap<DefId, TypeDeclId>,
// }

// fn collect_items(tcx: TyCtxt<'_>) -> HashMap<String, Item> {
//     // get initial set of mono_items
//     let items = mono_collect(tcx);
//     items
//         .iter()
//         .map(|item| {
//             let name = mono_item_name(tcx, item);
//             (name.clone(), mk_item(tcx, item.clone(), name))
//         })
//         .collect::<HashMap<_, _>>()
// }

// // Type metadata required for execution

// #[derive(Serialize)]
// pub enum TypeMetadata {
//     PrimitiveType(RigidTy),
//     EnumType {
//         name: String,
//         adt_def: AdtDef,
//         discriminants: Vec<(VariantIdx, u128)>,
//     },
//     StructType {
//         name: String,
//         adt_def: AdtDef,
//         fields: Vec<stable_mir::ty::Ty>,
//     },
//     UnionType {
//         name: String,
//         adt_def: AdtDef,
//     },
//     ArrayType(stable_mir::ty::Ty, Option<stable_mir::ty::TyConst>),
//     PtrType(stable_mir::ty::Ty),
//     RefType(stable_mir::ty::Ty),
//     TupleType {
//         types: Vec<stable_mir::ty::Ty>,
//     },
//     FunType(String),
// }

// fn mk_type_metadata(
//     tcx: TyCtxt<'_>,
//     k: stable_mir::ty::Ty,
//     t: TyKind,
// ) -> Option<(stable_mir::ty::Ty, TypeMetadata)> {
//     use TyKind::RigidTy as T;
//     use TypeMetadata::*;
//     use stable_mir::ty::RigidTy::*;
//     match t {
//         T(prim_type) if t.is_primitive() => Some((k, PrimitiveType(prim_type))),
//         // for enums, we need a mapping of variantIdx to discriminant
//         // this requires access to the internals and is not provided as an interface function at the moment
//         T(Adt(adt_def, _)) if t.is_enum() => {
//             let adt_internal = rustc_internal::internal(tcx, adt_def);
//             let discriminants = adt_internal
//                 .discriminants(tcx)
//                 .map(|(v_idx, discr)| (rustc_internal::stable(v_idx), discr.val))
//                 .collect::<Vec<_>>();
//             let name = adt_def.name();
//             Some((
//                 k,
//                 EnumType {
//                     name,
//                     adt_def,
//                     discriminants,
//                 },
//             ))
//         }
//         // for structs, we record the name for information purposes and the field types
//         T(Adt(adt_def, _)) if t.is_struct() => {
//             let name = adt_def.name();
//             let fields = rustc_internal::internal(tcx, adt_def)
//                 .all_fields() // is_struct, so only one variant
//                 .map(move |field| tcx.type_of(field.did).instantiate_identity())
//                 .map(rustc_internal::stable)
//                 .collect();
//             Some((
//                 k,
//                 StructType {
//                     name,
//                     adt_def,
//                     fields,
//                 },
//             ))
//         }
//         // for unions, we only record the name
//         T(Adt(adt_def, _)) if t.is_union() => {
//             let name = adt_def.name();
//             Some((k, UnionType { name, adt_def }))
//         }
//         // encode str together with primitive types
//         T(Str) => Some((k, PrimitiveType(Str))),
//         // for arrays and slices, record element type and optional size
//         T(Array(ty, ty_const)) => Some((k, ArrayType(ty, Some(ty_const)))),
//         T(Slice(ty)) => Some((k, ArrayType(ty, None))),
//         // for raw pointers and references store the pointee type
//         T(RawPtr(ty, _)) => Some((k, PtrType(ty))),
//         T(Ref(_, ty, _)) => Some((k, RefType(ty))),
//         // for tuples the element types are provided
//         T(Tuple(tys)) => Some((k, TupleType { types: tys })),
//         // opaque function types (fun ptrs, closures, FnDef) are only provided to avoid dangling ty references
//         T(FnDef(_, _)) | T(FnPtr(_)) | T(Closure(_, _)) => Some((k, FunType(format!("{}", k)))),
//         // other types are not provided either
//         T(Foreign(_))
//         | T(Pat(_, _))
//         | T(Coroutine(_, _, _))
//         | T(Dynamic(_, _, _))
//         | T(CoroutineWitness(_, _)) => None,
//         TyKind::Alias(_, _) | TyKind::Param(_) | TyKind::Bound(_, _) => None,
//         _ => None, // redundant because of first 4 cases, but rustc does not understand that
//     }
// }
// type SourceData = (String, usize, usize, usize, usize);

// /// the serialised data structure as a whole
// #[derive(Serialize)]
// pub struct SmirJson<'t> {
//     pub name: String,
//     pub crate_id: u64,
//     pub allocs: Vec<(AllocId, AllocInfo)>,
//     pub functions: Vec<(LinkMapKey<'t>, FnSymType)>,
//     pub uneval_consts: Vec<(ConstDef, String)>,
//     pub items: Vec<Item>,
//     pub types: Vec<(stable_mir::ty::Ty, TypeMetadata)>,
//     pub spans: Vec<(usize, SourceData)>,
//     pub debug: Option<SmirJsonDebugInfo<'t>>,
//     pub machine: stable_mir::target::MachineInfo,
// }

// #[derive(Serialize)]
// pub struct SmirJsonDebugInfo<'t> {
//     fn_sources: Vec<(LinkMapKey<'t>, ItemSource)>,
//     types: TyMap,
//     foreign_modules: Vec<(String, Vec<ForeignModule>)>,
// }

// Serialization Entrypoint
// ========================

pub fn emit_smir(opts: &crate::args::CliOpts, tcx: TyCtxt<'_>) {
    let mut ctx = translate(&charon_lib::options::CliOpts::default(), tcx);
    use charon_lib::transform;
    let transforms: &[Pass] = &[
        Pass::NonBody(&transform::insert_storage_lives::Transform),
        Pass::NonBody(&transform::reorder_decls::Transform),
    ];
    for pass in transforms {
        pass.run(&mut ctx);
    }

    if opts.print_ullbc {
        println!("\n// Final ULLBC:\n\n{ctx}\n");
    }

    let path = opts.dest_file.clone().or_else(|| {
        if let OutFileName::Real(path) = tcx.output_filenames(()).path(OutputType::Mir) {
            Some(path.with_extension("ullbc"))
        } else {
            None
        }
    });

    if let Some(path) = path {
        let crate_data = CrateData::new(ctx);
        crate_data
            .serialize_to_file(&path)
            .expect("Failed to write smir.json to output")
    }
}
