/// Replaces MIR-level TypeId construction patterns with `ConstantExprKind::TypeId(T)`.
///
/// When smir evaluates a `TypeId::of::<T>()` or `<T as Any>::type_id()` call, it
/// produces a constant of the form `TypeId { data: [&raw const g, &raw const g] }` where
/// `g` is a zero-sized `GlobalAlloc::TypeId { ty: T }` marker alloc.  This pass finds those
/// constants and replaces them with the semantic `ConstantExprKind::TypeId(T)` before
/// `simplify_constants` desugars them into statement sequences.
use std::collections::HashMap;

use charon_lib::{
    ast::*,
    transform::{CowBox, TransformCtx, ctx::UllbcPass},
    ullbc_ast::ExprBody,
};

pub struct Transform {
    /// Maps each GlobalDeclId that represents a `GlobalAlloc::TypeId { ty: T }` marker to T.
    typeid_globals: HashMap<GlobalDeclId, Ty>,
}

impl Transform {
    pub fn new(ctx: &TransformCtx) -> CowBox<dyn UllbcPass> {
        // The `GlobalAlloc::TypeId` arm of `translate_global_alloc_value` stores the marker
        // directly as the global's value, so we just read it off.
        let typeid_globals = ctx
            .translated
            .global_decls
            .iter()
            .filter(|g| matches!(g.global_kind, GlobalKind::AnonConst))
            .filter_map(|g| match &g.value.kind {
                ConstantExprKind::TypeId(t) => Some((g.def_id, t.clone())),
                _ => None,
            })
            .collect();
        CowBox::Owned(Box::new(Transform { typeid_globals }))
    }
}

impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx, body: &mut ExprBody) {
        body.dyn_visit_in_body_mut(|cexpr: &mut ConstantExpr| {
            if let Some(t) = extract_typeid_ty(cexpr, &self.typeid_globals) {
                cexpr.kind = ConstantExprKind::TypeId(t);
            }
        });
    }

    fn finalize(&self, ctx: &mut TransformCtx) {
        for gid in self.typeid_globals.keys() {
            ctx.translated.global_decls.remove(*gid);
            // Also remove the init function for this global.
            // We have to find it through the global decl, but the global decl has already been
            // removed above. We instead remove all fun_decls whose is_global_initializer points
            // to one of our removed globals.
        }
        // Remove all init functions that initialised a now-deleted TypeId marker global.
        let init_ids_to_remove: Vec<FunDeclId> = ctx
            .translated
            .fun_decls
            .iter()
            .filter(|f| {
                f.is_global_initializer
                    .is_some_and(|gid| self.typeid_globals.contains_key(&gid))
            })
            .map(|f| f.def_id)
            .collect();
        for fid in init_ids_to_remove {
            ctx.translated.fun_decls.remove(fid);
        }
    }
}

/// If `cexpr` has the shape `TypeId { data: [&raw const g, &raw const g] }` where `g` is a
/// known TypeId marker global, returns the corresponding type T.
fn extract_typeid_ty(cexpr: &ConstantExpr, map: &HashMap<GlobalDeclId, Ty>) -> Option<Ty> {
    if let ConstantExprKind::Adt(None, fields) = &cexpr.kind
        && let [data_field] = fields.as_slice()
        && let ConstantExprKind::Array(ptrs) = &data_field.kind
        && let [ptr0, ptr1] = ptrs.as_slice()
        && let ConstantExprKind::Ptr(RefKind::Shared, inner0, None) = &ptr0.kind
        && let ConstantExprKind::Global(gref0) = &inner0.kind
        && let ConstantExprKind::Ptr(RefKind::Shared, inner1, None) = &ptr1.kind
        && let ConstantExprKind::Global(gref1) = &inner1.kind
        && gref0.id == gref1.id
    {
        map.get(&gref0.id).cloned()
    } else {
        None
    }
}
