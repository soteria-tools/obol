//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_public;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::{raise_error, register_error};
use rustc_public::{CrateDef, mir, rustc_internal};

pub(crate) fn is_named_const(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> bool {
    matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Const { .. } | rustc_hir::def::DefKind::AssocConst { .. }
    )
}

/// A MIR `MutVisitor` that evaluates every const operand to its value — exactly like
/// rustc_public's `BodyBuilder` does when producing a stable body — *except* references to named
/// const items, which it leaves as `Const::Unevaluated`. We keep those unevaluated so that
/// `translate_operand` can emit a reference to a `GlobalKind::NamedConst` global instead of
/// inlining the value.
struct NamedConstPreservingEvaluator<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
}

impl<'tcx> rustc_middle::mir::visit::MutVisitor<'tcx> for NamedConstPreservingEvaluator<'tcx> {
    fn tcx(&self) -> rustc_middle::ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_const_operand(
        &mut self,
        constant: &mut rustc_middle::mir::ConstOperand<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_
            && uneval.promoted.is_none()
            && is_named_const(self.tcx, uneval.def)
        {
            // Leave references to named const items unevaluated.
            return;
        }
        let const_ = constant.const_;
        match const_.eval(self.tcx, self.typing_env, constant.span) {
            Ok(val) => constant.const_ = rustc_middle::mir::Const::Val(val, const_.ty()),
            Err(rustc_middle::mir::interpret::ErrorHandled::Reported(..)) => {}
            Err(rustc_middle::mir::interpret::ErrorHandled::TooGeneric(..)) => {}
        }
        self.super_const_operand(constant, location);
    }
}

impl ItemTransCtx<'_, '_> {
    pub fn requires_caller_location(&self, instance: mir::mono::Instance) -> bool {
        let instance_internal = rustc_internal::internal(self.t_ctx.tcx, instance);
        instance_internal
            .def
            .requires_caller_location(self.t_ctx.tcx)
    }

    /// If this instance is a closure, meaning in MIR it has untupled arguments both in the
    /// signature and the body.
    pub fn instance_is_closure(&self, def: mir::mono::Instance) -> bool {
        let def = rustc_internal::internal(self.t_ctx.tcx, def.def.def_id());
        self.t_ctx.tcx.is_closure_like(def)
    }

    /// Translate a function's signature
    pub(crate) fn translate_function_signature(
        &mut self,
        def: mir::mono::Instance,
        span: Span,
    ) -> Result<FunSig, Error> {
        // CrateItem::try_from fails for Shim/Intrinsic/Virtual instances (which have no
        // CrateItem) and for InstanceKind::Item items that have no MIR body (e.g. extern
        // functions, constructors).  In all cases, skip the item-kind check and fall through
        // to fn_abi-based signature translation below.
        if let Ok(crate_item) = rustc_public::CrateItem::try_from(def) {
            match crate_item.kind() {
                rustc_public::ItemKind::Fn | rustc_public::ItemKind::Ctor(_) => {}
                rustc_public::ItemKind::Static => {
                    let stt: mir::mono::StaticDef = crate_item.try_into()?;
                    let output = self.translate_ty(span, stt.ty())?;
                    return Ok(FunSig {
                        is_unsafe: false,
                        abi: Abi::rust(),
                        inputs: vec![],
                        output,
                    });
                }
                kind => {
                    raise_error!(
                        self,
                        span,
                        "Unexpected item kind in translate signature: {kind:?}"
                    )
                }
            }
        }

        // Rust may add an implicit call location argument to the function, to improve error
        // tracking; this argument however doesn't exist when calling the function or for the
        // body's locals; we must remove it manually.
        // https://rustc-dev-guide.rust-lang.org/backend/implicit-caller-location.html
        let instance_abi = def.fn_abi()?;
        let arg_count = if self.requires_caller_location(def) {
            instance_abi.args.len() - 1
        } else {
            instance_abi.args.len()
        };

        let inputs: Vec<_> = instance_abi.args[0..arg_count]
            .iter()
            .map(|arg| self.translate_ty(span, arg.ty))
            .try_collect()?;
        let output = self.translate_ty(span, instance_abi.ret.ty)?;

        Ok(FunSig {
            inputs,
            output,
            // TODO: not sure how to get those
            is_unsafe: false,
            abi: Abi::rust(),
        })
    }

    /// Get the (monomorphic) MIR body of this instance, if it exists.
    ///
    /// We deliberately do *not* use rustc_public's `Instance::body`: that goes through
    /// `BodyBuilder`, which evaluates every const operand. That would discard the information
    /// that a constant refers to a named const item. Instead we fetch the MIR ourselves,
    /// and run our own [`NamedConstPreservingEvaluator`].
    pub fn get_body(&mut self, def: mir::mono::Instance) -> Option<rustc_public::mir::Body> {
        let tcx = self.t_ctx.tcx;
        let instance = rustc_internal::internal(tcx, def);
        let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();

        use rustc_middle::ty::InstanceKind;
        let body_internal = if !matches!(
            instance.def,
            InstanceKind::Intrinsic(..) | InstanceKind::Virtual(..)
        ) && def.body().is_some()
        {
            // A body is available and this isn't an intrinsic/virtual instance (for which
            // `instance_mir` would try—and fail—to build a shim). `instance_mir` handles shims
            // (drop glue, clone, fn-ptr shims, …) and ctfe bodies just like `BodyBuilder`, but we
            // then skip its const evaluation.
            Some(tcx.instance_mir(instance.def).clone())
        } else {
            // `def.body()` returns `None` for some items that still have usable MIR (notably
            // enum-variant constructors, and intrinsics with a fallback body). Fall back to the
            // raw MIR query — unlike `instance_mir`, this never tries to build a shim.
            let def_id = instance.def_id();
            if tcx.is_mir_available(def_id) && !tcx.is_static(def_id) {
                Some(tcx.optimized_mir(def_id).clone())
            } else if (tcx.is_static(def_id) && !tcx.is_trivial_const(def_id))
                || tcx.is_const_fn(def_id)
            {
                Some(tcx.mir_for_ctfe(def_id).clone())
            } else {
                None
            }
        };

        body_internal.map(|b| {
            // The MIR is generic; instantiate it with the instance's arguments so it is monomorphic.
            let mut b = instance.instantiate_mir_and_normalize_erasing_regions(
                tcx,
                typing_env,
                rustc_middle::ty::EarlyBinder::bind(b),
            );
            use rustc_middle::mir::visit::MutVisitor;
            NamedConstPreservingEvaluator { tcx, typing_env }.visit_body(&mut b);
            rustc_public::rustc_internal::stable(b)
        })
    }

    /// Translate the names of the arguments of this definition, if they are available,
    /// otherwise naming arguments `arg0`, `arg1`, etc.
    /// Note that the names of the arguments are not always available, even when
    /// we can retrieve the MIR body, in which case we also fall back to `argN`.
    pub fn translate_argument_names(
        &mut self,
        def: mir::mono::Instance,
        n_args: usize,
    ) -> Vec<Option<String>> {
        let Some(body) = self.get_body(def) else {
            return vec![None; n_args];
        };
        body.arg_locals()
            .iter()
            .enumerate()
            .map(|(index, _)| {
                body.var_debug_info.iter().find_map(|v| {
                    if let mir::VarDebugInfoContents::Place(place) = &v.value
                        && place.projection.is_empty()
                        && place.local == index + 1
                    {
                        Some(v.name.clone())
                    } else {
                        None
                    }
                })
            })
            .collect()
    }
}
