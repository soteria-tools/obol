//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

extern crate rustc_middle;
extern crate stable_mir;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::{raise_error, register_error};
use stable_mir::{CrateDef, mir, rustc_internal, ty};

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

    /// If this instance is a closure or a call shim, meaning in MIR it has untupled arguments but
    /// only in the signature!
    pub fn instance_is_closure_or_call_shim(&self, def: mir::mono::Instance) -> bool {
        let def_ty = def.ty().kind();
        let name_opt = match def_ty.rigid() {
            Some(ty::RigidTy::FnDef(fndef, _)) => Some(fndef.def_id().name()),
            _ => None,
        };
        self.instance_is_closure(def)
            || name_opt.is_some_and(|name| {
                matches!(
                    name.as_str(),
                    "std::ops::Fn::call"
                        | "std::ops::FnMut::call_mut"
                        | "std::ops::FnOnce::call_once"
                )
            })
    }

    fn get_function_ins_outs_sure_function(
        &mut self,
        span: Span,
        def: mir::mono::Instance,
    ) -> Result<(Vec<ty::Ty>, ty::Ty), Error> {
        // Translate the signature

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

        let mut inputs: Vec<_> = instance_abi.args[0..arg_count]
            .iter()
            .map(|arg| arg.ty)
            .collect();

        // If the first argument is a closure, we need to tuple up the remaining arguments
        if self.instance_is_closure_or_call_shim(def) {
            let [closure_state, rest @ ..] = &*inputs.into_boxed_slice() else {
                raise_error!(self, span, "Unexpected closure signature");
            };
            let tupled_args = ty::Ty::new_tuple(rest);
            inputs = vec![*closure_state, tupled_args];
        }
        Ok((inputs, instance_abi.ret.ty))
    }

    pub(crate) fn get_function_ins_outs(
        &mut self,
        span: Span,
        def: mir::mono::Instance,
    ) -> Result<(Vec<ty::Ty>, ty::Ty), Error> {
        let Ok(crate_item) = stable_mir::CrateItem::try_from(def) else {
            // worth a shot
            return self.get_function_ins_outs_sure_function(span, def);
        };
        match crate_item.kind() {
            stable_mir::ItemKind::Fn | stable_mir::ItemKind::Ctor(_) => {
                self.get_function_ins_outs_sure_function(span, def)
            }
            stable_mir::ItemKind::Static => {
                let stt: mir::mono::StaticDef = crate_item.try_into()?;
                Ok((vec![], stt.ty()))
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

    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    pub(crate) fn translate_function_signature(
        &mut self,
        def: mir::mono::Instance,
        item_meta: &ItemMeta,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        let (inputs, outputs) = self.get_function_ins_outs(span, def)?;

        let inputs = inputs
            .into_iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let output = self.translate_ty(span, outputs)?;

        Ok(FunSig {
            generics: GenericParams::empty(),
            is_unsafe: false,
            inputs,
            output,
        })
    }
}
