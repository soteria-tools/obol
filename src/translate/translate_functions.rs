//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

extern crate stable_mir;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::{raise_error, register_error};
use stable_mir::{mir, rustc_internal, ty};

impl ItemTransCtx<'_, '_> {
    pub fn requires_caller_location(&self, instance: &mir::mono::Instance) -> bool {
        let instance_internal = rustc_internal::internal(self.t_ctx.tcx, instance);
        instance_internal
            .def
            .requires_caller_location(self.t_ctx.tcx)
    }

    pub(crate) fn get_function_ins_outs(
        &mut self,
        span: Span,
        def: &mir::mono::Instance,
    ) -> Result<(Vec<ty::Ty>, ty::Ty), Error> {
        let crate_item = stable_mir::CrateItem::try_from(*def)?;
        match crate_item.kind() {
            stable_mir::ItemKind::Fn | stable_mir::ItemKind::Ctor(_) => {
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

                let inputs = instance_abi.args[0..arg_count]
                    .iter()
                    .map(|arg| arg.ty)
                    .collect();
                Ok((inputs, instance_abi.ret.ty))
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
        def: &mir::mono::Instance,
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
