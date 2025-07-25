//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

extern crate stable_mir;

use super::translate_ctx::*;
use charon_lib::ast::*;
use stable_mir::mir;

impl ItemTransCtx<'_, '_> {
    /// Translate a function's signature, and initialize a body translation context
    /// at the same time - the function signature gives us the list of region and
    /// type parameters, that we put in the translation context.
    pub(crate) fn translate_function_signature(
        &mut self,
        def: &mir::mono::Instance,
        item_meta: &ItemMeta,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        let instance_abi = def.fn_abi()?;

        // Translate the signature

        let inputs: Vec<Ty> = instance_abi
            .args
            .iter()
            .map(|arg| self.translate_ty(span, arg.ty))
            .try_collect()?;
        let output = self.translate_ty(span, instance_abi.ret.ty)?;

        Ok(FunSig {
            generics: GenericParams::empty(),
            is_unsafe: false,
            inputs,
            output,
        })
    }
}
