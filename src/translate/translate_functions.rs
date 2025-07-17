//! Translate functions from the rust compiler MIR to our internal representation.
//! Our internal representation is very close to MIR, but is more convenient for
//! us to handle, and easier to maintain - rustc's representation can evolve
//! independently.

extern crate stable_mir;

use super::translate_ctx::*;
use charon_lib::{ast::*, raise_error, register_error};
use stable_mir::{mir, ty};

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

        // self.translate_def_generics(span, def)?;
        // is_unsafe = def.ty().kind().fn_def().unwrap().0.fn_sig().value.safety
        let instance_ty = def.ty().kind();
        let Some(rigid) = instance_ty.rigid() else {
            raise_error!(self, Span::dummy(), "Instance without a rigid type?");
        };
        let signature = {
            match rigid {
                ty::RigidTy::FnDef(fndef, _) => Ok(fndef.fn_sig().value),
                ty::RigidTy::Closure(_, args) => {
                    let [.., fn_ty, _] = args.0.as_slice() else {
                        raise_error!(self, Span::dummy(), "Weird closure gen args");
                    };
                    let fn_ty_kind = fn_ty.expect_ty().kind();
                    let Some(ty::RigidTy::FnPtr(polysig)) = fn_ty_kind.rigid() else {
                        raise_error!(
                            self,
                            Span::dummy(),
                            "Expected a function type as the last argument of closure"
                        );
                    };
                    Ok(polysig.value.clone())
                }
                _ => raise_error!(
                    self,
                    Span::dummy(),
                    "Expected a function definition, found: {rigid:?}"
                ),
            }
        }?;
        // Translate the signature
        let inputs: Vec<Ty> = signature
            .inputs()
            .iter()
            .map(|ty| self.translate_ty(span, *ty))
            .try_collect()?;
        let output = self.translate_ty(span, signature.output())?;

        Ok(FunSig {
            generics: GenericParams::empty(),
            is_unsafe: false,
            inputs,
            output,
        })
    }
}
