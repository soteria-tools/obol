extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_span;

use log::trace;
use rustc_public::{mir, ty};

use charon_lib::{ast::*, ids::IndexVec, raise_error, register_error, ullbc_ast::*};

use crate::translate::translate_ctx::ItemTransCtx;

impl ItemTransCtx<'_, '_> {
    /// Translate a coroutine as an enum
    pub(crate) fn translate_coroutine_as_adt_def(
        &mut self,
        trans_id: TypeDeclId,
        def_span: Span,
        item_meta: &ItemMeta,
        _coroutine: &ty::CoroutineDef,
        args: &ty::GenericArgs,
    ) -> Result<TypeDeclKind, Error> {
        if item_meta.opacity.is_opaque() {
            return Ok(TypeDeclKind::Opaque);
        }

        trace!("{}", trans_id);

        let tupled_upvars = args.0.last().unwrap().expect_ty().kind();
        let Some(ty::RigidTy::Tuple(state_tys)) = tupled_upvars.rigid() else {
            raise_error!(self, def_span, "Closure state argument is not a tuple?");
        };

        let mut fields: IndexVec<FieldId, Field> = Default::default();
        for (j, state_ty) in state_tys.iter().enumerate() {
            // Translate the field type
            let ty = self.translate_ty(def_span, *state_ty)?;

            // Retrieve the field name.
            let field_name = format!("upvar_{j}");

            // Store the field
            let field = Field {
                span: def_span,
                attr_info: AttrInfo::default(),
                name: Some(field_name),
                ty,
            };
            fields.push(field);
        }

        let type_def_kind = TypeDeclKind::Struct(fields);

        Ok(type_def_kind)
    }

    pub(crate) fn translate_coroutine_src_info(
        &mut self,
        _span: Span,
        _coroutine: &ty::CoroutineDef,
        _args: &ty::GenericArgs,
    ) -> Result<ItemSource, Error> {
        // FIXME: This is wrong, I just need it to compile.
        Ok(ItemSource::TopLevel)
    }
}
