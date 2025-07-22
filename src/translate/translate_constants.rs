extern crate stable_mir;

use charon_lib::{ast::*, error_assert, raise_error, register_error};
use stable_mir::ty;

use crate::translate::translate_ctx::ItemTransCtx;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub fn translate_allocation(
        &mut self,
        _span: Span,
        alloc: &ty::Allocation,
        ty: ty::Ty,
    ) -> Result<RawConstantExpr, Error> {
        let constant = match ty.kind() {
            ty::TyKind::RigidTy(ty::RigidTy::Int(it)) => {
                let value = alloc.read_int().unwrap();
                let int_ty = self.translate_int_ty(&it);
                RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Signed(int_ty, value)))
            }
            ty::TyKind::RigidTy(ty::RigidTy::Uint(uit)) => {
                let value = alloc.read_uint().unwrap();
                let uint_ty = self.translate_uint_ty(&uit);
                RawConstantExpr::Literal(Literal::Scalar(ScalarValue::Unsigned(uint_ty, value)))
            }
            ty::TyKind::RigidTy(ty::RigidTy::Bool) => {
                let value = alloc.read_bool().unwrap();
                RawConstantExpr::Literal(Literal::Bool(value))
            }
            ty::TyKind::RigidTy(ty::RigidTy::Char) => {
                let value = char::from_u32(alloc.read_uint().unwrap() as u32);
                RawConstantExpr::Literal(Literal::Char(value.unwrap()))
            }
            _ => RawConstantExpr::RawMemory(alloc.bytes.iter().map(|b| b.unwrap_or(0u8)).collect()),
        };
        Ok(constant)
    }

    pub(crate) fn translate_constant_expr_to_const_generic(
        &mut self,
        span: Span,
        value: RawConstantExpr,
    ) -> Result<ConstGeneric, Error> {
        match value {
            RawConstantExpr::Var(v) => Ok(ConstGeneric::Var(v)),
            RawConstantExpr::Literal(v) => Ok(ConstGeneric::Value(v)),
            RawConstantExpr::Global(global_ref) => {
                // TODO: handle constant arguments with generics (this can likely only happen with
                // a feature gate).
                error_assert!(self, span, global_ref.generics.is_empty());
                Ok(ConstGeneric::Global(global_ref.id))
            }
            RawConstantExpr::Adt(..)
            | RawConstantExpr::Array { .. }
            | RawConstantExpr::RawMemory { .. }
            | RawConstantExpr::TraitConst { .. }
            | RawConstantExpr::Ref(_)
            | RawConstantExpr::Ptr(..)
            | RawConstantExpr::FnPtr { .. }
            | RawConstantExpr::Opaque(_) => {
                raise_error!(self, span, "Unexpected constant generic: {:?}", value)
            }
        }
    }

    pub fn translate_tyconst_to_const_generic(
        &mut self,
        span: Span,
        v: &ty::TyConst,
    ) -> Result<ConstGeneric, Error> {
        match v.kind() {
            ty::TyConstKind::Value(ty, alloc) => {
                let alloc = self.translate_allocation(span, alloc, *ty)?;
                self.translate_constant_expr_to_const_generic(span, alloc)
            }
            _ => {
                raise_error!(
                    self,
                    span,
                    "Unexpected constant expression kind: {:?}",
                    v.kind()
                )
            }
        }
    }
}
