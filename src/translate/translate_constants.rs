extern crate rustc_apfloat;
extern crate stable_mir;

use rustc_apfloat::{Float, ieee};

use charon_lib::{ast::*, error_assert, raise_error, register_error};
use stable_mir::ty;

use crate::translate::translate_ctx::ItemTransCtx;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub fn translate_allocation(
        &mut self,
        _span: Span,
        alloc: &ty::Allocation,
        ty: &TyKind,
    ) -> Result<RawConstantExpr, Error> {
        let constant = match ty {
            TyKind::Literal(lit) => match lit {
                LiteralTy::Int(it) => RawConstantExpr::Literal(Literal::Scalar(
                    ScalarValue::Signed(it.clone(), alloc.read_int().unwrap()),
                )),
                LiteralTy::UInt(uit) => RawConstantExpr::Literal(Literal::Scalar(
                    ScalarValue::Unsigned(uit.clone(), alloc.read_uint().unwrap()),
                )),
                LiteralTy::Bool => {
                    RawConstantExpr::Literal(Literal::Bool(alloc.read_bool().unwrap()))
                }
                LiteralTy::Char => RawConstantExpr::Literal(Literal::Char(
                    char::from_u32(alloc.read_uint().unwrap() as u32).unwrap(),
                )),
                LiteralTy::Float(f) => {
                    let bits = alloc.read_uint().unwrap();
                    let value = match f {
                        FloatTy::F16 => ieee::Half::from_bits(bits).to_string(),
                        FloatTy::F32 => ieee::Single::from_bits(bits).to_string(),
                        FloatTy::F64 => ieee::Double::from_bits(bits).to_string(),
                        FloatTy::F128 => ieee::Quad::from_bits(bits).to_string(),
                    };
                    RawConstantExpr::Literal(Literal::Float(FloatValue {
                        value,
                        ty: f.clone(),
                    }))
                }
            },
            _ => {
                println!("Gave up for raw memory of type {ty:?}");
                RawConstantExpr::RawMemory(alloc.bytes.iter().map(|b| b.unwrap_or(0u8)).collect())
            }
        };
        Ok(constant)
    }

    pub fn translate_zst_constant(
        &mut self,
        _span: Span,
        ty: &TyKind,
    ) -> Result<RawConstantExpr, Error> {
        match ty {
            TyKind::FnDef(fnptr) => Ok(RawConstantExpr::FnPtr(fnptr.skip_binder.clone())),
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Tuple,
                generics,
            }) if generics.is_empty() => Ok(RawConstantExpr::Adt(None, vec![])),
            _ => {
                println!("Gave up on const for ZST type: {:?}", ty);
                Ok(RawConstantExpr::RawMemory(vec![]))
            }
        }
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
                let ty = self.translate_ty(span, *ty)?;
                let alloc = self.translate_allocation(span, alloc, ty.kind())?;
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
