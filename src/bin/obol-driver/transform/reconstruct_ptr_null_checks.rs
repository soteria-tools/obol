//! # Micro-pass: reconstruct pointer null-checks.
//!
//! When rustc lowers a pointer null-check (e.g. `<*const T>::is_null`), it reinterprets the
//! pointer's bits as an integer and tests that integer against `0`. Depending on the MIR level, the
//! test takes one of two shapes:
//! ```text
//! // optimized MIR: the comparison is a `switch` terminator
//! _23 := transmute<*mut u8, usize>(copy raw_ptr_6);
//! switch copy _23 -> [0: bb20, otherwise: bb21]
//!
//! // built MIR: the comparison is a `== 0` / `!= 0` statement
//! _3 := transmute<*const u8, usize>(copy _2);
//! _0 := move _3 == const 0usize;
//! ```
//!
//! Some tools would like to avoid reasoning about the pointer-to-integer transmutation. Instead we
//! compare the pointer against the null pointer (a no-provenance pointer with address `0`), so
//! that the comparison stays in the pointer world:
//! ```text
//! _tmp := copy raw_ptr_6 != const (no-provenance 0);
//! _23 := cast<bool, usize>(move _tmp);
//! switch copy _23 -> [0: bb20, otherwise: bb21]
//! ```
//! The new value assigned to `_23` is `0` if and only if the pointer is null, exactly like the
//! transmuted address it replaces, so the null-check itself is left untouched. The only
//! information lost is the address of a non-null pointer (the value becomes `1`), which is sound
//! because that value feeds nothing but the null-check.
//!
//! The transformation is only fired when:
//! - we transmute a *sized* (thin) pointer to `usize`/`isize`;
//! - the result feeds either a switch with a single `0` case and an otherwise branch, or a
//!   `== 0` / `!= 0` comparison against the null address;
//! - the transmuted value is used nowhere else (necessary for soundness)

use charon_lib::ast::Visitor;
use std::collections::HashSet;
use std::ops::ControlFlow::{self, Continue};

use charon_lib::ids::IndexVec;
use charon_lib::transform::TransformCtx;
use charon_lib::transform::ctx::{BodyTransformCtx, UllbcPass};
use charon_lib::ullbc_ast::*;

/// Count how many times each local appears in the body, ignoring `StorageLive`/`StorageDead`
/// statements (which mention a local but don't actually use its value).
#[derive(Visitor)]
struct LocalUsageCounter {
    counts: IndexVec<LocalId, usize>,
}

fn literal_is_zero(lit: &Literal) -> bool {
    matches!(lit, Literal::Scalar(scalar) if scalar.to_bits() == 0)
}

fn operand_is_zero(op: &Operand) -> bool {
    matches!(
        op,
        Operand::Const(c) if matches!(&c.kind, ConstantExprKind::Literal(lit) if literal_is_zero(lit))
    )
}

fn operand_as_local(op: &Operand) -> Option<LocalId> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => p.as_local(),
        Operand::Const(_) => None,
    }
}

impl VisitBody for LocalUsageCounter {
    fn enter_local_id(&mut self, lid: &LocalId) {
        self.counts[*lid] += 1;
    }
    fn visit_ullbc_statement(&mut self, st: &Statement) -> ControlFlow<Self::Break> {
        match &st.kind {
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => Continue(()),
            _ => self.visit_inner(st),
        }
    }
}

fn count_local_usages(b: &ExprBody) -> IndexVec<LocalId, usize> {
    let mut visitor = LocalUsageCounter {
        counts: b.locals.locals.map_ref(|_| 0),
    };
    let _ = b.body.drive_body(&mut visitor);
    visitor.counts
}

/// Whether `local`'s non-defining use is a pointer null-check, i.e. either:
/// - a `switch local -> [0: _, otherwise: _]` terminator (the shape rustc emits in *optimized*
///   MIR), or
/// - a `_ = (local == 0)` / `_ = (local != 0)` comparison statement (the shape rustc emits in
///   *built* MIR, where `<*const T>::is_null` is `transmute::<*T, usize>(p) == 0`).
///
/// The caller guarantees `local` is used exactly twice, so whichever use we find here is its unique
/// non-defining use.
fn feeds_null_check(block: &BlockData, local: LocalId) -> bool {
    // The result feeds a `switch [0, otherwise]` terminator.
    if let TerminatorKind::Switch {
        discr,
        targets: SwitchTargets::SwitchInt(_, cases, _),
    } = &block.terminator.kind
        && let [(case, _)] = cases.as_slice()
        && literal_is_zero(case)
        && operand_as_local(discr) == Some(local)
    {
        return true;
    }
    // The result feeds a `== 0` / `!= 0` comparison against the null address.
    block.statements.iter().any(|st| {
        matches!(
            &st.kind,
            StatementKind::Assign(_, Rvalue::BinaryOp(BinOp::Eq | BinOp::Ne, lhs, rhs))
                if (operand_as_local(lhs) == Some(local) && operand_is_zero(rhs))
                    || (operand_as_local(rhs) == Some(local) && operand_is_zero(lhs))
        )
    })
}

/// Whether `st` is a `transmute` of a sized (thin) pointer into a `usize`/`isize` whose result is
/// used exactly twice and whose unique other use is a null-check (a `switch [0, _]` or a `== 0` /
/// `!= 0` within `block`). When it is, return the local the transmute result is assigned to.
fn match_transmuted_null_check(
    ctx: &TransformCtx,
    usages: &IndexVec<LocalId, usize>,
    block: &BlockData,
    st: &Statement,
) -> Option<LocalId> {
    let StatementKind::Assign(
        place,
        Rvalue::UnaryOp(UnOp::Cast(CastKind::Transmute(src_ty, tgt_ty)), _),
    ) = &st.kind
    else {
        return None;
    };
    let result = place.as_local()?;
    let TyKind::Literal(LiteralTy::UInt(UIntTy::Usize) | LiteralTy::Int(IntTy::Isize)) =
        tgt_ty.kind()
    else {
        return None;
    };
    if usages[result] != 2 {
        return None;
    }
    let (TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _)) = src_ty.kind() else {
        return None;
    };
    if !matches!(pointee.get_ptr_metadata(&ctx.translated), PtrMetadata::None) {
        return None;
    }
    if !feeds_null_check(block, result) {
        return None;
    }
    Some(result)
}

pub struct Transform;

impl UllbcPass for Transform {
    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        let Some(body) = decl.body.as_unstructured() else {
            return;
        };

        // Find the transmute results to rewrite up front: the rewrite below runs per-statement and
        // can't see the block terminator, but recognizing the null-check needs it (the `switch`
        // shape) and needs the body-wide usage counts.
        let usages = count_local_usages(body);
        let targets: HashSet<LocalId> = body
            .body
            .iter()
            .flat_map(|block| {
                block
                    .statements
                    .iter()
                    .filter_map(|st| match_transmuted_null_check(ctx, &usages, block, st))
            })
            .collect();
        if targets.is_empty() {
            return;
        }

        decl.transform_ullbc_statements(ctx, |ctx, st: &mut Statement| {
            let StatementKind::Assign(
                place,
                Rvalue::UnaryOp(UnOp::Cast(CastKind::Transmute(src_ty, tgt_ty)), op),
            ) = &st.kind
            else {
                return;
            };
            let Some(result) = place.as_local() else {
                return;
            };
            if !targets.contains(&result) {
                return;
            }
            let TyKind::Literal(tgt_lit_ty) = tgt_ty.kind() else {
                return;
            };
            let tgt_lit_ty = *tgt_lit_ty;
            let dest = place.clone();
            let src_ty = src_ty.clone();
            let operand = op.clone();

            // `(p != null) as usize` is `0` exactly when `transmute::<_, usize>(p)` is, so the
            // downstream null-check is left untouched. `fresh_var` inserts the temp's `StorageLive`;
            // we reuse the transmute statement's own slot for the matching `StorageDead`.
            let tmp = ctx.fresh_var(None, Ty::mk_bool());
            let null_ptr = Operand::Const(Box::new(ConstantExpr {
                kind: ConstantExprKind::PtrNoProvenance(0),
                ty: src_ty,
            }));
            ctx.insert_assn_stmt(tmp.clone(), Rvalue::BinaryOp(BinOp::Ne, operand, null_ptr));
            ctx.insert_assn_stmt(
                dest,
                Rvalue::UnaryOp(
                    UnOp::Cast(CastKind::Scalar(LiteralTy::Bool, tgt_lit_ty)),
                    Operand::Move(tmp.clone()),
                ),
            );
            st.kind = StatementKind::StorageDead(tmp.as_local().unwrap());
        });
    }
}
