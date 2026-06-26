use crate::prelude::*;

/// Structural alignment for builtin patterns: two objects match iff their `Display` text matches.
#[inline]
pub fn objs_equal_by_display_string(a: &Obj, b: &Obj) -> bool {
    a.to_string() == b.to_string()
}

pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
    objs_equal_by_display_string(left, right)
}

#[inline]
pub(crate) fn obj_expr_mentions_bare_id_on_two(l: &Obj, r: &Obj, id: &str) -> bool {
    obj_expr_mentions_bare_id(l, id) || obj_expr_mentions_bare_id(r, id)
}

/// Whether `obj` contains a bare [`Identifier`] equal to `id` (used to detect index use in a
/// summand `equal_to`). Unknown / unhandled shapes return `true` (conservative).
pub(crate) fn obj_expr_mentions_bare_id(obj: &Obj, id: &str) -> bool {
    match obj {
        Obj::Atom(AtomObj::Identifier(i)) => i.name == id,
        Obj::Number(_) | Obj::StandardSet(_) => false,
        Obj::Add(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Sub(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Mul(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Div(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Mod(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Max(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Min(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Union(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::Intersect(b) => {
            obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id)
        }
        Obj::SetMinus(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::SetDiff(b) => obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id),
        Obj::MatrixAdd(b) => {
            obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id)
        }
        Obj::MatrixSub(b) => {
            obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id)
        }
        Obj::MatrixMul(b) => {
            obj_expr_mentions_bare_id_on_two(b.left.as_ref(), b.right.as_ref(), id)
        }
        Obj::Pow(p) => {
            obj_expr_mentions_bare_id(p.base.as_ref(), id)
                || obj_expr_mentions_bare_id(p.exponent.as_ref(), id)
        }
        Obj::MatrixScalarMul(m) => {
            obj_expr_mentions_bare_id(m.scalar.as_ref(), id)
                || obj_expr_mentions_bare_id(m.matrix.as_ref(), id)
        }
        Obj::MatrixPow(m) => {
            obj_expr_mentions_bare_id(m.base.as_ref(), id)
                || obj_expr_mentions_bare_id(m.exponent.as_ref(), id)
        }
        Obj::Abs(u) => obj_expr_mentions_bare_id(u.arg.as_ref(), id),
        Obj::Sqrt(u) => obj_expr_mentions_bare_id(u.arg.as_ref(), id),
        Obj::PowerSet(u) => obj_expr_mentions_bare_id(u.set.as_ref(), id),
        Obj::Cup(u) => obj_expr_mentions_bare_id(u.left.as_ref(), id),
        Obj::Cap(u) => obj_expr_mentions_bare_id(u.left.as_ref(), id),
        Obj::Log(l) => {
            obj_expr_mentions_bare_id(l.base.as_ref(), id)
                || obj_expr_mentions_bare_id(l.arg.as_ref(), id)
        }
        Obj::ListSet(list) => list
            .list
            .iter()
            .any(|o| obj_expr_mentions_bare_id(o.as_ref(), id)),
        Obj::Tuple(t) => t
            .args
            .iter()
            .any(|o| obj_expr_mentions_bare_id(o.as_ref(), id)),
        Obj::Cart(c) => c
            .args
            .iter()
            .any(|o| obj_expr_mentions_bare_id(o.as_ref(), id)),
        Obj::Count(c) => obj_expr_mentions_bare_id(c.set.as_ref(), id),
        Obj::FnRange(r) => obj_expr_mentions_bare_id(r.function.as_ref(), id),
        Obj::FnRangeOn(r) => {
            obj_expr_mentions_bare_id(r.function.as_ref(), id)
                || obj_expr_mentions_bare_id(r.set.as_ref(), id)
        }
        Obj::Replacement(r) => obj_expr_mentions_bare_id(r.source_set.as_ref(), id),
        Obj::TupleDim(t) => obj_expr_mentions_bare_id(t.arg.as_ref(), id),
        Obj::CartDim(c) => obj_expr_mentions_bare_id(c.set.as_ref(), id),
        Obj::Proj(p) => {
            obj_expr_mentions_bare_id(p.set.as_ref(), id)
                || obj_expr_mentions_bare_id(p.dim.as_ref(), id)
        }
        Obj::ObjAtIndex(oi) => {
            obj_expr_mentions_bare_id(oi.obj.as_ref(), id)
                || obj_expr_mentions_bare_id(oi.index.as_ref(), id)
        }
        Obj::Range(r) => obj_expr_mentions_bare_id_on_two(r.start.as_ref(), r.end.as_ref(), id),
        Obj::ClosedRange(r) => {
            obj_expr_mentions_bare_id_on_two(r.start.as_ref(), r.end.as_ref(), id)
        }
        Obj::IntervalObj(i) => obj_expr_mentions_bare_id_on_two(i.start(), i.end(), id),
        Obj::OneSideInfinityIntervalObj(i) => obj_expr_mentions_bare_id(i.start(), id),
        Obj::Sum(s) => {
            obj_expr_mentions_bare_id(s.start.as_ref(), id)
                || obj_expr_mentions_bare_id(s.end.as_ref(), id)
                || obj_expr_mentions_bare_id(s.func.as_ref(), id)
        }
        Obj::SumOfFiniteSet(s) => {
            obj_expr_mentions_bare_id(s.set.as_ref(), id)
                || obj_expr_mentions_bare_id(s.func.as_ref(), id)
        }
        Obj::Product(p) => {
            obj_expr_mentions_bare_id(p.start.as_ref(), id)
                || obj_expr_mentions_bare_id(p.end.as_ref(), id)
                || obj_expr_mentions_bare_id(p.func.as_ref(), id)
        }
        Obj::ProductOfFiniteSet(p) => {
            obj_expr_mentions_bare_id(p.set.as_ref(), id)
                || obj_expr_mentions_bare_id(p.func.as_ref(), id)
        }
        Obj::FiniteSeqListObj(f) => f
            .objs
            .iter()
            .any(|o| obj_expr_mentions_bare_id(o.as_ref(), id)),
        Obj::MatrixListObj(m) => m.rows.iter().any(|row| {
            row.iter()
                .any(|o| obj_expr_mentions_bare_id(o.as_ref(), id))
        }),
        Obj::StructObj(so) => so.params.iter().any(|p| obj_expr_mentions_bare_id(p, id)),
        Obj::ObjAsStructInstanceWithFieldAccess(fa) => {
            obj_expr_mentions_bare_id(fa.obj.as_ref(), id)
                || fa
                    .struct_obj
                    .params
                    .iter()
                    .any(|p| obj_expr_mentions_bare_id(p, id))
        }
        Obj::InstantiatedTemplateObj(t) => {
            t.args.iter().any(|arg| obj_expr_mentions_bare_id(arg, id))
        }
        Obj::FiniteSeqSet(fs) => {
            obj_expr_mentions_bare_id(fs.set.as_ref(), id)
                || obj_expr_mentions_bare_id(fs.n.as_ref(), id)
        }
        Obj::SeqSet(ss) => obj_expr_mentions_bare_id(ss.set.as_ref(), id),
        Obj::MatrixSet(ms) => {
            obj_expr_mentions_bare_id(ms.set.as_ref(), id)
                || obj_expr_mentions_bare_id(ms.row_len.as_ref(), id)
                || obj_expr_mentions_bare_id(ms.col_len.as_ref(), id)
        }
        Obj::Atom(AtomObj::IdentifierWithMod(_)) => false,
        Obj::AnonymousFn(anon) => {
            for g in anon.body.params_def_with_set.iter() {
                let mentions = obj_expr_mentions_bare_id(g.set_obj(), id);
                if mentions {
                    return true;
                }
            }
            obj_expr_mentions_bare_id(anon.body.ret_set.as_ref(), id)
                || obj_expr_mentions_bare_id(anon.equal_to.as_ref(), id)
        }
        Obj::FnObj(_) | Obj::FnSet(_) | Obj::SetBuilder(_) => true,
        Obj::Atom(AtomObj::Forall(p)) => p.name == id,
        Obj::Atom(AtomObj::Def(p)) => p.name == id,
        Obj::Atom(AtomObj::Exist(p)) => p.name == id,
        Obj::Atom(AtomObj::SetBuilder(p)) => p.name == id,
        Obj::Atom(AtomObj::FnSet(p)) => p.name == id,
        Obj::Atom(AtomObj::Induc(p)) => p.name == id,
        Obj::Atom(AtomObj::DefAlgo(p)) => p.name == id,
        Obj::Atom(AtomObj::DefStructField(p)) => p.name == id,
    }
}

pub(crate) fn factual_equal_success_by_builtin_reason(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
) -> StmtResult {
    factual_equal_success_by_builtin_reason_with_subgoals(
        left,
        right,
        line_file,
        reason,
        Vec::new(),
    )
}

pub(crate) fn factual_equal_success_by_builtin_reason_with_subgoals(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
    subgoals: Vec<StmtResult>,
) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            EqualFact::new(left.clone(), right.clone(), line_file).into(),
            reason.to_string(),
            subgoals,
        ),
    )
}

pub(crate) fn equality_builtin_match_subgoals(
    actual: &Obj,
    expected: &Obj,
    result: StmtResult,
) -> Vec<StmtResult> {
    if verify_equality_by_they_are_the_same(actual, expected) {
        Vec::new()
    } else {
        vec![result]
    }
}
