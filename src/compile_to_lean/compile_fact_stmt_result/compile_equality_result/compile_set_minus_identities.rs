use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_set_minus_identity(
        &self,
        fact: &EqualFact,
        rule: &EqualitySearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if let Some((law, args)) = difference_identity(left, right, rule) {
                let object = self.compile_object_reference(left, position)?;
                let symm = if reversed { ".symm" } else { "" };
                return Ok(format!(
                    "(let _set := {object}; (Litex.{law} {args}){symm})"
                ));
            }
        }
        Err(LeanCompileError::unsupported("SetMinusIdentity/Endpoints"))
    }
}

fn empty(object: &Obj) -> bool {
    matches!(object, Obj::SetFormer(SetFormer::ListSet(p)) if p.list.is_empty())
}

fn difference(object: &Obj) -> Option<(&Obj, &Obj)> {
    match object {
        Obj::SetOperator(SetOperator::SetMinus(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}

fn difference_identity(
    left: &Obj,
    right: &Obj,
    rule: &EqualitySearchProofByBuiltinRule,
) -> Option<(&'static str, &'static str)> {
    use EqualitySearchProofByBuiltinRule as Rule;
    if matches!(rule, Rule::IntersectSetMinusSelfEmpty(_)) {
        let Obj::SetOperator(SetOperator::Intersect(p)) = left else {
            return None;
        };
        if !empty(right) {
            return None;
        }
        if let Some((_, b)) = difference(&p.right) {
            if b.ir() == p.left.ir() {
                return Some((
                    "intersectSetMinusEmpty",
                    "_set.val.left _set.val.right.val.left",
                ));
            }
        }
        if let Some((_, b)) = difference(&p.left) {
            if b.ir() == p.right.ir() {
                return Some((
                    "setMinusIntersectEmpty",
                    "_set.val.right _set.val.left.val.left",
                ));
            }
        }
        return None;
    }
    let (a, b) = difference(left)?;
    match rule {
        Rule::SetMinusChainToUnion(_) => {
            let (base, first_removed) = difference(a)?;
            let (target_base, removed) = difference(right)?;
            let Obj::SetOperator(SetOperator::Union(removed)) = removed else {
                return None;
            };
            if base.ir() != target_base.ir() {
                return None;
            }
            let law = if first_removed.ir() == removed.left.ir() && b.ir() == removed.right.ir() {
                "setMinusChain"
            } else if first_removed.ir() == removed.right.ir() && b.ir() == removed.left.ir() {
                "setMinusChainSwap"
            } else {
                return None;
            };
            Some((
                law,
                "_set.val.left.val.left _set.val.left.val.right _set.val.right",
            ))
        }
        Rule::SetMinusSelfEmpty(_) => {
            (a.ir() == b.ir() && empty(right)).then_some(("setMinusSelf", "_set.val.left"))
        }
        Rule::SetMinusEmptyRight(_) => {
            (empty(b) && a.ir() == right.ir()).then_some(("setMinusEmptyRight", "_set.val.left"))
        }
        Rule::SetMinusEmptyLeft(_) => {
            (empty(a) && empty(right)).then_some(("setMinusEmptyLeft", "_set.val.right"))
        }
        Rule::SetMinusUnionDeMorgan(_) | Rule::SetMinusIntersectDeMorgan(_) => {
            let (b, d, first, second, law) = match (rule, b, right) {
                (
                    Rule::SetMinusUnionDeMorgan(_),
                    Obj::SetOperator(SetOperator::Union(p)),
                    Obj::SetOperator(SetOperator::Intersect(q)),
                ) => (&p.left, &p.right, &q.left, &q.right, "setMinusUnion"),
                (
                    Rule::SetMinusIntersectDeMorgan(_),
                    Obj::SetOperator(SetOperator::Intersect(p)),
                    Obj::SetOperator(SetOperator::Union(q)),
                ) => (&p.left, &p.right, &q.left, &q.right, "setMinusIntersect"),
                _ => return None,
            };
            let (fa, fb) = difference(first)?;
            let (sa, sd) = difference(second)?;
            (a.ir() == fa.ir() && a.ir() == sa.ir() && b.ir() == fb.ir() && d.ir() == sd.ir())
                .then_some((
                    law,
                    "_set.val.left _set.val.right.val.left _set.val.right.val.right",
                ))
        }
        _ => None,
    }
}
