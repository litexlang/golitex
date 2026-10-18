//! Fixed symmetric-difference identities under parent set-object WD.
use super::super::helper::corresponding_arg_pairs;
use crate::prelude::*;
pub(super) fn symmetric_difference(fact: &EqualFact) -> Option<SymmetricDifferenceEqualityProof> {
    use SymmetricDifferenceEqualityProof as P;
    if let Some(proof) = finite_rationals(fact) {
        return Some(P::SymDiffFiniteRationals(proof));
    }
    let mut pending = vec![fact.left.clone(), fact.right.clone()];
    while let Some(obj) = pending.pop() {
        let pair = match &obj {
            Obj::SetOperator(SetOperator::SymmetricDifference(pair)) => {
                Some((&*pair.left, &*pair.right))
            }
            _ => None,
        };
        if let Some((a, b)) = pair {
            if matches_equation(
                fact,
                diff(a.clone(), b.clone()),
                union(minus(a.clone(), b.clone()), minus(b.clone(), a.clone())),
            ) {
                return Some(P::SymDiffDefinition(SymDiffDefinitionProof));
            }
            if matches_equation(fact, diff(a.clone(), b.clone()), diff(b.clone(), a.clone())) {
                return Some(P::SymDiffCommutative(SymDiffCommutativeProof));
            }
            if matches_equation(fact, diff(a.clone(), a.clone()), empty()) {
                return Some(P::SymDiffSelf(SymDiffSelfProof));
            }
            if matches_equation(fact, diff(a.clone(), empty()), a.clone()) {
                return Some(P::SymDiffEmpty(SymDiffEmptyProof));
            }
            if matches_equation(fact, diff(empty(), b.clone()), b.clone()) {
                return Some(P::SymDiffEmptyLeft(SymDiffEmptyLeftProof));
            }
            if matches_equation(fact, diff(diff(a.clone(), b.clone()), b.clone()), a.clone()) {
                return Some(P::SymDiffCancel(SymDiffCancelProof));
            }
            if matches_equation(
                fact,
                diff(a.clone(), b.clone()),
                minus(union(a.clone(), b.clone()), intersect(a.clone(), b.clone())),
            ) {
                return Some(P::SymDiffUnionMinusIntersection(
                    SymDiffUnionMinusIntersectionProof,
                ));
            }
            for nested in [a, b] {
                if let Obj::SetOperator(SetOperator::SymmetricDifference(inner)) = nested {
                    let (a, b, c) = if nested.ir() == a.ir() {
                        (&*inner.left, &*inner.right, b)
                    } else {
                        (a, &*inner.left, &*inner.right)
                    };
                    if matches_equation(
                        fact,
                        diff(diff(a.clone(), b.clone()), c.clone()),
                        diff(a.clone(), diff(b.clone(), c.clone())),
                    ) {
                        return Some(P::SymDiffAssociative(SymDiffAssociativeProof));
                    }
                }
            }
        }
        if let Obj::SetOperator(SetOperator::Intersect(pair)) = &obj {
            if let Obj::SetOperator(SetOperator::SymmetricDifference(inner)) = &*pair.right {
                let (a, b, c) = (&*pair.left, &*inner.left, &*inner.right);
                if matches_equation(
                    fact,
                    intersect(a.clone(), diff(b.clone(), c.clone())),
                    diff(
                        intersect(a.clone(), b.clone()),
                        intersect(a.clone(), c.clone()),
                    ),
                ) {
                    return Some(P::IntersectionDistributesSymDiff(
                        IntersectionDistributesSymDiffProof,
                    ));
                }
            }
        }
        if let Some(children) = corresponding_arg_pairs(&obj, &obj) {
            pending.extend(children.into_iter().map(|(child, _)| child));
        }
    }
    None
}

fn diff(left: Obj, right: Obj) -> Obj {
    SymmetricDifference::new(left, right).into()
}
fn union(left: Obj, right: Obj) -> Obj {
    Obj::SetOperator(SetOperator::Union(Union {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
fn minus(left: Obj, right: Obj) -> Obj {
    Obj::SetOperator(SetOperator::SetMinus(SetMinus {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
fn intersect(left: Obj, right: Obj) -> Obj {
    Obj::SetOperator(SetOperator::Intersect(Intersect {
        left: Box::new(left),
        right: Box::new(right),
    }))
}
fn empty() -> Obj {
    Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] }))
}
fn matches_equation(f: &EqualFact, left: Obj, right: Obj) -> bool {
    (f.left.ir() == left.ir() && f.right.ir() == right.ir())
        || (f.right.ir() == left.ir() && f.left.ir() == right.ir())
}
pub enum SymmetricDifferenceEqualityProof {
    SymDiffFiniteRationals(SymDiffFiniteRationalsProof),
    SymDiffDefinition(SymDiffDefinitionProof),
    SymDiffCommutative(SymDiffCommutativeProof),
    SymDiffSelf(SymDiffSelfProof),
    SymDiffEmpty(SymDiffEmptyProof),
    SymDiffEmptyLeft(SymDiffEmptyLeftProof),
    SymDiffCancel(SymDiffCancelProof),
    SymDiffUnionMinusIntersection(SymDiffUnionMinusIntersectionProof),
    SymDiffAssociative(SymDiffAssociativeProof),
    IntersectionDistributesSymDiff(IntersectionDistributesSymDiffProof),
}
pub struct SymDiffDefinitionProof;
pub struct SymDiffCommutativeProof;
pub struct SymDiffSelfProof;
pub struct SymDiffEmptyProof;
pub struct SymDiffEmptyLeftProof;
pub struct SymDiffCancelProof;
pub struct SymDiffUnionMinusIntersectionProof;
pub struct SymDiffAssociativeProof;
pub struct IntersectionDistributesSymDiffProof;
impl SymmetricDifferenceEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SymDiffFiniteRationals(_) => "SymDiffFiniteRationals",
            Self::SymDiffDefinition(_) => "SymDiffDefinition",
            Self::SymDiffCommutative(_) => "SymDiffCommutative",
            Self::SymDiffSelf(_) => "SymDiffSelf",
            Self::SymDiffEmpty(_) => "SymDiffEmpty",
            Self::SymDiffEmptyLeft(_) => "SymDiffEmptyLeft",
            Self::SymDiffCancel(_) => "SymDiffCancel",
            Self::SymDiffUnionMinusIntersection(_) => "SymDiffUnionMinusIntersection",
            Self::SymDiffAssociative(_) => "SymDiffAssociative",
            Self::IntersectionDistributesSymDiff(_) => "IntersectionDistributesSymDiff",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SymDiffFiniteRationals(_) => {
                "Finite rational lists: keep exactly the values occurring in one operand"
            }
            Self::SymDiffDefinition(_) => "A triangle B=(A-B) union (B-A)",
            Self::SymDiffCommutative(_) => "A triangle B=B triangle A",
            Self::SymDiffSelf(_) => "A triangle A={}",
            Self::SymDiffEmpty(_) => "A triangle {}=A",
            Self::SymDiffEmptyLeft(_) => "{} triangle A=A",
            Self::SymDiffCancel(_) => "(A triangle B) triangle B=A",
            Self::SymDiffUnionMinusIntersection(_) => "A triangle B=(A union B)-(A intersect B)",
            Self::SymDiffAssociative(_) => "(A triangle B) triangle C=A triangle (B triangle C)",
            Self::IntersectionDistributesSymDiff(_) => {
                "A intersect (B triangle C)=(A intersect B) triangle (A intersect C)"
            }
        }
    }
}

// Store exact normalized values so output/replay does not depend on recomputing
// membership through a mutable environment. Unknown symbolic overlaps decline.
pub struct SymDiffFiniteRationalsProof {
    pub left_values: Vec<EvalRational>,
    pub right_values: Vec<EvalRational>,
    pub result_values: Vec<EvalRational>,
}
fn rational_list(obj: &Obj) -> Option<Vec<EvalRational>> {
    let Obj::SetFormer(SetFormer::ListSet(list)) = obj else {
        return None;
    };
    list.list
        .iter()
        .map(|x| EvalRational::from_obj(x))
        .collect()
}
fn finite_rationals(fact: &EqualFact) -> Option<SymDiffFiniteRationalsProof> {
    for (native, target) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
        let Obj::SetOperator(SetOperator::SymmetricDifference(pair)) = native else {
            continue;
        };
        let (Some(left), Some(right), Some(result)) = (
            rational_list(&pair.left),
            rational_list(&pair.right),
            rational_list(target),
        ) else {
            continue;
        };
        let expected: Vec<_> = left
            .iter()
            .filter(|x| !right.contains(x))
            .chain(right.iter().filter(|x| !left.contains(x)))
            .collect();
        // Parent list WD establishes pairwise distinctness in each listed set.
        if expected.len() == result.len() && result.iter().all(|x| expected.contains(&x)) {
            return Some(SymDiffFiniteRationalsProof {
                left_values: left,
                right_values: right,
                result_values: result,
            });
        }
    }
    None
}
