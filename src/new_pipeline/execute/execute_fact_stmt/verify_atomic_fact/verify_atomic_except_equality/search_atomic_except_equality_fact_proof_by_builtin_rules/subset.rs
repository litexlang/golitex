use crate::new_pipeline::ast::fact::SubsetFact;
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Standard number sets form a fixed inclusion chain.
// Example: prove `N $subset R`, `Z $subset Q`.
//
// Elementary set containments follow from membership definitions.
// Example: prove `intersect(A, B) $subset A`, `A $subset union(A, B)`.
//
// Finite and one-sided real intervals are subsets of R.
// Example: prove `'[a, b] $subset R`, `'[a,) $subset R`.
//
// Every set is a subset of itself.
// Example: prove `A $subset A`.
pub enum SubsetFactSearchProofByBuiltinRule {
    StandardSetSubset(StandardSetSubsetBuiltinRuleProof),
    ElementarySetSubset(ElementarySetSubsetBuiltinRuleProof),
    RealIntervalSubsetReal(RealIntervalSubsetRealBuiltinRuleProof),
    SubsetReflexivity(SubsetReflexivityBuiltinRuleProof),
}

pub struct StandardSetSubsetBuiltinRuleProof {
    pub left: StandardSet,
    pub right: StandardSet,
}

pub enum ElementarySetSubsetKind {
    IntersectSubsetLeft,
    IntersectSubsetRight,
    SubsetUnionLeft,
    SubsetUnionRight,
    SetMinusSubsetLeft,
}

pub struct ElementarySetSubsetBuiltinRuleProof {
    pub kind: ElementarySetSubsetKind,
}

pub struct RealIntervalSubsetRealBuiltinRuleProof {}

pub struct SubsetReflexivityBuiltinRuleProof {}

impl Runtime {
    // Builtin: zero-premise subset rules for standard sets, elementary
    // constructors, real intervals, and reflexivity.
    // Example: prove `N $subset R`, `intersect(A, B) $subset A`, `'[a, b] $subset R`.
    pub fn search_subset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let _ = verify_state;
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) = (&fact.left, &fact.right) {
            if standard_set_is_subset_eq(left, right) {
                return Ok(Some(SubsetFactSearchProofByBuiltinRule::StandardSetSubset(
                    StandardSetSubsetBuiltinRuleProof {
                        left: left.clone(),
                        right: right.clone(),
                    },
                )));
            }
        }

        if let Some(kind) = elementary_set_subset_kind(&fact.left, &fact.right) {
            return Ok(Some(
                SubsetFactSearchProofByBuiltinRule::ElementarySetSubset(
                    ElementarySetSubsetBuiltinRuleProof { kind },
                ),
            ));
        }

        if matches!(
            &fact.left,
            Obj::IntervalObj(_) | Obj::OneSideInfinityIntervalObj(_)
        ) && matches!(&fact.right, Obj::StandardSet(StandardSet::R))
        {
            return Ok(Some(
                SubsetFactSearchProofByBuiltinRule::RealIntervalSubsetReal(
                    RealIntervalSubsetRealBuiltinRuleProof {},
                ),
            ));
        }

        if fact.left == fact.right {
            return Ok(Some(SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(
                SubsetReflexivityBuiltinRuleProof {},
            )));
        }

        Ok(None)
    }
}

pub(super) fn standard_set_is_subset_eq(left: &StandardSet, right: &StandardSet) -> bool {
    matches!(
        (left, right),
        (_, StandardSet::C)
            | (StandardSet::NPos, StandardSet::NPos)
            | (StandardSet::NPos, StandardSet::N)
            | (StandardSet::NPos, StandardSet::Z)
            | (StandardSet::NPos, StandardSet::Q)
            | (StandardSet::NPos, StandardSet::R)
            | (StandardSet::NPos, StandardSet::QPos)
            | (StandardSet::NPos, StandardSet::RPos)
            | (StandardSet::NPos, StandardSet::ZStar)
            | (StandardSet::NPos, StandardSet::QStar)
            | (StandardSet::NPos, StandardSet::RStar)
            | (StandardSet::N, StandardSet::N)
            | (StandardSet::N, StandardSet::Z)
            | (StandardSet::N, StandardSet::Q)
            | (StandardSet::N, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::ZNeg)
            | (StandardSet::ZNeg, StandardSet::Z)
            | (StandardSet::ZNeg, StandardSet::Q)
            | (StandardSet::ZNeg, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::QNeg)
            | (StandardSet::ZNeg, StandardSet::RNeg)
            | (StandardSet::ZNeg, StandardSet::ZStar)
            | (StandardSet::ZNeg, StandardSet::QStar)
            | (StandardSet::ZNeg, StandardSet::RStar)
            | (StandardSet::ZStar, StandardSet::ZStar)
            | (StandardSet::ZStar, StandardSet::Z)
            | (StandardSet::ZStar, StandardSet::Q)
            | (StandardSet::ZStar, StandardSet::R)
            | (StandardSet::ZStar, StandardSet::QStar)
            | (StandardSet::ZStar, StandardSet::RStar)
            | (StandardSet::Z, StandardSet::Z)
            | (StandardSet::Z, StandardSet::Q)
            | (StandardSet::Z, StandardSet::R)
            | (StandardSet::QPos, StandardSet::QPos)
            | (StandardSet::QPos, StandardSet::Q)
            | (StandardSet::QPos, StandardSet::R)
            | (StandardSet::QPos, StandardSet::RPos)
            | (StandardSet::QPos, StandardSet::QStar)
            | (StandardSet::QPos, StandardSet::RStar)
            | (StandardSet::QNeg, StandardSet::QNeg)
            | (StandardSet::QNeg, StandardSet::Q)
            | (StandardSet::QNeg, StandardSet::R)
            | (StandardSet::QNeg, StandardSet::RNeg)
            | (StandardSet::QNeg, StandardSet::QStar)
            | (StandardSet::QNeg, StandardSet::RStar)
            | (StandardSet::QStar, StandardSet::QStar)
            | (StandardSet::QStar, StandardSet::Q)
            | (StandardSet::QStar, StandardSet::R)
            | (StandardSet::QStar, StandardSet::RStar)
            | (StandardSet::Q, StandardSet::Q)
            | (StandardSet::Q, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RPos)
            | (StandardSet::RPos, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RStar)
            | (StandardSet::RNeg, StandardSet::RNeg)
            | (StandardSet::RNeg, StandardSet::R)
            | (StandardSet::RNeg, StandardSet::RStar)
            | (StandardSet::RStar, StandardSet::RStar)
            | (StandardSet::RStar, StandardSet::R)
            | (StandardSet::NPos, StandardSet::CStar)
            | (StandardSet::ZNeg, StandardSet::CStar)
            | (StandardSet::ZStar, StandardSet::CStar)
            | (StandardSet::QPos, StandardSet::CStar)
            | (StandardSet::QNeg, StandardSet::CStar)
            | (StandardSet::QStar, StandardSet::CStar)
            | (StandardSet::RPos, StandardSet::CStar)
            | (StandardSet::RNeg, StandardSet::CStar)
            | (StandardSet::RStar, StandardSet::CStar)
            | (StandardSet::CStar, StandardSet::CStar)
            | (StandardSet::R, StandardSet::R)
    )
}

fn elementary_set_subset_kind(left: &Obj, right: &Obj) -> Option<ElementarySetSubsetKind> {
    match (left, right) {
        (Obj::Intersect(intersect), right) if intersect.left.as_ref() == right => {
            Some(ElementarySetSubsetKind::IntersectSubsetLeft)
        }
        (Obj::Intersect(intersect), right) if intersect.right.as_ref() == right => {
            Some(ElementarySetSubsetKind::IntersectSubsetRight)
        }
        (left, Obj::Union(union)) if union.left.as_ref() == left => {
            Some(ElementarySetSubsetKind::SubsetUnionLeft)
        }
        (left, Obj::Union(union)) if union.right.as_ref() == left => {
            Some(ElementarySetSubsetKind::SubsetUnionRight)
        }
        (Obj::SetMinus(set_minus), right) if set_minus.left.as_ref() == right => {
            Some(ElementarySetSubsetKind::SetMinusSubsetLeft)
        }
        _ => None,
    }
}
