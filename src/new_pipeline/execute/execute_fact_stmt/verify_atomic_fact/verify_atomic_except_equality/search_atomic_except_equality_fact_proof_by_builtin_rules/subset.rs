use crate::new_pipeline::ast::fact::{AtomicFact, Fact, InFact, SubsetFact};
use crate::new_pipeline::ast::obj::{Obj, StandardSet, SetFormer, SetOperator};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
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
    // `{x S: P…} $subset S` — a set-builder is a subset of its parameter set.
    // Example: `{x R: x > 0} $subset R`.
    SetBuilderSubsetOfParamSet(SetBuilderSubsetOfParamSetBuiltinRuleProof),
    // `A $subset S` and `B $subset S` ⇒ `union(A, B) $subset S`.
    // Mathematical property: binary union is the least upper bound of its operands.
    // Example: known `{1} $subset N` and `{2} $subset N` prove `union({1}, {2}) $subset N`.
    UnionSubsetFromBothOperands(UnionSubsetFromBothOperandsBuiltinRuleProof),
    // `A $subset S` ⇒ `intersect(A, B) $subset S`.
    // Mathematical property: intersection is below each operand, so any upper bound of
    // the left operand is an upper bound of the intersection.
    // Example: known `{1, 2} $subset N` proves `intersect({1, 2}, {2, 3}) $subset N`.
    IntersectSubsetFromLeftUpperBound(IntersectSubsetFromLeftUpperBoundBuiltinRuleProof),
    // `B $subset S` ⇒ `intersect(A, B) $subset S`.
    // Mathematical property: dual of IntersectSubsetFromLeftUpperBound on the right operand.
    // Example: known `{2, 3} $subset N` proves `intersect({1, 2}, {2, 3}) $subset N`.
    IntersectSubsetFromRightUpperBound(IntersectSubsetFromRightUpperBoundBuiltinRuleProof),
    // `{a1, …, an} $subset S` from each `ai $in S` (empty list is vacuously true).
    // Mathematical property: a finite enumeration is contained in S iff every listed member is.
    // Example: `1 $in N` and `2 $in N` prove `{1, 2} $subset N`.
    ListSetSubsetFromMembers(ListSetSubsetFromMembersBuiltinRuleProof),
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

pub struct SetBuilderSubsetOfParamSetBuiltinRuleProof {}

pub struct UnionSubsetFromBothOperandsBuiltinRuleProof {
    pub left_operand_subset_proof: VerifyFactResult,
    pub right_operand_subset_proof: VerifyFactResult,
}

pub struct IntersectSubsetFromLeftUpperBoundBuiltinRuleProof {
    pub left_operand_subset_proof: VerifyFactResult,
}

pub struct IntersectSubsetFromRightUpperBoundBuiltinRuleProof {
    pub right_operand_subset_proof: VerifyFactResult,
}

pub struct ListSetSubsetFromMembersBuiltinRuleProof {
    pub member_in_proofs: Vec<VerifyFactResult>,
}

impl Runtime {
    // Builtin: zero-premise subset rules, then union/intersect from operand upper bounds.
    // Example: prove `N $subset R`, `intersect(A, B) $subset A`, `'[a, b] $subset R`,
    // `{x R: x > 0} $subset R`, `union(A, B) $subset S` from `A,B $subset S`.
    pub fn search_subset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
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
            Obj::SetFormer(SetFormer::IntervalObj(_)) | Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_))
        ) && matches!(&fact.right, Obj::StandardSet(StandardSet::R))
        {
            return Ok(Some(
                SubsetFactSearchProofByBuiltinRule::RealIntervalSubsetReal(
                    RealIntervalSubsetRealBuiltinRuleProof {},
                ),
            ));
        }

        if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &fact.left {
            if builder.param_set.as_ref().ir() == fact.right.ir() {
                return Ok(Some(
                    SubsetFactSearchProofByBuiltinRule::SetBuilderSubsetOfParamSet(
                        SetBuilderSubsetOfParamSetBuiltinRuleProof {},
                    ),
                ));
            }
        }

        if fact.left == fact.right {
            return Ok(Some(SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(
                SubsetReflexivityBuiltinRuleProof {},
            )));
        }

        if let Some(proof) = self.list_set_subset_from_members_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.union_subset_from_both_operands_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.intersect_subset_from_left_upper_bound_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.intersect_subset_from_right_upper_bound_proof(fact, verify_state)?
        {
            return Ok(Some(proof));
        }

        Ok(None)
    }

    // `{a1, …, an} $subset S` from each `ai $in S`.
    fn list_set_subset_from_members_proof(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::ListSet(list_set)) = &fact.left else {
            return Ok(None);
        };
        let mut member_in_proofs = Vec::with_capacity(list_set.list.len());
        for element in &list_set.list {
            let premise = in_fact(element.as_ref(), &fact.right, self);
            let proof = self.verify_fact(&premise, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            member_in_proofs.push(proof);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::ListSetSubsetFromMembers(
                ListSetSubsetFromMembersBuiltinRuleProof { member_in_proofs },
            ),
        ))
    }

    // `A $subset S` and `B $subset S` ⇒ `union(A, B) $subset S`.
    fn union_subset_from_both_operands_proof(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Union(union)) = &fact.left else {
            return Ok(None);
        };
        let left_premise = subset_fact(union.left.as_ref(), &fact.right, self);
        let left_operand_subset_proof = self.verify_fact(&left_premise, verify_state.clone())?;
        if left_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        let right_premise = subset_fact(union.right.as_ref(), &fact.right, self);
        let right_operand_subset_proof = self.verify_fact(&right_premise, verify_state)?;
        if right_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::UnionSubsetFromBothOperands(
                UnionSubsetFromBothOperandsBuiltinRuleProof {
                    left_operand_subset_proof,
                    right_operand_subset_proof,
                },
            ),
        ))
    }

    // `A $subset S` ⇒ `intersect(A, B) $subset S`.
    fn intersect_subset_from_left_upper_bound_proof(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Intersect(intersect)) = &fact.left else {
            return Ok(None);
        };
        let premise = subset_fact(intersect.left.as_ref(), &fact.right, self);
        let left_operand_subset_proof = self.verify_fact(&premise, verify_state)?;
        if left_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromLeftUpperBound(
                IntersectSubsetFromLeftUpperBoundBuiltinRuleProof {
                    left_operand_subset_proof,
                },
            ),
        ))
    }

    // `B $subset S` ⇒ `intersect(A, B) $subset S`.
    fn intersect_subset_from_right_upper_bound_proof(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Intersect(intersect)) = &fact.left else {
            return Ok(None);
        };
        let premise = subset_fact(intersect.right.as_ref(), &fact.right, self);
        let right_operand_subset_proof = self.verify_fact(&premise, verify_state)?;
        if right_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromRightUpperBound(
                IntersectSubsetFromRightUpperBoundBuiltinRuleProof {
                    right_operand_subset_proof,
                },
            ),
        ))
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
        (Obj::SetOperator(SetOperator::Intersect(intersect)), right) if intersect.left.as_ref() == right => {
            Some(ElementarySetSubsetKind::IntersectSubsetLeft)
        }
        (Obj::SetOperator(SetOperator::Intersect(intersect)), right) if intersect.right.as_ref() == right => {
            Some(ElementarySetSubsetKind::IntersectSubsetRight)
        }
        (left, Obj::SetOperator(SetOperator::Union(union))) if union.left.as_ref() == left => {
            Some(ElementarySetSubsetKind::SubsetUnionLeft)
        }
        (left, Obj::SetOperator(SetOperator::Union(union))) if union.right.as_ref() == left => {
            Some(ElementarySetSubsetKind::SubsetUnionRight)
        }
        (Obj::SetOperator(SetOperator::SetMinus(set_minus)), right) if set_minus.left.as_ref() == right => {
            Some(ElementarySetSubsetKind::SetMinusSubsetLeft)
        }
        _ => None,
    }
}

fn subset_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

fn in_fact(element: &Obj, set: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::InFact(InFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        element: element.clone(),
        set: set.clone(),
        line_file: None,
    }))
}
