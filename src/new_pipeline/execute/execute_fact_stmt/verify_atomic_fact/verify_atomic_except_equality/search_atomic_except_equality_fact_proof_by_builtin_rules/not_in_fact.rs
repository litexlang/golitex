use crate::new_pipeline::ast::fact::{AtomicFact, Fact, NotEqualFact, NotInFact};
use crate::new_pipeline::ast::obj::{Obj, SetFormer, SetOperator, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::normalized_decimal_inhabits_standard_set;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not x $in S` (zero-premise or subgoal routes).
pub enum NotInFactSearchProofByBuiltinRule {
    // Closed numeric non-membership by decimal evaluation.
    // Mathematical property: a closed expression that evaluates to a normalized
    // decimal outside the target standard set is not a member.
    // Examples: `not (-1) $in N`, `not 0 $in N+`, `not 1.5 $in Z`.
    ClosedNumericNonMembership(ClosedNumericNonMembershipBuiltinRuleProof),
    // Finite list-set non-membership by inequality to every listed element.
    // Mathematical property: if `x != a_i` for every `a_i` in `{a_1, …, a_n}`,
    // then `not x $in {a_1, …, a_n}`.
    // Example: `not 4 $in {1, 2, 3}`.
    ListSetExhaustiveDisequality(ListSetExhaustiveDisequalityBuiltinRuleProof),
    // Intersection non-membership from the left factor.
    // Mathematical property: `not x $in A` ⇒ `not x $in intersect(A, B)`.
    // Example: prove `not 1 $in intersect({2}, {1, 2})` from `not 1 $in {2}`.
    NonMembershipOfIntersectFromLeft(NonMembershipOfIntersectFromLeftBuiltinRuleProof),
    // Intersection non-membership from the right factor.
    // Mathematical property: `not x $in B` ⇒ `not x $in intersect(A, B)`.
    // Example: prove `not 1 $in intersect({1, 2}, {2})` from `not 1 $in {2}`.
    NonMembershipOfIntersectFromRight(NonMembershipOfIntersectFromRightBuiltinRuleProof),
    // Union non-membership from both sides.
    // Mathematical property: `not x $in A` and `not x $in B` ⇒
    // `not x $in union(A, B)`.
    // Example: `not 0 $in {1}` and `not 0 $in {2}` prove `not 0 $in union({1}, {2})`.
    NonMembershipOfUnion(NonMembershipOfUnionBuiltinRuleProof),
}

pub struct ClosedNumericNonMembershipBuiltinRuleProof {
    pub normal: String,
}

pub struct ListSetExhaustiveDisequalityBuiltinRuleProof {
    pub disequality_proofs: Vec<VerifyFactResult>,
}

pub struct NonMembershipOfIntersectFromLeftBuiltinRuleProof {
    pub left_non_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfIntersectFromRightBuiltinRuleProof {
    pub right_non_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfUnionBuiltinRuleProof {
    pub left_non_membership_proof: VerifyFactResult,
    pub right_non_membership_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin NotIn: closed numeric, list-set exhaustion, then intersect/union algebra.
    pub fn search_not_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::StandardSet(_) => Ok(closed_numeric_non_membership_proof(fact)),
            Obj::SetFormer(SetFormer::ListSet(_)) => {
                self.list_set_exhaustive_disequality_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::Intersect(_)) => {
                self.intersect_non_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::Union(_)) => {
                self.union_non_membership_proof(fact, verify_state)
            }
            _ => Ok(None),
        }
    }

    fn list_set_exhaustive_disequality_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::ListSet(list_set)) = &fact.set else {
            return Ok(None);
        };
        let mut disequality_proofs = Vec::with_capacity(list_set.list.len());
        for listed in &list_set.list {
            let disequality = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: listed.as_ref().clone(),
                line_file: None,
            }));
            let proof = self.verify_fact(&disequality, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            disequality_proofs.push(proof);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::ListSetExhaustiveDisequality(
                ListSetExhaustiveDisequalityBuiltinRuleProof {
                    disequality_proofs,
                },
            ),
        ))
    }

    fn intersect_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Intersect(intersect)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: intersect.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if !left_proof.is_failed() {
            return Ok(Some(
                NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromLeft(
                    NonMembershipOfIntersectFromLeftBuiltinRuleProof {
                        left_non_membership_proof: left_proof,
                    },
                ),
            ));
        }
        let right_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: intersect.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromRight(
                NonMembershipOfIntersectFromRightBuiltinRuleProof {
                    right_non_membership_proof: right_proof,
                },
            ),
        ))
    }

    fn union_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Union(union)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: union.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_fact(&left_goal, verify_state.clone())?;
        if left_proof.is_failed() {
            return Ok(None);
        }
        let right_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: union.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_fact(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(NotInFactSearchProofByBuiltinRule::NonMembershipOfUnion(
            NonMembershipOfUnionBuiltinRuleProof {
                left_non_membership_proof: left_proof,
                right_non_membership_proof: right_proof,
            },
        )))
    }
}

fn closed_numeric_non_membership_proof(
    fact: &NotInFact,
) -> Option<NotInFactSearchProofByBuiltinRule> {
    let number = evaluate_obj_to_normalized_decimal_number(&fact.element)?;
    let Obj::StandardSet(set) = &fact.set else {
        return None;
    };
    // C / R / Q contain every real decimal; non-membership cannot fire there.
    if matches!(set, StandardSet::C | StandardSet::R | StandardSet::Q) {
        return None;
    }
    if normalized_decimal_inhabits_standard_set(&number.normalized_value, set) {
        return None;
    }
    Some(
        NotInFactSearchProofByBuiltinRule::ClosedNumericNonMembership(
            ClosedNumericNonMembershipBuiltinRuleProof {
                normal: number.normalized_value,
            },
        ),
    )
}
