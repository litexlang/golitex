use crate::ast::fact::{
    AtomicFact, Fact, IsFiniteSetFact, NotIsFiniteSetFact,
};
use crate::ast::obj::{Obj, SetOperator, SetMinus};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not $is_finite_set(...)`.
pub enum NotIsFiniteSetFactSearchProofByBuiltinRule {
    // Standard infinite carriers are infinite.
    // Mathematical property: every standard number set (N, Z, Q, R, C, and signed/star variants)
    // is infinite.
    // Example: `not $is_finite_set(N)`.
    StandardInfiniteSet(StandardInfiniteSetBuiltinRuleProof),
    // Removing a finite set from an infinite set stays infinite.
    // Mathematical property: if `A` is infinite and `B` is finite, then `set_minus(A, B)` is infinite.
    // Example: known `not $is_finite_set(N)` and `$is_finite_set({1})` prove
    // `not $is_finite_set(set_minus(N, {1}))`.
    SetMinusInfiniteOfInfiniteFinite(SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof),
}

pub struct StandardInfiniteSetBuiltinRuleProof {}

pub struct SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof {
    pub left_infinite_proof: VerifyFactResult,
    pub right_finite_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin search for `not $is_finite_set(S)`.
    // Shapes: standard infinite carriers; or `S = set_minus(A, B)` with `A` infinite and `B` finite.
    // Example: prove `not $is_finite_set(N)` and `not $is_finite_set(set_minus(N, {0}))`.
    pub fn search_not_is_finite_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotIsFiniteSetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsFiniteSetFactSearchProofByBuiltinRule>> {
        if matches!(fact.set, Obj::StandardSet(_)) {
            return Ok(Some(
                NotIsFiniteSetFactSearchProofByBuiltinRule::StandardInfiniteSet(
                    StandardInfiniteSetBuiltinRuleProof {},
                ),
            ));
        }

        let Obj::SetOperator(SetOperator::SetMinus(SetMinus { left, right })) = &fact.set else {
            return Ok(None);
        };

        let left_goal = Fact::AtomicFact(AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: left.as_ref().clone(),
            line_file: None,
        }));
        let left_infinite_proof = self.verify_builtin_rule_premise(&left_goal, verify_state.clone())?;
        if left_infinite_proof.is_failed() {
            return Ok(None);
        }

        let right_goal = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: right.as_ref().clone(),
            line_file: None,
        }));
        let right_finite_proof = self.verify_builtin_rule_premise(&right_goal, verify_state)?;
        if right_finite_proof.is_failed() {
            return Ok(None);
        }

        Ok(Some(
            NotIsFiniteSetFactSearchProofByBuiltinRule::SetMinusInfiniteOfInfiniteFinite(
                SetMinusInfiniteOfInfiniteFiniteBuiltinRuleProof {
                    left_infinite_proof,
                    right_finite_proof,
                },
            ),
        ))
    }
}
