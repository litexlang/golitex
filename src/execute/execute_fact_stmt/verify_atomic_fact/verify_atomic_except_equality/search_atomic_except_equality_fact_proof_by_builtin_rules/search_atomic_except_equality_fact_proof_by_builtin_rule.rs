use crate::ast::fact::{
    AtomicFact, NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsSetFact, NotIsTupleFact,
    NotSubsetFact, NotSupersetFact,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

use super::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    AtomicExceptEqualityFactSearchProofByBuiltinRule, NotInFactSearchProofByBuiltinRule,
    NotIsCartFactSearchProofByBuiltinRule, NotIsFiniteSetFactSearchProofByBuiltinRule,
    NotIsSetFactSearchProofByBuiltinRule, NotIsTupleFactSearchProofByBuiltinRule,
};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_builtin_rule(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinRule>> {
        match fact {
            AtomicFact::EqualFact(_) => unreachable!(
                "equality facts use the equality search pipeline, not atomic-except-equality builtin rules"
            ),
            AtomicFact::NormalAtomicFact(fact) => Ok(self
                .search_normal_atomic_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact)),
            AtomicFact::LessFact(fact) => Ok(self
                .search_less_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact)),
            AtomicFact::GreaterFact(fact) => Ok(self
                .search_greater_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact)),
            AtomicFact::LessEqualFact(fact) => Ok(self
                .search_less_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact)),
            AtomicFact::GreaterEqualFact(fact) => Ok(self
                .search_greater_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact)),
            AtomicFact::IsSetFact(fact) => Ok(self
                .search_is_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact)),
            AtomicFact::IsNonemptySetFact(fact) => Ok(self
                .search_is_nonempty_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact)),
            AtomicFact::IsFiniteSetFact(fact) => Ok(self
                .search_is_finite_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact)),
            AtomicFact::InFact(fact) => Ok(self
                .search_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact)),
            AtomicFact::IsCartFact(fact) => Ok(self
                .search_is_cart_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsCartFact)),
            AtomicFact::IsTupleFact(fact) => Ok(self
                .search_is_tuple_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsTupleFact)),
            AtomicFact::SubsetFact(fact) => Ok(self
                .search_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact)),
            AtomicFact::SupersetFact(fact) => Ok(self
                .search_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact)),
            AtomicFact::NotNormalAtomicFact(fact) => Ok(self
                .search_not_normal_atomic_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact)),
            AtomicFact::NotEqualFact(fact) => Ok(self
                .search_not_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact)),
            AtomicFact::NotLessFact(fact) => Ok(self
                .search_not_less_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact)),
            AtomicFact::NotGreaterFact(fact) => Ok(self
                .search_not_greater_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact)),
            AtomicFact::NotLessEqualFact(fact) => Ok(self
                .search_not_less_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact)),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(self
                .search_not_greater_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact)),
            AtomicFact::NotIsSetFact(fact) => Ok(self
                .search_not_is_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact)),
            AtomicFact::NotIsNonemptySetFact(fact) => Ok(self
                .search_not_is_nonempty_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact)),
            AtomicFact::NotIsFiniteSetFact(fact) => Ok(self
                .search_not_is_finite_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact)),
            AtomicFact::NotInFact(fact) => Ok(self
                .search_not_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact)),
            AtomicFact::NotIsCartFact(fact) => Ok(self
                .search_not_is_cart_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsCartFact)),
            AtomicFact::NotIsTupleFact(fact) => Ok(self
                .search_not_is_tuple_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsTupleFact)),
            AtomicFact::NotSubsetFact(fact) => Ok(self
                .search_not_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact)),
            AtomicFact::NotSupersetFact(fact) => Ok(self
                .search_not_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact)),
        }
    }

    pub fn search_not_is_set_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotIsSetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsSetFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_is_cart_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotIsCartFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsCartFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_is_tuple_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotIsTupleFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsTupleFactSearchProofByBuiltinRule>> {
        Ok(None)
    }
}
