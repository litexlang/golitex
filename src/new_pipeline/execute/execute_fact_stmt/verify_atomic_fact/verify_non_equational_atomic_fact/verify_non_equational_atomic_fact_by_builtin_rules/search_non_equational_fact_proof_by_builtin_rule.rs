use crate::new_pipeline::ast::fact::{
    AtomicFact, FnEqualFact, FnEqualInFact, NormalAtomicFact, NotGreaterEqualFact, NotGreaterFact,
    NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsSetFact, NotIsTupleFact, NotLessEqualFact,
    NotLessFact, NotNormalAtomicFact, NotSubsetFact, NotSupersetFact,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::search_non_equational_fact_proof_by_builtin_rule_result::{
    FnEqualFactSearchProofByBuiltinRule, FnEqualInFactSearchProofByBuiltinRule,
    NonEquationalAtomicFactSearchProofByBuiltinRule, NormalAtomicFactSearchProofByBuiltinRule,
    NotGreaterEqualFactSearchProofByBuiltinRule, NotGreaterFactSearchProofByBuiltinRule,
    NotInFactSearchProofByBuiltinRule, NotIsCartFactSearchProofByBuiltinRule,
    NotIsFiniteSetFactSearchProofByBuiltinRule, NotIsSetFactSearchProofByBuiltinRule,
    NotIsTupleFactSearchProofByBuiltinRule, NotLessEqualFactSearchProofByBuiltinRule,
    NotLessFactSearchProofByBuiltinRule, NotNormalAtomicFactSearchProofByBuiltinRule,
    NotSubsetFactSearchProofByBuiltinRule, NotSupersetFactSearchProofByBuiltinRule,
};

impl Runtime {
    pub fn search_non_equational_fact_proof_by_builtin_rule(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinRule>> {
        match fact {
            AtomicFact::EqualFact(_) => unreachable!(
                "equality facts use the equality search pipeline, not non-equational builtin rules"
            ),
            AtomicFact::NormalAtomicFact(fact) => Ok(self
                .search_normal_atomic_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NormalAtomicFact)),
            AtomicFact::LessFact(fact) => Ok(self
                .search_less_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::LessFact)),
            AtomicFact::GreaterFact(fact) => Ok(self
                .search_greater_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::GreaterFact)),
            AtomicFact::LessEqualFact(fact) => Ok(self
                .search_less_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::LessEqualFact)),
            AtomicFact::GreaterEqualFact(fact) => Ok(self
                .search_greater_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::GreaterEqualFact)),
            AtomicFact::IsSetFact(fact) => Ok(self
                .search_is_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::IsSetFact)),
            AtomicFact::IsNonemptySetFact(fact) => Ok(self
                .search_is_nonempty_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::IsNonemptySetFact)),
            AtomicFact::IsFiniteSetFact(fact) => Ok(self
                .search_is_finite_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::IsFiniteSetFact)),
            AtomicFact::InFact(fact) => Ok(self
                .search_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::InFact)),
            AtomicFact::IsCartFact(fact) => Ok(self
                .search_is_cart_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::IsCartFact)),
            AtomicFact::IsTupleFact(fact) => Ok(self
                .search_is_tuple_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::IsTupleFact)),
            AtomicFact::SubsetFact(fact) => Ok(self
                .search_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::SubsetFact)),
            AtomicFact::SupersetFact(fact) => Ok(self
                .search_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::SupersetFact)),
            AtomicFact::NotNormalAtomicFact(fact) => Ok(self
                .search_not_normal_atomic_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotNormalAtomicFact)),
            AtomicFact::NotEqualFact(fact) => Ok(self
                .search_not_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotEqualFact)),
            AtomicFact::NotLessFact(fact) => Ok(self
                .search_not_less_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotLessFact)),
            AtomicFact::NotGreaterFact(fact) => Ok(self
                .search_not_greater_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotGreaterFact)),
            AtomicFact::NotLessEqualFact(fact) => Ok(self
                .search_not_less_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotLessEqualFact)),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(self
                .search_not_greater_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotGreaterEqualFact)),
            AtomicFact::NotIsSetFact(fact) => Ok(self
                .search_not_is_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotIsSetFact)),
            AtomicFact::NotIsNonemptySetFact(fact) => Ok(self
                .search_not_is_nonempty_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotIsNonemptySetFact)),
            AtomicFact::NotIsFiniteSetFact(fact) => Ok(self
                .search_not_is_finite_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotIsFiniteSetFact)),
            AtomicFact::NotInFact(fact) => Ok(self
                .search_not_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotInFact)),
            AtomicFact::NotIsCartFact(fact) => Ok(self
                .search_not_is_cart_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotIsCartFact)),
            AtomicFact::NotIsTupleFact(fact) => Ok(self
                .search_not_is_tuple_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotIsTupleFact)),
            AtomicFact::NotSubsetFact(fact) => Ok(self
                .search_not_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotSubsetFact)),
            AtomicFact::NotSupersetFact(fact) => Ok(self
                .search_not_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::NotSupersetFact)),
            AtomicFact::FnEqualInFact(fact) => Ok(self
                .search_fn_equal_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::FnEqualInFact)),
            AtomicFact::FnEqualFact(fact) => Ok(self
                .search_fn_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(NonEquationalAtomicFactSearchProofByBuiltinRule::FnEqualFact)),
        }
    }

    pub fn search_normal_atomic_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NormalAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NormalAtomicFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_normal_atomic_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotNormalAtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotNormalAtomicFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotLessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotLessFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_greater_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotGreaterFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotGreaterFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_less_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotLessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotLessEqualFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_greater_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotGreaterEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotGreaterEqualFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_is_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotIsSetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsSetFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_is_finite_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotIsFiniteSetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsFiniteSetFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_is_cart_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotIsCartFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsCartFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_is_tuple_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotIsTupleFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsTupleFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_subset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotSubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSubsetFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_not_superset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotSupersetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSupersetFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_fn_equal_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &FnEqualInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FnEqualInFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_fn_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &FnEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FnEqualFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
