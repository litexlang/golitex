use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    atomic_except_equality_fact_result_from_search_fail,
    atomic_except_equality_fact_result_from_success,
    atomic_except_equality_fact_result_from_wd_fail,
    AtomicExceptEqualityFactSearchedProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail, EqualFactSearchedProof,
};
use crate::execute::execute_fact_stmt::{
    VerifyAtomicFactWellDefinedResult, VerifyEqualFactWellDefinedResult,
    VerifyFactResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::rational_expression::compare_closed_numeric_objs;

impl Runtime {
    // Premise WD keeps the caller's permissions; truth cannot reopen ordinary
    // builtin/deep/rewrite search. One permitted parent may use the same direct
    // calculation / known-citation leaves as a zero-depth strategy.
    pub(crate) fn verify_builtin_rule_premise(
        &mut self,
        premise: &Fact,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let wd_state = state.without_well_defined_storage();
        self.verify_builtin_rule_premise_with_wd_state(premise, state, wd_state)
    }

    pub(crate) fn verify_builtin_rule_premise_with_wd_state(
        &mut self,
        premise: &Fact,
        state: VerifyState,
        wd_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let child = state.after_builtin_rule();
        match premise {
            Fact::AtomicFact(AtomicFact::EqualFact(fact)) => {
                let wd = match self.verify_equal_fact_well_definedness(fact, wd_state)? {
                    VerifyEqualFactWellDefinedResult::Success(proof) => proof,
                    VerifyEqualFactWellDefinedResult::Failed(reason) => {
                        return Ok(equal_fact_result_from_wd_fail(reason));
                    }
                };
                if let Some(proof) = self.search_equal_fact_proof(fact, child.clone())? {
                    return Ok(equal_fact_result_from_success(fact, wd, proof));
                }
                if state.can_use_builtin_rule {
                    if let Some(proof) =
                        self.search_builtin_premise_application_equality(fact, state.clone())?
                    {
                        return Ok(equal_fact_result_from_success(
                            fact,
                            wd,
                            EqualFactSearchedProof::ByObjectDefinition(proof),
                        ));
                    }
                }
                let proof = if state.can_use_builtin_rule {
                    self.search_equal_fact_builtin_rule(fact, child)?
                } else {
                    self.search_equal_fact_by_calculation(fact, child)?
                        .map(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByBuiltinRule::Calculation)
                };
                if let Some(proof) = proof {
                    return Ok(equal_fact_result_from_success(
                        fact,
                        wd,
                        EqualFactSearchedProof::ByBuiltinRule(proof),
                    ));
                }
                Ok(equal_fact_result_from_search_fail(fact, wd))
            }
            Fact::AtomicFact(fact) => {
                let wd = match self.verify_atomic_fact_well_definedness(fact, wd_state)? {
                    VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
                    VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                        return Ok(atomic_except_equality_fact_result_from_wd_fail(reason));
                    }
                };
                if let Some(proof) =
                    self.search_atomic_except_equality_fact_proof_by_known(fact, child.clone())?
                {
                    return Ok(atomic_except_equality_fact_result_from_success(
                        fact, wd, proof,
                    ));
                }
                if state.can_use_builtin_rule || is_closed_numeric_premise(fact) {
                    if let Some(proof) =
                        self.search_atomic_except_equality_fact_proof_by_builtin_rule(fact, child)?
                    {
                        return Ok(atomic_except_equality_fact_result_from_success(
                            fact,
                            wd,
                            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(proof),
                        ));
                    }
                }
                Ok(atomic_except_equality_fact_result_from_search_fail(
                    fact, wd,
                ))
            }
            _ => self.verify_fact(premise, child),
        }
    }
}

// These owner dispatchers decide closed comparisons and standard-set numeric
// membership by evaluation, before any branch that generates another premise.
fn is_closed_numeric_premise(fact: &AtomicFact) -> bool {
    let sides = match fact {
        AtomicFact::LessFact(f) => Some((&f.left, &f.right)),
        AtomicFact::LessEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::GreaterFact(f) => Some((&f.left, &f.right)),
        AtomicFact::GreaterEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::NotLessFact(f) => Some((&f.left, &f.right)),
        AtomicFact::NotLessEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::NotGreaterFact(f) => Some((&f.left, &f.right)),
        AtomicFact::NotGreaterEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::NotEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::InFact(f) if matches!(f.set, Obj::StandardSet(_)) => {
            Some((&f.element, &f.element))
        }
        AtomicFact::NotInFact(f) if matches!(f.set, Obj::StandardSet(_)) => {
            Some((&f.element, &f.element))
        }
        _ => None,
    };
    sides.is_some_and(|(left, right)| {
        compare_closed_numeric_objs(left, right).is_some()
    })
}
