//! Central dispatch from a fact shape to its verifier.

use crate::error::{
    RuntimeError, RuntimeErrorOutput, RuntimeErrorStruct, UnknownRuntimeError, VerifyRuntimeError,
};
use crate::fact::{AndChainAtomicFact, ExistOrAndChainAtomicFact, Fact, QuantifierFreeFact};
use crate::result::{
    ProveFactResult, UnknownFactResult, UnknownVerifyFactResult, VerifiedFactResult,
    VerifyFactResult,
};
use crate::runtime::Runtime;
use crate::verification::VerifyState;
use std::rc::Rc;

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        fact: &crate::fact::AndFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    pub fn verify_chain_fact(
        &mut self,
        fact: &crate::fact::ChainFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    pub fn verify_or_fact(
        &mut self,
        fact: &crate::fact::OrFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    pub fn verify_exist_fact(
        &mut self,
        fact: &crate::fact::ExistFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    pub fn verify_forall_fact(
        &mut self,
        fact: &crate::fact::ForallFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    pub fn verify_forall_fact_with_iff(
        &mut self,
        fact: &crate::fact::ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    pub fn verify_not_forall_fact(
        &mut self,
        fact: &crate::fact::NotForallFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }

    /// Full fact verification used for user proof obligations.
    ///
    /// This path may use the full verifier stack for the fact shape, including
    /// known forall instantiation, user strategies, definitions, and recursive
    /// proof obligations where those features are part of the ordinary proof
    /// model. Restricted builtin premises use the atomic builtin helpers.
    pub fn verify_fact_allow_unknown(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let checked = self.verify_fact_well_defined_result(fact, verify_state)?;
        let proof_result = self.prove_fact_allow_unknown(fact, verify_state)?;
        let proof_result = match fact {
            Fact::AtomicFact(_) => {
                self.structured_unknown_result_for_failed_fact(fact, verify_state, proof_result)?
            }
            _ => proof_result,
        };

        Ok(Self::finish_fact_verification(checked, proof_result))
    }

    #[track_caller]
    pub fn finish_fact_verification(
        checked: crate::result::WellDefinedFactResult,
        proof_result: ProveFactResult,
    ) -> VerifyFactResult {
        let fact = checked.fact.clone();
        match proof_result {
            ProveFactResult::Proven(result) => {
                debug_assert!(
                    result.fact_id.is_none(),
                    "fact proof search must not allocate a persistent FactId"
                );
                VerifyFactResult::Verified(Rc::new(VerifiedFactResult::new(
                    checked,
                    result.verification,
                )))
            }
            ProveFactResult::Unknown(unknown) => {
                let unknown = match unknown {
                    crate::result::UnknownStmtResult::Fact(unknown) => *unknown,
                    crate::result::UnknownStmtResult::Generic(unknown) => {
                        UnknownFactResult::from_stmt_unknown(fact.clone(), *unknown)
                    }
                };
                VerifyFactResult::Unknown(Box::new(UnknownVerifyFactResult { checked, unknown }))
            }
        }
    }

    /// Completes a truth-proof result with the fact's WD derivation.
    ///
    /// Internal proof algorithms may build `ProveFactResult` values, but every
    /// fact-shaped node that escapes into the returned verification DAG passes
    /// through this boundary first.
    pub fn complete_fact_proof_result(
        &mut self,
        fact: &Fact,
        proof_result: ProveFactResult,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let checked = self.verify_fact_well_defined_result(fact, verify_state)?;
        Ok(Self::finish_fact_verification(checked, proof_result))
    }

    pub fn complete_atomic_fact_proof_result(
        &mut self,
        fact: &crate::fact::AtomicFact,
        proof_result: ProveFactResult,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.complete_fact_proof_result(&fact.clone().into(), proof_result, verify_state)
    }

    /// Truth-proof search after the caller has established the complete WD
    /// derivation. This phase is intentionally unable to persist a statement.
    fn prove_fact_allow_unknown(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.prove_atomic_fact(atomic_fact, verify_state),
            Fact::AndFact(and_fact) => self.prove_and_fact(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => self.prove_chain_fact(chain_fact, verify_state),
            Fact::ForallFact(forall_fact) => self.prove_forall_fact(forall_fact, verify_state),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.prove_forall_fact_with_iff(forall_fact_with_iff, verify_state)
            }
            Fact::NotForall(not_forall) => self.prove_not_forall_fact(not_forall, verify_state),
            Fact::ExistFact(exists_fact) => self.prove_exist_fact(exists_fact, verify_state),
            Fact::OrFact(or_fact) => self.prove_or_fact(or_fact, verify_state),
        }
    }

    pub fn verify_fact_or_error(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        match self.verify_fact_allow_unknown(fact, verify_state)? {
            result @ VerifyFactResult::Verified(_) => Ok(result),
            VerifyFactResult::Unknown(unknown) => {
                let fact_owned = fact.clone();
                let line_file = fact_owned.line_file();
                let unknown_output =
                    RuntimeErrorOutput::goal_unknown_fact(fact_owned.clone(), &unknown.unknown);
                Err(RuntimeError::from(VerifyRuntimeError(
                    RuntimeErrorStruct::new(
                        Some(fact_owned.clone().into_stmt()),
                        "verification failed".to_string(),
                        line_file.clone(),
                        Some(RuntimeError::from(UnknownRuntimeError(
                            RuntimeErrorStruct::new_with_output(
                                Some(fact_owned.into_stmt()),
                                "unknown result".to_string(),
                                line_file,
                                None,
                                vec![],
                                unknown_output,
                            ),
                        ))),
                        vec![],
                    ),
                )))
            }
        }
    }

    pub fn structured_unknown_result_for_failed_fact(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
        result: ProveFactResult,
    ) -> Result<ProveFactResult, RuntimeError> {
        if !result.is_unknown() || result.as_fact_unknown().is_some() {
            return Ok(result);
        }

        match fact {
            Fact::AndFact(and_fact) => {
                let verify_state_for_children = verify_state.clone();
                for (fact_index, child_fact) in and_fact.facts.iter().enumerate() {
                    let child_result =
                        self.prove_atomic_fact(child_fact, &verify_state_for_children)?;
                    if child_result.is_unknown() {
                        let child_result =
                            child_result.wrap_unknown_for_fact(child_fact.clone().into());
                        return Ok(UnknownFactResult::and_with_failed_part(
                            and_fact.clone(),
                            fact_index + 1,
                            and_fact.facts.len(),
                            child_fact.clone().into(),
                            child_result.as_fact_unknown().cloned(),
                        )
                        .into());
                    }
                }
                Ok(result.wrap_unknown_for_fact(fact.clone()))
            }
            Fact::ChainFact(chain_fact) => {
                let verify_state_for_children = verify_state.clone();
                let facts = chain_fact.facts(self)?;
                for (fact_index, child_fact) in facts.iter().enumerate() {
                    let child_result =
                        self.prove_atomic_fact(child_fact, &verify_state_for_children)?;
                    if child_result.is_unknown() {
                        let child_result =
                            child_result.wrap_unknown_for_fact(child_fact.clone().into());
                        return Ok(UnknownFactResult::chain_with_failed_part(
                            chain_fact.clone(),
                            fact_index + 1,
                            facts.len(),
                            child_fact.clone().into(),
                            child_result.as_fact_unknown().cloned(),
                            vec![],
                        )
                        .into());
                    }
                }
                Ok(result.wrap_unknown_for_fact(fact.clone()))
            }
            _ => {
                let detail_lines = self.contextual_rewrite_diagnostic_for_fact(fact);
                if detail_lines.is_empty() {
                    Ok(result.wrap_unknown_for_fact(fact.clone()))
                } else {
                    Ok(UnknownFactResult::new_with_detail_lines(fact.clone(), detail_lines).into())
                }
            }
        }
    }
    pub fn verify_exist_or_and_chain_atomic_fact(
        &mut self,
        exist_or_and_chain_atomic_fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(
            &exist_or_and_chain_atomic_fact.clone().to_fact(),
            verify_state,
        )
    }

    pub fn verify_quantifier_free_fact(
        &mut self,
        quantifier_free_fact: &QuantifierFreeFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&quantifier_free_fact.clone().to_fact(), verify_state)
    }

    pub fn verify_and_chain_atomic_fact(
        &mut self,
        and_chain_atomic_fact: &AndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&and_chain_atomic_fact.clone().into(), verify_state)
    }
}
