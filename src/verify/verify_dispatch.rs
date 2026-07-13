use crate::prelude::*;

impl Runtime {
    /// Full fact verification used for user proof obligations.
    ///
    /// This path may use the full verifier stack for the fact shape, including
    /// known forall instantiation, user strategies, definitions, and recursive
    /// proof obligations where those features are part of the ordinary proof
    /// model. Restricted builtin premises should use
    /// `verify_fact_restricted_known_builtin` instead.
    pub fn verify_fact_full(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            Fact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => self.verify_chain_fact(chain_fact, verify_state),
            Fact::ForallFact(forall_fact) => self.verify_forall_fact(forall_fact, verify_state),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.verify_forall_fact_with_iff(forall_fact_with_iff, verify_state)
            }
            Fact::NotForall(not_forall) => self.verify_not_forall_fact(not_forall, verify_state),
            Fact::ExistFact(exists_fact) => self.verify_exist_fact(exists_fact, verify_state),
            Fact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }
    }

    pub fn verify_fact_return_err_if_not_true(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let result = self.verify_fact_full(fact, verify_state)?;
        let result = self.structured_unknown_result_for_failed_fact(fact, verify_state, result)?;

        if result.is_unknown() {
            let fact_owned = fact.clone();
            let line_file = fact_owned.line_file();
            let unknown_output = RuntimeErrorOutput::goal_unknown(fact_owned.clone(), &result);
            return Err(RuntimeError::from(VerifyRuntimeError(
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
            )));
        }

        Ok(result)
    }

    pub(crate) fn structured_unknown_result_for_failed_fact(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        if !result.is_unknown() || result.as_fact_unknown().is_some() {
            return Ok(result);
        }

        match fact {
            Fact::AndFact(and_fact) => {
                let verify_state_for_children = verify_state.with_well_defined_already_verified();
                for (fact_index, child_fact) in and_fact.facts.iter().enumerate() {
                    let child_result =
                        self.verify_atomic_fact(child_fact, &verify_state_for_children)?;
                    if child_result.is_unknown() {
                        let child_result =
                            child_result.wrap_unknown_for_fact(child_fact.clone().into());
                        return Ok(FactUnknown::and_with_failed_part(
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
                let verify_state_for_children = verify_state.with_well_defined_already_verified();
                let facts = chain_fact.facts()?;
                for (fact_index, child_fact) in facts.iter().enumerate() {
                    let child_result =
                        self.verify_atomic_fact(child_fact, &verify_state_for_children)?;
                    if child_result.is_unknown() {
                        let child_result =
                            child_result.wrap_unknown_for_fact(child_fact.clone().into());
                        return Ok(FactUnknown::chain_with_failed_part(
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
            _ => Ok(result.wrap_unknown_for_fact(fact.clone())),
        }
    }
    pub fn verify_exist_or_and_chain_atomic_fact(
        &mut self,
        exist_or_and_chain_atomic_fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match exist_or_and_chain_atomic_fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact(atomic_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                self.verify_and_fact(and_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact(chain_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                self.verify_or_fact(or_fact, verify_state)
            }
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                self.verify_exist_fact(exist_fact, verify_state)
            }
        }
    }

    pub fn verify_or_and_chain_atomic_fact(
        &mut self,
        or_and_chain_atomic_fact: &OrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match or_and_chain_atomic_fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact(atomic_fact, verify_state)
            }
            OrAndChainAtomicFact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            OrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact(chain_fact, verify_state)
            }
            OrAndChainAtomicFact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }
    }

    pub fn verify_and_chain_atomic_fact(
        &mut self,
        and_chain_atomic_fact: &AndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match and_chain_atomic_fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact(atomic_fact, verify_state)
            }
            AndChainAtomicFact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            AndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact(chain_fact, verify_state)
            }
        }
    }
}
