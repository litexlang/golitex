use crate::prelude::*;

impl Runtime {
    /// If the fact string is in the known-facts cache, return the cached verification result.
    pub fn verify_fact_from_cache_using_display_string(&self, fact: &Fact) -> Option<StmtResult> {
        let key = fact.to_string();
        let (cache_ok, cite_fact_source) = self.cache_known_facts_contains(&key);
        if cache_ok {
            Some(
                (FactualStmtSuccess::new_with_verified_by_known_fact(
                    fact.clone(),
                    VerifiedByResult::cached_fact(fact.clone(), cite_fact_source),
                    Vec::new(),
                ))
                .into(),
            )
        } else {
            None
        }
    }

    /// If check_type_nonempty is true and param_type is Obj(set), verifies that the set is nonempty and stores the fact.
    pub fn verify_param_type_nonempty_if_required(
        &mut self,
        param_type: &ParamType,
        check_type_nonempty: bool,
    ) -> Result<(), RuntimeError> {
        if !check_type_nonempty {
            return Ok(());
        }
        match param_type {
            ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(param_set) => match param_set {
                Obj::FnSet(fn_set) => {
                    let ret_nonempty = IsNonemptySetFact::new(
                        fn_set.body.ret_set.as_ref().clone(),
                        default_line_file(),
                    )
                    .into();
                    self.verify_fact_well_defined_and_store_and_infer(
                        ret_nonempty,
                        &VerifyState::new(2, false),
                    )?;
                    Ok(())
                }
                Obj::AnonymousFn(anon) => {
                    let ret_nonempty = IsNonemptySetFact::new(
                        anon.body.ret_set.as_ref().clone(),
                        default_line_file(),
                    )
                    .into();
                    self.verify_fact_well_defined_and_store_and_infer(
                        ret_nonempty,
                        &VerifyState::new(2, false),
                    )?;
                    Ok(())
                }
                _ => {
                    let nonempty_fact =
                        IsNonemptySetFact::new(param_set.clone(), default_line_file());
                    let ret =
                        self.verify_fact(&nonempty_fact.into(), &VerifyState::new(0, false))?;
                    if ret.is_unknown() {
                        return Err(RuntimeError::from(VerifyRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(
                                "param type is not nonempty".to_string(),
                            ),
                        )));
                    }
                    Ok(())
                }
            },
        }
    }

    pub(crate) fn verify_atomic_fact_known_then_builtin_rules_only(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&atomic_fact.clone().into())
        {
            return Ok(cached_result);
        }
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_objs_are_equal_in_equality_builtin(
                &equal_fact.left,
                &equal_fact.right,
                equal_fact.line_file.clone(),
                verify_state,
            ),
            _ => {
                self.verify_non_equational_known_then_builtin_rules_only(atomic_fact, verify_state)
            }
        }
    }

    pub(crate) fn non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let result =
            self.verify_non_equational_known_then_builtin_rules_only(atomic_fact, verify_state)?;
        Ok(result.is_true())
    }

    pub(crate) fn verify_and_chain_atomic_fact_known_then_builtin_rules_only(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.verify_atomic_fact_known_then_builtin_rules_only(atomic_fact, verify_state)
            }
            AndChainAtomicFact::AndFact(and_fact) => {
                self.verify_and_fact_known_then_builtin_rules_only(and_fact, verify_state)
            }
            AndChainAtomicFact::ChainFact(chain_fact) => {
                self.verify_chain_fact_known_then_builtin_rules_only(chain_fact, verify_state)
            }
        }
    }

    pub(crate) fn verify_and_fact_known_then_builtin_rules_only(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let mut steps = Vec::with_capacity(and_fact.facts.len());
        for atomic_fact in and_fact.facts.iter() {
            let result =
                self.verify_atomic_fact_known_then_builtin_rules_only(atomic_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
            steps.push(result);
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                and_fact.clone().into(),
                "restricted builtin premise: each conjunct verified".to_string(),
                steps,
            )
            .into(),
        )
    }

    pub(crate) fn verify_chain_fact_known_then_builtin_rules_only(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let facts = chain_fact.facts()?;
        let and_fact = AndFact::new(facts, chain_fact.line_file.clone());
        self.verify_and_fact_known_then_builtin_rules_only(&and_fact, verify_state)
    }

    pub(crate) fn verify_or_fact_known_then_builtin_rules_only(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&or_fact.clone().into())
        {
            return Ok(cached_result);
        }
        let known_or_result = self.verify_or_fact_with_known_or_facts(or_fact)?;
        if known_or_result.is_true() {
            return Ok(known_or_result);
        }
        for fact in or_fact.facts.iter() {
            let result = self
                .verify_and_chain_atomic_fact_known_then_builtin_rules_only(fact, verify_state)?;
            if result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        or_fact.clone().into(),
                        "restricted builtin premise: one branch verified".to_string(),
                        vec![result],
                    )
                    .into(),
                );
            }
        }
        Ok(StmtUnknown::new().into())
    }
}
