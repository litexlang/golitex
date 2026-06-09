use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    pub fn verify_well_defined_and_store_and_infer(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_well_defined_and_store_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::VerifiedStatement,
        )
    }

    pub fn verify_well_defined_and_store_and_infer_with_reason(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        if let Err(wd_err) = self.verify_fact_well_defined(&fact, verify_state) {
            return Err(StoreFactRuntimeError(RuntimeErrorStruct::new(
                Some(fact.clone().into_stmt()),
                "cannot store fact: not well-defined".to_string(),
                fact.line_file(),
                Some(wd_err),
                vec![],
            ))
            .into());
        }
        self.store_and_infer_fact_without_well_defined_verified_with_reason(fact, reason)
    }

    pub fn verify_well_defined_and_store_and_infer_with_default_verify_state(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
            fact,
            InferReason::VerifiedStatement,
        )
    }

    pub fn verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let verify_state = match &fact {
            Fact::ForallFact(_) => VerifyState::new(0, false),
            Fact::ForallFactWithIff(_) => VerifyState::new(0, false),
            _ => VerifyState::new_with_final_round(false),
        };
        self.verify_well_defined_and_store_and_infer_with_reason(fact, &verify_state, reason)
    }

    fn store_and_infer_fact_without_well_defined_verified_with_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        match &reason {
            InferReason::VerifiedStatement => infer_result.add_verified_statement(&fact),
            InferReason::ProvedClaim => infer_result.add_proved_claim(&fact),
            InferReason::UnsafeAssumption => infer_result.add_unsafe_assumption(&fact),
            InferReason::LetBinding => infer_result.add_let_binding(&fact),
            InferReason::ObjectIntroduction => infer_result.add_object_introduction(&fact),
            InferReason::ExistElimination => infer_result.add_exist_elimination(&fact),
            InferReason::TheoremInstantiation => infer_result.add_theorem_instantiation(&fact),
            InferReason::Evaluation => infer_result.add_evaluation(&fact),
            InferReason::ParameterDeclaration => infer_result.add_parameter_declaration(&fact),
            _ => infer_result.add_fact_with_reason(reason.clone(), &fact),
        }

        let ret = match fact {
            Fact::AtomicFact(_)
            | Fact::ExistFact(_)
            | Fact::OrFact(_)
            | Fact::AndFact(_)
            | Fact::ChainFact(_)
            | Fact::NotForall(_) => self.store_whole_fact_update_cache_known_fact_and_infer(fact),
            Fact::ForallFact(forall_fact) => {
                self.store_forall_fact_without_well_defined_verified_and_infer(forall_fact)
            }
            Fact::ForallFactWithIff(forall_fact_with_iff) => self
                .store_forall_fact_with_iff_without_well_defined_verified_and_infer(
                    forall_fact_with_iff,
                ),
        };

        infer_result.new_infer_result_inside(ret?);

        Ok(infer_result)
    }

    pub fn store_fact_without_forall_coverage_check_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_whole_fact_update_cache_known_fact_and_infer(fact)
    }

    pub(crate) fn store_forall_fact_without_well_defined_verified_and_infer(
        &mut self,
        mut forall_fact: ForallFact,
    ) -> Result<InferResult, RuntimeError> {
        forall_fact.expand_then_facts_with_order_chain_closure()?;

        let coverage_error_detail_lines =
            forall_fact.error_messages_if_forall_param_missing_in_some_then_clause();
        if !coverage_error_detail_lines.is_empty() {
            let then_drop: HashSet<usize> = coverage_error_detail_lines
                .iter()
                .map(|(i, _)| *i)
                .collect();
            forall_fact.then_facts = forall_fact
                .then_facts
                .into_iter()
                .enumerate()
                .filter(|(i, _)| !then_drop.contains(i))
                .map(|(_, f)| f)
                .collect();
            if forall_fact.then_facts.is_empty() {
                return Ok(InferResult::new());
            }
        }

        self.store_whole_fact_update_cache_known_fact_and_infer(Fact::ForallFact(forall_fact))
    }

    fn store_forall_fact_with_iff_without_well_defined_verified_and_infer(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
    ) -> Result<InferResult, RuntimeError> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts()?;
        let mut infer_result = self
            .store_forall_fact_without_well_defined_verified_and_infer(forall_then_implies_iff)?;
        infer_result.new_infer_result_inside(
            self.store_forall_fact_without_well_defined_verified_and_infer(
                forall_iff_implies_then,
            )?,
        );
        Ok(infer_result)
    }

    fn store_whole_fact_update_cache_known_fact_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.clone();
        let chain_atomic_facts = match &fact {
            Fact::ChainFact(chain_fact) => chain_fact.facts_with_order_transitive_closure()?,
            _ => Vec::new(),
        };
        let transitive_chain_facts = match &fact {
            Fact::ChainFact(chain_fact) => self.transitive_prop_chain_closure_facts(chain_fact)?,
            _ => Vec::new(),
        };
        self.top_level_env().store_fact(fact)?;
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        Ok(self.infer(&fact_for_infer)?)
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer: Fact = fact.clone().into();
        let chain_atomic_facts = match &fact {
            AndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.facts_with_order_transitive_closure()?
            }
            _ => Vec::new(),
        };
        let transitive_chain_facts = match &fact {
            AndChainAtomicFact::ChainFact(chain_fact) => {
                self.transitive_prop_chain_closure_facts(chain_fact)?
            }
            _ => Vec::new(),
        };
        self.top_level_env().store_and_chain_atomic_fact(fact)?;
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        Ok(self.infer(&fact_for_infer)?)
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let infer_wrapped_fact: Fact = fact.clone().into();
        self.top_level_env().store_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        Ok(self.infer(&infer_wrapped_fact)?)
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.clone();
        let chain_atomic_facts = match &fact {
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.facts_with_order_transitive_closure()?
            }
            _ => Vec::new(),
        };
        let transitive_chain_facts = match &fact {
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.transitive_prop_chain_closure_facts(chain_fact)?
            }
            _ => Vec::new(),
        };
        self.top_level_env()
            .store_exist_or_and_chain_atomic_fact(fact)?;
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        Ok(self.infer_exist_or_and_chain_atomic_fact(&fact_for_infer)?)
    }

    pub fn store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: OrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.clone();
        let chain_atomic_facts = match &fact {
            OrAndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.facts_with_order_transitive_closure()?
            }
            _ => Vec::new(),
        };
        let transitive_chain_facts = match &fact {
            OrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.transitive_prop_chain_closure_facts(chain_fact)?
            }
            _ => Vec::new(),
        };
        self.top_level_env().store_or_and_chain_atomic_fact(fact)?;
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        Ok(self.infer_or_and_chain_atomic_fact(&fact_for_infer)?)
    }

    fn store_transitive_prop_chain_atomic_facts(
        &mut self,
        facts: Vec<AtomicFact>,
    ) -> Result<(), RuntimeError> {
        for atomic_fact in facts {
            self.top_level_env().store_atomic_fact(atomic_fact)?;
        }
        Ok(())
    }

    fn store_chain_atomic_facts_to_cache(
        &mut self,
        facts: Vec<AtomicFact>,
    ) -> Result<(), RuntimeError> {
        for atomic_fact in facts {
            let line_file = atomic_fact.line_file();
            self.top_level_env()
                .store_fact_to_cache_known_fact(atomic_fact.to_string(), line_file)?;
        }
        Ok(())
    }

    fn transitive_prop_chain_closure_facts(
        &self,
        chain_fact: &ChainFact,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        if chain_fact.prop_names.is_empty() || chain_fact.objs.len() < 3 {
            return Ok(Vec::new());
        }

        let prop_name = chain_fact.prop_names[0].to_string();
        for name in chain_fact.prop_names.iter() {
            if name.to_string() != prop_name {
                return Ok(Vec::new());
            }
        }
        if !self.is_transitive_prop_name_known(&prop_name) {
            return Ok(Vec::new());
        }

        let mut facts = Vec::new();
        for i in 0..chain_fact.objs.len() {
            for j in i + 2..chain_fact.objs.len() {
                facts.push(
                    NormalAtomicFact::new(
                        chain_fact.prop_names[0].clone(),
                        vec![chain_fact.objs[i].clone(), chain_fact.objs[j].clone()],
                        chain_fact.line_file.clone(),
                    )
                    .into(),
                );
            }
        }
        Ok(facts)
    }

    fn is_transitive_prop_name_known(&self, prop_name: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if env.known_transitive_props.contains_key(prop_name) {
                return true;
            }
        }
        false
    }
}
