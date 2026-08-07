use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    /// Mathematical contract: outside an explicitly trusted source boundary,
    /// a fact is stored and used for inference only after central
    /// well-definedness succeeds.
    pub fn verify_well_defined_and_store_and_infer(
        &mut self,
        fact: Fact,
        verify_state: &UseContextVerifyState,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_well_defined_and_store_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::VerifiedStatement,
        )
    }

    /// Mathematical contract: adding a provenance reason does not change the
    /// fact's well-definedness obligations or inferred mathematics.
    pub fn verify_well_defined_and_store_and_infer_with_reason(
        &mut self,
        fact: Fact,
        verify_state: &UseContextVerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.store_reason();
        self.verify_well_defined_and_store_and_infer_with_reason_text(
            fact,
            verify_state,
            reason_text,
        )
    }

    /// Mathematical contract implementation: cached facts reuse their prior
    /// check, ordinary sources are centrally checked, and only the repository's
    /// explicit trusted-file boundary may bypass this gate.
    fn verify_well_defined_and_store_and_infer_with_reason_text(
        &mut self,
        fact: Fact,
        verify_state: &UseContextVerifyState,
        reason_text: String,
    ) -> Result<InferResult, RuntimeError> {
        if self.non_forall_fact_is_cached(&fact) {
            return self.infer(&fact);
        }
        if self.current_execution_is_trusted_file() {
            return self.store_and_infer_fact_without_well_defined_verified_with_reason_text(
                fact,
                reason_text,
            );
        }
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
        self.store_and_infer_fact_without_well_defined_verified_with_reason_text(fact, reason_text)
    }

    /// Mathematical contract: enforce the same fact contract using the
    /// verifier state appropriate to quantified versus non-quantified facts.
    pub fn verify_well_defined_and_store_and_infer_with_default_verify_state(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        self.verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
            fact,
            InferReason::VerifiedStatement,
        )
    }

    /// Mathematical contract: provenance does not alter the default-state
    /// well-definedness check selected for the fact's quantifier form.
    pub fn verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let verify_state = match &fact {
            Fact::ForallFact(_) => UseContextVerifyState::new(0, false),
            Fact::ForallFactWithIff(_) => UseContextVerifyState::new(0, false),
            _ => UseContextVerifyState::new_with_final_round(false),
        };
        self.verify_well_defined_and_store_and_infer_with_reason(fact, &verify_state, reason)
    }

    pub fn store_trusted_fact_and_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.store_reason();
        self.store_and_infer_fact_without_well_defined_verified_with_reason_text(fact, reason_text)
    }

    fn store_and_infer_fact_without_well_defined_verified_with_reason_text(
        &mut self,
        fact: Fact,
        reason_text: String,
    ) -> Result<InferResult, RuntimeError> {
        if self.non_forall_fact_is_cached(&fact) {
            return self.infer(&fact);
        }
        let output_fact = fact.clone();

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

        let inferred_facts = ret?.inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&output_fact, reason_text, inferred_facts);
        Ok(infer_result)
    }

    pub fn store_fact_without_forall_coverage_check_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_fact_without_forall_coverage_check_and_infer_with_reason(
            fact,
            InferReason::StoredFactWithoutForallCoverageCheck.store_reason(),
        )
    }

    pub fn store_fact_without_forall_coverage_check_and_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: impl Into<String>,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.into();
        let output_fact = fact.clone();
        let inferred_facts = self
            .store_whole_fact_update_cache_known_fact_and_infer(fact)?
            .inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&output_fact, reason_text, inferred_facts);
        Ok(infer_result)
    }

    pub(crate) fn store_forall_fact_without_well_defined_verified_and_infer(
        &mut self,
        mut forall_fact: ForallFact,
    ) -> Result<InferResult, RuntimeError> {
        forall_fact.expand_then_facts_with_order_chain_closure()?;

        let coverage_error_detail_lines =
            forall_fact.error_messages_if_forall_param_missing_in_some_then_clause();
        let mut projected_forall_facts = Vec::new();
        if !coverage_error_detail_lines.is_empty()
            && forall_fact
                .params_def_with_type
                .param_type_cited_param_indices
                .iter()
                .all(|indices| indices.is_empty())
        {
            for (then_index, _) in coverage_error_detail_lines.iter() {
                let then_fact = &forall_fact.then_facts[*then_index];
                let coverage = forall_fact.forall_param_coverage_for_then_clause(then_fact);
                let mut retained_groups = Vec::new();
                let mut omitted_types_are_nonempty = true;
                for group in forall_fact.params_def_with_type.groups.iter() {
                    let mut retained_params = Vec::new();
                    for binding in group.params.iter() {
                        if coverage.get(binding.name()).copied().unwrap_or(false) {
                            retained_params.push(binding.clone());
                        } else if self
                            .verify_param_type_nonempty_if_required(&group.param_type, true)
                            .is_err()
                        {
                            omitted_types_are_nonempty = false;
                            break;
                        }
                    }
                    if !retained_params.is_empty() {
                        retained_groups.push(ParamGroupWithParamType::new(
                            retained_params,
                            group.param_type.clone(),
                        ));
                    }
                    if !omitted_types_are_nonempty {
                        break;
                    }
                }
                if omitted_types_are_nonempty && !retained_groups.is_empty() {
                    // A grouped law may bind convenient shared variables even when one
                    // positive clause uses only a subset. Eliminate only unused
                    // parameters whose independent domains are known nonempty.
                    // Example: `forall a,b R, x,y E: norm(a • x)=...` exposes
                    // `forall a R, x E: norm(a • x)=...` when `E` is nonempty.
                    projected_forall_facts.push(ForallFact::new_canonical_forall(
                        ParamDefWithType::new(retained_groups),
                        forall_fact.dom_facts.clone(),
                        vec![then_fact.clone()],
                        forall_fact.line_file.clone(),
                    )?);
                }
            }
        }
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
                let mut infer_result = InferResult::new();
                for projected in projected_forall_facts {
                    infer_result.new_infer_result_inside(
                        self.store_forall_fact_without_well_defined_verified_and_infer(projected)?,
                    );
                }
                return Ok(infer_result);
            }
        }

        let output_fact: Fact = forall_fact.clone().into();
        let inferred_facts = self
            .store_whole_fact_update_cache_known_fact_and_infer(output_fact.clone())?
            .inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(
            &output_fact,
            InferReason::StoredForallFact.store_reason(),
            inferred_facts,
        );
        for projected in projected_forall_facts {
            infer_result.new_infer_result_inside(
                self.store_forall_fact_without_well_defined_verified_and_infer(projected)?,
            );
        }
        Ok(infer_result)
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
        if self.non_forall_fact_is_cached(&fact) {
            return self.infer(&fact);
        }
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let alpha_normalized_forall_key = match &fact {
            Fact::ForallFact(forall_fact) => {
                Some(self.alpha_normalized_forall_cache_key(forall_fact)?)
            }
            _ => None,
        };
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

        let fact_id = self.store_fact_cache_keys_with_nested_obj_binders(&fact_for_infer)?;
        if let Some(alpha_key) = alpha_normalized_forall_key {
            if alpha_key != fact_string {
                self.top_level_env()
                    .store_fact_to_cache_known_fact(alpha_key, line_file, fact_id)?;
            }
        }

        Ok(self.infer(&fact_for_infer)?)
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: AndChainAtomicFact,
        reason: impl Into<String>,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.into();
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

        self.store_fact_cache_keys_with_nested_obj_binders(&fact_for_infer)?;

        let inferred_facts = self.infer(&fact_for_infer)?.inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&fact_for_infer, reason_text, inferred_facts);
        Ok(infer_result)
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: AtomicFact,
        reason: impl Into<String>,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.into();
        let infer_wrapped_fact: Fact = fact.clone().into();
        self.top_level_env().store_atomic_fact(fact)?;

        self.store_fact_cache_keys_with_nested_obj_binders(&infer_wrapped_fact)?;

        let inferred_facts = self.infer(&infer_wrapped_fact)?.inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&infer_wrapped_fact, reason_text, inferred_facts);
        Ok(infer_result)
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
        reason: impl Into<String>,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.into();
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

        let output_fact = fact_for_infer.clone().to_fact();
        self.store_fact_cache_keys_with_nested_obj_binders(&output_fact)?;
        let inferred_facts = self
            .infer_exist_or_and_chain_atomic_fact(&fact_for_infer)?
            .inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&output_fact, reason_text, inferred_facts);
        Ok(infer_result)
    }

    pub fn store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: OrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: OrAndChainAtomicFact,
        reason: impl Into<String>,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.into();
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

        let output_fact = fact_for_infer.clone().to_fact();
        self.store_fact_cache_keys_with_nested_obj_binders(&output_fact)?;
        let inferred_facts = self
            .infer_or_and_chain_atomic_fact(&fact_for_infer)?
            .inferred_facts();
        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&output_fact, reason_text, inferred_facts);
        Ok(infer_result)
    }

    fn store_transitive_prop_chain_atomic_facts(
        &mut self,
        facts: Vec<AtomicFact>,
    ) -> Result<(), RuntimeError> {
        for atomic_fact in facts {
            self.top_level_env()
                .store_atomic_fact(atomic_fact.clone())?;
            self.store_fact_cache_keys_with_nested_obj_binders(&atomic_fact.into())?;
        }
        Ok(())
    }

    fn store_chain_atomic_facts_to_cache(
        &mut self,
        facts: Vec<AtomicFact>,
    ) -> Result<(), RuntimeError> {
        for atomic_fact in facts {
            self.store_fact_cache_keys_with_nested_obj_binders(&atomic_fact.into())?;
        }
        Ok(())
    }

    pub(crate) fn store_fact_cache_keys_with_nested_obj_binders(
        &mut self,
        fact: &Fact,
    ) -> Result<FactId, RuntimeError> {
        let line_file = fact.line_file();
        let fact_string = fact.to_string();
        let normalized_key = nested_obj_binder_normalized_fact_key(fact);
        let fact_id = self
            .known_fact_id_for_fact(fact)?
            .map(Ok)
            .unwrap_or_else(|| self.allocate_fact_id())?;
        self.top_level_env().store_fact_to_cache_known_fact(
            fact_string.clone(),
            line_file.clone(),
            fact_id,
        )?;
        if normalized_key != fact_string {
            self.top_level_env().store_fact_to_cache_known_fact(
                normalized_key,
                line_file,
                fact_id,
            )?;
        }
        Ok(fact_id)
    }

    /// Mathematical contract: store a fact without deriving consequences only
    /// after central well-definedness succeeds, except at the explicit
    /// trusted-file boundary.
    pub(crate) fn verify_well_defined_and_store_without_infer(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let verify_state = match &fact {
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => {
                UseContextVerifyState::new(0, false)
            }
            _ => UseContextVerifyState::new_with_final_round(false),
        };
        self.verify_well_defined_and_store_without_infer_with_state(fact, &verify_state, reason)
    }

    /// Mathematical contract: the state-aware form preserves a caller's
    /// recursion restrictions while staging a checked fact without deriving
    /// consequences from it.
    pub(crate) fn verify_well_defined_and_store_without_infer_with_state(
        &mut self,
        fact: Fact,
        verify_state: &UseContextVerifyState,
        reason: InferReason,
    ) -> Result<InferResult, RuntimeError> {
        let reason_text = reason.store_reason();
        if self.non_forall_fact_is_cached(&fact) {
            return Ok(InferResult::new());
        }
        if !self.current_execution_is_trusted_file() {
            self.verify_fact_well_defined(&fact, verify_state)?;
        }

        self.top_level_env().store_fact(fact.clone())?;
        self.store_fact_cache_keys_with_nested_obj_binders(&fact)?;

        let mut infer_result = InferResult::new();
        infer_result.add_store_fact_output(&fact, reason_text, vec![]);
        Ok(infer_result)
    }

    fn non_forall_fact_is_cached(&self, fact: &Fact) -> bool {
        if matches!(fact, Fact::ForallFact(_) | Fact::ForallFactWithIff(_)) {
            return false;
        }
        let fact_key = fact.to_string();
        if self.cache_known_facts_contains(&fact_key).0 {
            return true;
        }
        let normalized_key = nested_obj_binder_normalized_fact_key(fact);
        normalized_key != fact_key && self.cache_known_facts_contains(&normalized_key).0
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
