//! Fact storage, FactId assignment, and immediate closure inference.

use crate::prelude::*;
use std::collections::HashSet;

struct RegisteredTransitivePredicateChainClosureInference {
    rule: RegisteredTransitivePredicateChainClosureInferRule,
    premises: Vec<Fact>,
    conclusion: AtomicFact,
}

struct EqualityChainClosureInference {
    rule: EqualityChainClosureInferRule,
    premises: Vec<Fact>,
    conclusion: AtomicFact,
}

impl Runtime {
    /// Mathematical contract: outside an explicitly trusted source boundary,
    /// a fact is stored and used for inference only after central
    /// well-definedness succeeds.
    pub fn store_with_well_defined_verification_and_infer(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_with_well_defined_verification_and_infer_with_reason(
            fact,
            verify_state,
            InferReason::StatementWithVerification,
        )
    }

    /// Mathematical contract: adding a provenance reason does not change the
    /// fact's well-definedness obligations or inferred mathematics.
    pub fn store_with_well_defined_verification_and_infer_with_reason(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.store_reason();
        self.store_with_well_defined_verification_and_infer_with_reason_text(
            fact,
            verify_state,
            reason_text,
        )
    }

    /// Mathematical contract implementation: cached facts reuse their prior
    /// check, ordinary sources are centrally checked, and only the repository's
    /// explicit trusted-source boundary may bypass this gate.
    fn store_with_well_defined_verification_and_infer_with_reason_text(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
        reason_text: String,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_with_well_defined_verification_and_infer_with_reason_text_and_state(
            fact,
            verify_state,
            reason_text,
            verify_state.inference_state(),
        )
    }

    fn store_with_well_defined_verification_and_infer_with_reason_text_and_state(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
        reason_text: String,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if self.non_forall_fact_is_cached(&fact) {
            return self.infer_with_state(&fact, inference_state);
        }
        if self.current_execution_is_trusted_source() {
            return self
                .store_without_well_defined_verification_and_infer_with_reason_text_and_state(
                    fact,
                    reason_text,
                    inference_state,
                );
        }
        let verify_state = verify_state.with_inference_state(inference_state);
        if let Err(wd_err) = self.verify_fact_well_defined_result(&fact, &verify_state) {
            return Err(StoreFactRuntimeError(RuntimeErrorStruct::new(
                Some(fact.clone().into_stmt()),
                "cannot store fact: not well-defined".to_string(),
                fact.line_file(),
                Some(wd_err),
                vec![],
            ))
            .into());
        }
        self.store_without_well_defined_verification_and_infer_with_reason_text_and_state(
            fact,
            reason_text,
            inference_state,
        )
    }

    /// Mathematical contract: enforce the same fact contract using the
    /// verifier state appropriate to quantified versus non-quantified facts.
    pub fn store_with_well_defined_verification_and_infer_with_default_verify_state(
        &mut self,
        fact: Fact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
            fact,
            InferReason::StatementWithVerification,
        )
    }

    /// Mathematical contract: provenance does not alter the default-state
    /// well-definedness check selected for the fact's quantifier form.
    pub fn store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let verify_state = match &fact {
            Fact::ForallFact(_) => VerifyState::initial(),
            Fact::ForallFactWithIff(_) => VerifyState::initial(),
            _ => VerifyState::final_round(),
        };
        self.store_with_well_defined_verification_and_infer_with_reason(fact, &verify_state, reason)
    }

    /// Mathematical contract: a typed inference rule owns the justification
    /// for both the truth and well-definedness of its exact conclusion. Store
    /// that conclusion and continue closure inference without submitting it as
    /// a new, independent fact-verification process. Any later statement that
    /// uses the stored conclusion still constructs its own complete WD DAG.
    pub fn store_typed_inference_conclusion_and_infer(
        &mut self,
        fact: Fact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_typed_inference_conclusion_and_infer_with_reason(
            fact,
            InferReason::StoredFact,
            inference_state,
        )
    }

    /// The provenance label changes how the typed inference is explained, not
    /// whether its conclusion is redundantly submitted to fact verification.
    pub fn store_typed_inference_conclusion_and_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_without_well_defined_verification_and_infer_with_reason_and_state(
            fact,
            reason,
            inference_state,
        )
    }

    /// Mathematical contract: store a fact whose complete well-definedness
    /// contract was already established by the current statement preflight.
    pub fn store_without_well_defined_verification_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_without_well_defined_verification_and_infer_with_reason(
            fact,
            InferReason::StatementWithVerification,
        )
    }

    /// Mathematical contract: provenance does not weaken the caller's
    /// obligation to establish well-definedness before using this store path.
    pub fn store_without_well_defined_verification_and_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_without_well_defined_verification_and_infer_with_reason_text_and_state(
            fact,
            reason.store_reason(),
            &InferenceState::new(),
        )
    }

    pub fn store_without_well_defined_verification_and_infer_with_reason_and_state(
        &mut self,
        fact: Fact,
        reason: InferReason,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_without_well_defined_verification_and_infer_with_reason_text_and_state(
            fact,
            reason.store_reason(),
            inference_state,
        )
    }

    pub fn store_fact_with_trust_and_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_without_well_defined_verification_and_infer_with_reason(fact, reason)
    }

    fn store_without_well_defined_verification_and_infer_with_reason_text_and_state(
        &mut self,
        fact: Fact,
        reason_text: String,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if self.non_forall_fact_is_cached(&fact) {
            return self.infer_with_state(&fact, inference_state);
        }
        let output_fact = fact.clone();
        let may_store_forall_projections = matches!(&fact, Fact::ForallFact(_));

        let ret = match fact {
            Fact::AtomicFact(_)
            | Fact::ExistFact(_)
            | Fact::OrFact(_)
            | Fact::AndFact(_)
            | Fact::ChainFact(_)
            | Fact::NotForall(_) => {
                self.store_whole_fact_update_cache_known_fact_and_infer(fact, inference_state)
            }
            Fact::ForallFact(forall_fact) => self
                .store_forall_fact_without_well_defined_verified_and_infer_with_state(
                    forall_fact,
                    inference_state,
                ),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self
                .store_forall_fact_with_iff_without_well_defined_verified_and_infer_with_state(
                    forall_fact_with_iff,
                    inference_state,
                ),
        };

        let mut nested_infer_result = ret?;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &output_fact,
            reason_text,
            &mut nested_infer_result,
        );
        if may_store_forall_projections && self.known_fact_id_for_fact(&output_fact)?.is_none() {
            infer_result.new_infer_result_inside(nested_infer_result);
        }
        Ok(infer_result)
    }

    pub fn store_fact_without_forall_coverage_check_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_fact_without_forall_coverage_check_and_infer_with_reason_and_state(
            fact,
            InferReason::StoredFactWithoutForallCoverageCheck.store_reason(),
            &InferenceState::new(),
        )
    }

    pub fn store_fact_without_forall_coverage_check_and_infer_with_state(
        &mut self,
        fact: Fact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_fact_without_forall_coverage_check_and_infer_with_reason_and_state(
            fact,
            InferReason::StoredFactWithoutForallCoverageCheck.store_reason(),
            inference_state,
        )
    }

    pub fn store_fact_without_forall_coverage_check_and_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_fact_without_forall_coverage_check_and_infer_with_reason_and_state(
            fact,
            reason,
            &InferenceState::new(),
        )
    }

    fn store_fact_without_forall_coverage_check_and_infer_with_reason_and_state(
        &mut self,
        fact: Fact,
        reason: impl Into<String>,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.into();
        let output_fact = fact.clone();
        let mut nested_infer_result =
            self.store_whole_fact_update_cache_known_fact_and_infer(fact, inference_state)?;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &output_fact,
            reason_text,
            &mut nested_infer_result,
        );
        Ok(infer_result)
    }

    pub fn store_forall_fact_without_well_defined_verified_and_infer(
        &mut self,
        forall_fact: ForallFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_forall_fact_without_well_defined_verified_and_infer_with_state(
            forall_fact,
            &InferenceState::new(),
        )
    }

    pub fn store_forall_fact_without_well_defined_verified_and_infer_with_state(
        &mut self,
        mut forall_fact: ForallFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        forall_fact.expand_then_facts_with_order_chain_closure()?;

        let coverage_error_detail_lines =
            forall_fact.error_messages_if_forall_param_missing_in_some_then_clause();
        let mut projected_forall_facts = Vec::new();
        if !coverage_error_detail_lines.is_empty()
            && !forall_fact.typed_parameters.has_dependent_param_type()
        {
            for (then_index, _) in coverage_error_detail_lines.iter() {
                let then_fact = &forall_fact.then_facts[*then_index];
                let coverage = forall_fact.forall_param_coverage_for_then_clause(then_fact);
                let mut retained_groups = Vec::new();
                let mut omitted_types_are_nonempty = true;
                for group in forall_fact.typed_parameters.groups.iter() {
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
                        retained_groups.push(TypedParameterGroup::new(
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
                        TypedParameterList::new(retained_groups),
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
                let mut infer_result = SuccessInferResult::new();
                for projected in projected_forall_facts {
                    infer_result.new_infer_result_inside(
                        self.store_forall_fact_without_well_defined_verified_and_infer_with_state(
                            projected,
                            inference_state,
                        )?,
                    );
                }
                return Ok(infer_result);
            }
        }

        let output_fact: Fact = forall_fact.clone().into();
        let mut nested_infer_result = self.store_whole_fact_update_cache_known_fact_and_infer(
            output_fact.clone(),
            inference_state,
        )?;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &output_fact,
            InferReason::StoredForallFact.store_reason(),
            &mut nested_infer_result,
        );
        for projected in projected_forall_facts {
            infer_result.new_infer_result_inside(
                self.store_forall_fact_without_well_defined_verified_and_infer_with_state(
                    projected,
                    inference_state,
                )?,
            );
        }
        Ok(infer_result)
    }

    fn store_forall_fact_with_iff_without_well_defined_verified_and_infer_with_state(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts()?;
        let mut infer_result = self
            .store_forall_fact_without_well_defined_verified_and_infer_with_state(
                forall_then_implies_iff,
                inference_state,
            )?;
        infer_result.new_infer_result_inside(
            self.store_forall_fact_without_well_defined_verified_and_infer_with_state(
                forall_iff_implies_then,
                inference_state,
            )?,
        );
        Ok(infer_result)
    }

    fn store_whole_fact_update_cache_known_fact_and_infer(
        &mut self,
        fact: Fact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if self.non_forall_fact_is_cached(&fact) {
            return self.infer_with_state(&fact, inference_state);
        }
        // A stored forall may be found through its alpha-normalized alias even
        // when this exact Rust structure has not appeared before. Reuse the
        // canonical FactId. Re-index conclusions only when materialization has
        // genuinely changed their binder-normalized structure and introduced
        // an `InstantiatedTemplateObj` as a callable-application head,
        // including one nested inside another function application.
        // Merely alpha-renaming binders must not duplicate indexes, because
        // that can eagerly unfold otherwise opaque equal-set memberships.
        if let Fact::ForallFact(forall_fact) = &fact {
            if let Some(existing_fact_id) = self.known_fact_id_for_fact(&fact)? {
                let current_structural_key = nested_obj_binder_normalized_fact_key(&fact);
                let stored_structural_key = self
                    .stored_fact(existing_fact_id)
                    .map(|stored| nested_obj_binder_normalized_fact_key(&stored.fact))
                    .ok_or_else(|| {
                        StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("known FactId `{existing_fact_id}` has no stored proposition"),
                            fact.line_file(),
                        ))
                    })?;
                if current_structural_key != stored_structural_key
                    && forall_conclusion_contains_instantiated_template_callable_application(
                        forall_fact,
                    )
                {
                    self.top_level_env()
                        .index_additional_structural_spelling_of_existing_forall_fact(
                            forall_fact.clone(),
                            existing_fact_id,
                        )?;
                }
                return self.infer_with_state(&fact, inference_state);
            }
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
        let numeric_order_chain_steps = match &fact {
            Fact::ChainFact(chain_fact) => chain_fact.numeric_order_chain_closure_steps()?,
            _ => Vec::new(),
        };
        let equality_chain_facts = match &fact {
            Fact::ChainFact(chain_fact) => Self::equality_chain_closure_facts(chain_fact)?,
            _ => Vec::new(),
        };
        let transitive_chain_facts = match &fact {
            Fact::ChainFact(chain_fact) => self.transitive_prop_chain_closure_facts(chain_fact)?,
            _ => Vec::new(),
        };
        let fact_id = self.fact_id_for_fact_store(&fact_for_infer)?;
        let equivalent_proposition_lookup_key =
            self.equivalent_proposition_lookup_key_for_fact(&fact_for_infer)?;
        self.top_level_env()
            .store_fact_with_equivalent_proposition_key(
                fact,
                fact_id,
                equivalent_proposition_lookup_key,
            )?;
        let mut transitive_chain_infers =
            self.store_equality_chain_atomic_facts(equality_chain_facts)?;
        transitive_chain_infers.new_infer_result_inside(
            self.store_numeric_order_chain_atomic_facts(numeric_order_chain_steps)?,
        );
        transitive_chain_infers.new_infer_result_inside(
            self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?,
        );
        self.store_fact_cache_keys_with_nested_obj_binders_and_fact_id(&fact_for_infer, fact_id)?;
        if let Some(alpha_key) = alpha_normalized_forall_key {
            if alpha_key != fact_string {
                self.top_level_env()
                    .store_fact_to_cache_known_fact_with_equivalent_proposition_key(
                        alpha_key.clone(),
                        line_file,
                        fact_id,
                        alpha_key,
                    )?;
            }
        }

        transitive_chain_infers
            .new_infer_result_inside(self.infer_with_state(&fact_for_infer, inference_state)?);
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        Ok(transitive_chain_infers)
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AndChainAtomicFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: AndChainAtomicFact,
        reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            fact,
            reason,
            &InferenceState::new(),
        )
    }

    fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
        &mut self,
        fact: AndChainAtomicFact,
        reason: impl Into<String>,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.into();
        let fact_for_infer: Fact = fact.clone().into();
        let chain_atomic_facts = match &fact {
            AndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.facts_with_order_transitive_closure()?
            }
            _ => Vec::new(),
        };
        let numeric_order_chain_steps = match &fact {
            AndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.numeric_order_chain_closure_steps()?
            }
            _ => Vec::new(),
        };
        let equality_chain_facts = match &fact {
            AndChainAtomicFact::ChainFact(chain_fact) => {
                Self::equality_chain_closure_facts(chain_fact)?
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
        let mut transitive_chain_infers =
            self.store_equality_chain_atomic_facts(equality_chain_facts)?;
        transitive_chain_infers.new_infer_result_inside(
            self.store_numeric_order_chain_atomic_facts(numeric_order_chain_steps)?,
        );
        transitive_chain_infers.new_infer_result_inside(
            self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?,
        );

        self.store_fact_cache_keys_with_nested_obj_binders(&fact_for_infer)?;

        transitive_chain_infers
            .new_infer_result_inside(self.infer_with_state(&fact_for_infer, inference_state)?);
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        let mut nested_infer_result = transitive_chain_infers;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &fact_for_infer,
            reason_text,
            &mut nested_infer_result,
        );
        Ok(infer_result)
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AtomicFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: AtomicFact,
        reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            fact,
            reason,
            &InferenceState::new(),
        )
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
        &mut self,
        fact: AtomicFact,
        reason: impl Into<String>,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.into();
        let infer_wrapped_fact: Fact = fact.clone().into();
        self.top_level_env().store_atomic_fact(fact)?;

        self.store_fact_cache_keys_with_nested_obj_binders(&infer_wrapped_fact)?;

        let mut nested_infer_result =
            self.infer_with_state(&infer_wrapped_fact, inference_state)?;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &infer_wrapped_fact,
            reason_text,
            &mut nested_infer_result,
        );
        Ok(infer_result)
    }

    /// Stores a derived atomic fact whose well-definedness follows from its
    /// source fact, without recursively firing inference for the derived fact.
    pub fn store_derived_atomic_fact_without_infer(
        &mut self,
        fact: AtomicFact,
        reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.into();
        let wrapped_fact: Fact = fact.clone().into();
        self.top_level_env().store_atomic_fact(fact)?;
        self.store_fact_cache_keys_with_nested_obj_binders(&wrapped_fact)?;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output(&wrapped_fact, reason_text, Vec::new());
        Ok(infer_result)
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
        reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            fact,
            reason,
            &InferenceState::new(),
        )
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
        reason: impl Into<String>,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.into();
        let fact_for_infer = fact.clone();
        let output_fact = fact_for_infer.clone().to_fact();
        let chain_atomic_facts = match &fact {
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.facts_with_order_transitive_closure()?
            }
            _ => Vec::new(),
        };
        let numeric_order_chain_steps = match &fact {
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                chain_fact.numeric_order_chain_closure_steps()?
            }
            _ => Vec::new(),
        };
        let equality_chain_facts = match &fact {
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                Self::equality_chain_closure_facts(chain_fact)?
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
        let mut transitive_chain_infers =
            self.store_equality_chain_atomic_facts(equality_chain_facts)?;
        transitive_chain_infers.new_infer_result_inside(
            self.store_numeric_order_chain_atomic_facts(numeric_order_chain_steps)?,
        );
        transitive_chain_infers.new_infer_result_inside(
            self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?,
        );

        self.store_fact_cache_keys_with_nested_obj_binders(&output_fact)?;
        transitive_chain_infers.new_infer_result_inside(
            self.infer_exist_or_and_chain_atomic_fact(&fact_for_infer, inference_state)?,
        );
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        let mut nested_infer_result = transitive_chain_infers;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &output_fact,
            reason_text,
            &mut nested_infer_result,
        );
        Ok(infer_result)
    }

    pub fn store_quantifier_free_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: QuantifierFreeFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_quantifier_free_fact_without_well_defined_verified_and_infer_with_reason(
            fact,
            InferReason::StoredFact.store_reason(),
        )
    }

    pub fn store_quantifier_free_fact_without_well_defined_verified_and_infer_with_reason(
        &mut self,
        fact: QuantifierFreeFact,
        reason: impl Into<String>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_quantifier_free_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            fact,
            reason,
            &InferenceState::new(),
        )
    }

    pub fn store_quantifier_free_fact_without_well_defined_verified_and_infer_with_reason_and_state(
        &mut self,
        fact: QuantifierFreeFact,
        reason: impl Into<String>,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.into();
        let fact_for_infer = fact.clone();
        let output_fact = fact_for_infer.clone().to_fact();
        let chain_atomic_facts = match &fact {
            QuantifierFreeFact::ChainFact(chain_fact) => {
                chain_fact.facts_with_order_transitive_closure()?
            }
            _ => Vec::new(),
        };
        let numeric_order_chain_steps = match &fact {
            QuantifierFreeFact::ChainFact(chain_fact) => {
                chain_fact.numeric_order_chain_closure_steps()?
            }
            _ => Vec::new(),
        };
        let equality_chain_facts = match &fact {
            QuantifierFreeFact::ChainFact(chain_fact) => {
                Self::equality_chain_closure_facts(chain_fact)?
            }
            _ => Vec::new(),
        };
        let transitive_chain_facts = match &fact {
            QuantifierFreeFact::ChainFact(chain_fact) => {
                self.transitive_prop_chain_closure_facts(chain_fact)?
            }
            _ => Vec::new(),
        };
        self.top_level_env().store_quantifier_free_fact(fact)?;
        let mut transitive_chain_infers =
            self.store_equality_chain_atomic_facts(equality_chain_facts)?;
        transitive_chain_infers.new_infer_result_inside(
            self.store_numeric_order_chain_atomic_facts(numeric_order_chain_steps)?,
        );
        transitive_chain_infers.new_infer_result_inside(
            self.store_transitive_prop_chain_atomic_facts(transitive_chain_facts)?,
        );

        self.store_fact_cache_keys_with_nested_obj_binders(&output_fact)?;
        transitive_chain_infers.new_infer_result_inside(
            self.infer_quantifier_free_fact(&fact_for_infer, inference_state)?,
        );
        self.store_chain_atomic_facts_to_cache(chain_atomic_facts)?;
        let mut nested_infer_result = transitive_chain_infers;
        let mut infer_result = SuccessInferResult::new();
        infer_result.add_store_fact_output_from_nested(
            &output_fact,
            reason_text,
            &mut nested_infer_result,
        );
        Ok(infer_result)
    }

    fn store_transitive_prop_chain_atomic_facts(
        &mut self,
        inferences: Vec<RegisteredTransitivePredicateChainClosureInference>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        for inference in inferences {
            let conclusion_fact: Fact = inference.conclusion.clone().into();
            let conclusion_infers = self.store_derived_atomic_fact_without_infer(
                inference.conclusion,
                InferReason::InferredFact.store_reason(),
            )?;
            let conclusion =
                SuccessStoreFactResult::new(conclusion_fact, conclusion_infers.clone());
            result.new_infer_result_inside(conclusion_infers);
            result.add_rule_application_with_premises(
                InferRule::RegisteredTransitivePredicateChainClosure(inference.rule),
                inference.premises,
                vec![conclusion],
            );
        }
        Ok(result)
    }

    fn store_numeric_order_chain_atomic_facts(
        &mut self,
        inferences: Vec<crate::fact::NumericOrderChainClosureStep>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        for inference in inferences {
            let conclusion_fact: Fact = inference.conclusion.clone().into();
            let conclusion_infers = self.store_derived_atomic_fact_without_infer(
                inference.conclusion,
                InferReason::InferredFact.store_reason(),
            )?;
            let conclusion =
                SuccessStoreFactResult::new(conclusion_fact, conclusion_infers.clone());
            result.new_infer_result_inside(conclusion_infers);
            result.add_rule_application_with_premises(
                InferRule::NumericOrderChainClosure(NumericOrderChainClosureInferRule {
                    start_object_index: inference.start_object_index,
                    end_object_index: inference.end_object_index,
                }),
                inference.premises,
                vec![conclusion],
            );
        }
        Ok(result)
    }

    fn store_equality_chain_atomic_facts(
        &mut self,
        inferences: Vec<EqualityChainClosureInference>,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        for inference in inferences {
            let conclusion_fact: Fact = inference.conclusion.clone().into();
            let conclusion_infers = self.store_derived_atomic_fact_without_infer(
                inference.conclusion,
                InferReason::InferredFact.store_reason(),
            )?;
            let conclusion =
                SuccessStoreFactResult::new(conclusion_fact, conclusion_infers.clone());
            result.new_infer_result_inside(conclusion_infers);
            result.add_rule_application_with_premises(
                InferRule::EqualityChainClosure(inference.rule),
                inference.premises,
                vec![conclusion],
            );
        }
        Ok(result)
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

    pub fn store_fact_cache_keys_with_nested_obj_binders(
        &mut self,
        fact: &Fact,
    ) -> Result<FactId, RuntimeError> {
        let fact_id = self.fact_id_for_fact_store(fact)?;
        self.store_fact_cache_keys_with_nested_obj_binders_and_fact_id(fact, fact_id)?;
        Ok(fact_id)
    }

    fn fact_id_for_fact_store(&mut self, fact: &Fact) -> Result<FactId, RuntimeError> {
        Ok(fact.fact_id())
    }

    pub fn equivalent_proposition_lookup_key_for_fact(
        &self,
        fact: &Fact,
    ) -> Result<FactString, RuntimeError> {
        match fact {
            Fact::ForallFact(forall_fact) => self.alpha_normalized_forall_cache_key(forall_fact),
            Fact::ExistFact(exist_fact) => self.alpha_normalized_exist_fact_id_key(exist_fact),
            _ => Ok(nested_obj_binder_normalized_fact_key(fact)),
        }
    }

    fn store_fact_cache_keys_with_nested_obj_binders_and_fact_id(
        &mut self,
        fact: &Fact,
        fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        let line_file = fact.line_file();
        let fact_string = fact.to_string();
        let normalized_key = nested_obj_binder_normalized_fact_key(fact);
        let alpha_normalized_forall_key = match fact {
            Fact::ForallFact(forall_fact) => {
                Some(self.alpha_normalized_forall_cache_key(forall_fact)?)
            }
            _ => None,
        };
        let alpha_normalized_exist_key = match fact {
            Fact::ExistFact(exist_fact) => {
                Some(self.alpha_normalized_exist_fact_id_key(exist_fact)?)
            }
            _ => None,
        };
        let equivalent_proposition_lookup_key = alpha_normalized_forall_key
            .as_ref()
            .or(alpha_normalized_exist_key.as_ref())
            .cloned()
            .unwrap_or_else(|| normalized_key.clone());
        let existing_fact = self
            .top_level_env()
            .facts
            .stored_facts
            .stored_fact(fact_id)
            .map(|stored| stored.fact.clone());
        if let Some(existing_fact) = existing_fact {
            if existing_fact.to_string() != fact_string
                && self.known_fact_id_for_fact(fact)? != Some(fact_id)
            {
                return Err(StoreFactRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "FactId `{fact_id}` already identifies `{existing_fact}`, cannot retarget it to `{fact}`"
                        ),
                        fact.line_file(),
                    ),
                )
                .into());
            }
        } else {
            self.top_level_env()
                .record_stored_fact_with_equivalent_proposition_key(
                    fact.clone(),
                    fact_id,
                    equivalent_proposition_lookup_key.clone(),
                )?;
        }
        self.top_level_env()
            .store_fact_to_cache_known_fact_with_equivalent_proposition_key(
                fact_string.clone(),
                line_file.clone(),
                fact_id,
                equivalent_proposition_lookup_key.clone(),
            )?;
        if normalized_key != fact_string {
            self.top_level_env()
                .store_fact_to_cache_known_fact_with_equivalent_proposition_key(
                    normalized_key.clone(),
                    line_file,
                    fact_id,
                    equivalent_proposition_lookup_key.clone(),
                )?;
        }
        if let Some(alpha_key) = alpha_normalized_exist_key {
            if alpha_key != fact_string && alpha_key != normalized_key {
                self.top_level_env()
                    .store_fact_to_cache_known_fact_with_equivalent_proposition_key(
                        alpha_key,
                        fact.line_file(),
                        fact_id,
                        equivalent_proposition_lookup_key,
                    )?;
            }
        }
        Ok(())
    }

    /// Mathematical contract: store a fact without deriving consequences only
    /// after central well-definedness succeeds, except at the explicit
    /// trusted-source boundary.
    pub fn verify_well_defined_and_store_without_infer(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let verify_state = match &fact {
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => VerifyState::initial(),
            _ => VerifyState::final_round(),
        };
        self.verify_well_defined_and_store_without_infer_with_state(fact, &verify_state, reason)
    }

    /// Mathematical contract: the state-aware form preserves a caller's
    /// recursion restrictions while staging a checked fact without deriving
    /// consequences from it.
    pub fn verify_well_defined_and_store_without_infer_with_state(
        &mut self,
        fact: Fact,
        verify_state: &VerifyState,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if !self.current_execution_is_trusted_source() {
            self.verify_fact_well_defined_result(&fact, verify_state)?;
        }

        self.store_fact_without_well_defined_verified_and_without_infer_with_reason(fact, reason)
    }

    pub fn store_fact_without_well_defined_verified_and_without_infer_with_reason(
        &mut self,
        fact: Fact,
        reason: InferReason,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let reason_text = reason.store_reason();
        if self.non_forall_fact_is_cached(&fact) {
            return Ok(SuccessInferResult::new());
        }
        let fact_id = self.fact_id_for_fact_store(&fact)?;
        let equivalent_proposition_lookup_key =
            self.equivalent_proposition_lookup_key_for_fact(&fact)?;
        self.top_level_env()
            .store_fact_with_equivalent_proposition_key(
                fact.clone(),
                fact_id,
                equivalent_proposition_lookup_key,
            )?;
        self.store_fact_cache_keys_with_nested_obj_binders_and_fact_id(&fact, fact_id)?;

        let mut infer_result = SuccessInferResult::new();
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
    ) -> Result<Vec<RegisteredTransitivePredicateChainClosureInference>, RuntimeError> {
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

        let adjacent_facts = chain_fact.facts()?;
        let mut inferences = Vec::new();
        for i in 0..chain_fact.objs.len() {
            for j in i + 2..chain_fact.objs.len() {
                inferences.push(RegisteredTransitivePredicateChainClosureInference {
                    rule: RegisteredTransitivePredicateChainClosureInferRule {
                        predicate_name: prop_name.clone(),
                        start_object_index: i,
                        end_object_index: j,
                    },
                    premises: adjacent_facts[i..j]
                        .iter()
                        .cloned()
                        .map(Fact::from)
                        .collect(),
                    conclusion: NormalAtomicFact::new(
                        chain_fact.prop_names[0].clone(),
                        vec![chain_fact.objs[i].clone(), chain_fact.objs[j].clone()],
                        chain_fact.line_file.clone(),
                    )
                    .into(),
                });
            }
        }
        Ok(inferences)
    }

    fn is_transitive_prop_name_known(&self, prop_name: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if env.predicate_algebraic_properties.is_transitive(prop_name) {
                return true;
            }
        }
        false
    }

    fn equality_chain_closure_facts(
        chain_fact: &ChainFact,
    ) -> Result<Vec<EqualityChainClosureInference>, RuntimeError> {
        if chain_fact.objs.len() < 3
            || chain_fact
                .prop_names
                .iter()
                .any(|name| name.to_string() != EQUAL)
        {
            return Ok(Vec::new());
        }
        let adjacent_facts = chain_fact.facts()?;
        let mut inferences = Vec::new();
        for start_object_index in 0..chain_fact.objs.len() {
            for end_object_index in start_object_index + 2..chain_fact.objs.len() {
                inferences.push(EqualityChainClosureInference {
                    rule: EqualityChainClosureInferRule {
                        start_object_index,
                        end_object_index,
                    },
                    premises: adjacent_facts[start_object_index..end_object_index]
                        .iter()
                        .cloned()
                        .map(Fact::from)
                        .collect(),
                    conclusion: EqualFact::new(
                        chain_fact.objs[start_object_index].clone(),
                        chain_fact.objs[end_object_index].clone(),
                        chain_fact.line_file.clone(),
                    )
                    .into(),
                });
            }
        }
        Ok(inferences)
    }
}

/// Template materialization sometimes changes a callable conclusion from an
/// identifier-headed application into an application whose head is the
/// public `InstantiatedTemplateObj`. The known-forall matcher indexes callable
/// head structure, so that spelling needs an alias under the existing FactId.
///
/// A bare instantiated template object used as a set is deliberately excluded:
/// membership through an opaque equal-set alias must continue to unfold only
/// when verification demands it.
fn forall_conclusion_contains_instantiated_template_callable_application(
    forall_fact: &ForallFact,
) -> bool {
    fn contains_template_callable_application(object: &Obj) -> bool {
        let Obj::FnObj(function) = object else {
            return false;
        };
        matches!(
            function.head.as_ref(),
            FnObjHead::InstantiatedTemplateObj(_)
        ) || function
            .body
            .iter()
            .flatten()
            .any(|object| contains_template_callable_application(object.as_ref()))
    }

    forall_fact.then_facts.iter().any(|conclusion| {
        let arguments = match conclusion {
            ExistOrAndChainAtomicFact::AtomicFact(fact) => fact.get_args_from_fact_ref(),
            ExistOrAndChainAtomicFact::AndFact(fact) => fact.get_args_from_fact_ref(),
            ExistOrAndChainAtomicFact::ChainFact(fact) => fact.get_args_from_fact_ref(),
            ExistOrAndChainAtomicFact::OrFact(fact) => fact.get_args_from_fact_ref(),
            ExistOrAndChainAtomicFact::ExistFact(fact) => fact.get_args_from_fact_ref(),
        };
        arguments
            .into_iter()
            .any(contains_template_callable_application)
    })
}

#[cfg(test)]
#[path = "../../tests/unit/runtime/fact_storage/registered_transitive_predicate_chain_result_tests.rs"]
mod registered_transitive_predicate_chain_result_tests;

#[cfg(test)]
#[path = "../../tests/unit/runtime/fact_storage/equality_chain_result_tests.rs"]
mod equality_chain_result_tests;
