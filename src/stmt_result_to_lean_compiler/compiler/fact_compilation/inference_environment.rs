//! Typed inference compilation in the current compiler environment.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Compile the typed inference children owned by one active Result scope.
    ///
    /// The returned records retain identity, proposition, name, and proof as
    /// separate fields. Callers decide whether those records become local
    /// `have`s, anonymous-function `let`s, or top-level theorems. No caller is
    /// permitted to recover semantic fields by parsing rendered Lean source.
    pub(in super::super) fn compile_typed_inference_results_in_current_compiler_environment(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        availability: CompiledInferenceFactAvailabilityInLeanEnvironment,
        result_layer: &str,
        force_replay_visible_conclusions: Option<&HashSet<FactId>>,
    ) -> Result<Vec<CompiledInferenceFactProofStep>, String> {
        validate_typed_infer_result_identity_completeness(infers, result_layer)?;

        let mut compiled_inference_fact_proof_steps = Vec::new();
        let mut advertised_conclusions = HashSet::new();
        for (store_index, output) in infers.store_fact_outputs.iter().enumerate() {
            let source_fact_id = output.fact_id.ok_or_else(|| {
                format!("{result_layer} store {store_index} has no source FactId")
            })?;
            if !allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                *allowed_fact_id == source_fact_id
                    && fact.to_string() == output.itself_and_why_itself_is_stored.0.to_string()
            }) {
                return Err(format!(
                    "{result_layer} store {store_index} is not owned by a visible source fact"
                ));
            }
            if output.inferred_facts.len() != output.inferred_fact_ids.len() {
                return Err(format!(
                    "{result_layer} store {store_index} changed its inferred FactId arity"
                ));
            }
            for (fact, fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
            {
                let fact_id = fact_id.ok_or_else(|| {
                    format!("{result_layer} advertised inferred fact `{fact}` without a FactId")
                })?;
                if !advertised_conclusions.insert((fact_id, fact.to_string())) {
                    return Err(format!(
                        "{result_layer} advertised inferred FactId `{fact_id}` more than once"
                    ));
                }
            }
        }

        let mut compiled_conclusions = HashSet::new();
        for (application_index, application) in infers.rule_applications.iter().enumerate() {
            let expected_premise_count = match &application.rule {
                InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => 2,
                InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
                    _,
                ) => 3,
                InferRule::EqualityChainClosure(rule) => rule
                    .end_object_index
                    .checked_sub(rule.start_object_index)
                    .ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} reversed its equality-chain interval"
                        )
                    })?,
                InferRule::NumericOrderChainClosure(rule) => rule
                    .end_object_index
                    .checked_sub(rule.start_object_index)
                    .ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} reversed its numeric-order interval"
                        )
                    })?,
                _ => 1,
            };
            if !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                || application.premises.len() != expected_premise_count
                || application.conclusions.len() != 1
            {
                return Err(format!(
                    "{result_layer} application {application_index} has no supported direct compiler-environment consumer"
                ));
            }
            let premise = &application.premises[0];
            let premise_fact_id = premise.fact_id.ok_or_else(|| {
                format!("{result_layer} application {application_index} premise has no FactId")
            })?;
            let premise_key = (premise_fact_id, premise.fact.to_string());
            if !allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                *allowed_fact_id == premise_fact_id && fact.to_string() == premise.fact.to_string()
            }) && !compiled_conclusions.contains(&premise_key)
                && !self
                    .environment_stack
                    .fact_propositions
                    .get(&premise_fact_id)
                    .is_some_and(|visible| visible.to_string() == premise.fact.to_string())
            {
                let allowed = allowed_sources
                    .iter()
                    .map(|(fact_id, fact)| format!("{fact_id}:{fact}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(format!(
                    "{result_layer} application {application_index} ({:?}) cites `{premise_fact_id}:{}` outside this Result layer; allowed exact roots or earlier typed conclusions: [{allowed}]",
                    application.rule,
                    premise.fact,
                ));
            }
            if matches!(application.rule, InferRule::EqualityChainClosure(_)) {
                for (premise_index, premise) in application.premises.iter().enumerate() {
                    let premise_fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    if !allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                        *allowed_fact_id == premise_fact_id
                            && fact.to_string() == premise.fact.to_string()
                    }) {
                        return Err(format!(
                            "{result_layer} application {application_index} equality premise {premise_index} is outside its source chain"
                        ));
                    }
                }
            }

            let conclusion = &application.conclusions[0];
            let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
                format!("{result_layer} application {application_index} conclusion has no FactId")
            })?;
            let conclusion_key = (conclusion_fact_id, conclusion.fact.to_string());
            let force_replay = force_replay_visible_conclusions
                .is_some_and(|fact_ids| fact_ids.contains(&conclusion_fact_id));
            let conclusion_already_visible = if self
                .environment_stack
                .fact_propositions
                .contains_key(&conclusion_fact_id)
            {
                resolve_fact_citation(
                    &conclusion_fact_id,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                !force_replay
            } else {
                false
            };
            let conclusion_is_advertised = advertised_conclusions.contains(&conclusion_key);
            if !conclusion_is_advertised && !conclusion_already_visible && !force_replay {
                return Err(format!(
                    "{result_layer} application {application_index} conclusion is neither in its ordered store output nor already visible by exact FactId"
                ));
            }
            if conclusion_is_advertised
                && !compiled_conclusions.insert(conclusion_key)
                && !conclusion_already_visible
            {
                return Err(format!(
                    "{result_layer} application {application_index} repeats an inferred conclusion before its exact FactId is visible"
                ));
            }
            if let InferRule::NumericOrderChainClosure(rule) = &application.rule {
                if rule.end_object_index < rule.start_object_index + 2 {
                    return Err(format!(
                        "{result_layer} application {application_index} does not span a non-adjacent order consequence"
                    ));
                }
                let descending = application.premises.iter().all(|premise| {
                    matches!(
                        premise.fact,
                        Fact::AtomicFact(
                            AtomicFact::GreaterFact(_) | AtomicFact::GreaterEqualFact(_)
                        )
                    )
                });
                let ascending = application.premises.iter().all(|premise| {
                    matches!(
                        premise.fact,
                        Fact::AtomicFact(
                            AtomicFact::LessFact(_) | AtomicFact::LessEqualFact(_)
                        )
                    )
                });
                if ascending == descending {
                    return Err(format!(
                        "{result_layer} application {application_index} mixes incompatible order directions"
                    ));
                }
                let ordered_premises = if descending {
                    application.premises.iter().rev().collect::<Vec<_>>()
                } else {
                    application.premises.iter().collect::<Vec<_>>()
                };
                let mut rendered = Vec::with_capacity(ordered_premises.len());
                let mut expected_left = None;
                let mut expected_right: Option<Obj> = None;
                for (premise_index, premise) in ordered_premises.iter().enumerate() {
                    let fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    let visible = allowed_sources.iter().any(|(allowed_id, fact)| {
                        *allowed_id == fact_id && fact.to_string() == premise.fact.to_string()
                    }) || compiled_conclusions
                        .contains(&(fact_id, premise.fact.to_string()));
                    if !visible {
                        return Err(format!(
                            "{result_layer} application {application_index} order premise {premise_index} is outside its source chain"
                        ));
                    }
                    let (left, right, strict) = order_relation_parts(&premise.fact)?;
                    if let Some(previous_right) = expected_right.as_ref() {
                        if obj_equality_key(previous_right) != obj_equality_key(left) {
                            return Err(format!(
                                "{result_layer} application {application_index} order premises are not endpoint-contiguous"
                            ));
                        }
                    } else {
                        expected_left = Some(left.clone());
                    }
                    expected_right = Some(right.clone());
                    rendered.push((
                        resolve_fact_citation(
                            &fact_id,
                            &premise.fact,
                            &self.environment_stack,
                        )?,
                        strict,
                    ));
                }
                let (conclusion_left, conclusion_right, conclusion_strict) =
                    order_relation_parts(&conclusion.fact)?;
                if obj_equality_key(expected_left.as_ref().ok_or_else(|| {
                    format!(
                        "{result_layer} application {application_index} retained no order premises"
                    )
                })?) != obj_equality_key(conclusion_left)
                    || obj_equality_key(expected_right.as_ref().ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} retained no order endpoint"
                        )
                    })?) != obj_equality_key(conclusion_right)
                    || conclusion_strict != rendered.iter().any(|(_, strict)| *strict)
                {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its order endpoints or strictness"
                    ));
                }
                if !conclusion_already_visible {
                    let (mut proof, mut proof_is_strict) = rendered[0].clone();
                    for (next, next_is_strict) in rendered.iter().skip(1) {
                        let theorem = match (proof_is_strict, *next_is_strict) {
                            (false, false) => "Litex.Le.trans",
                            (false, true) => "Litex.Le.transLt",
                            (true, false) => "Litex.Lt.transLe",
                            (true, true) => "Litex.Lt.trans",
                        };
                        proof = format!("{theorem} ({proof}) ({next})");
                        proof_is_strict |= *next_is_strict;
                    }
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::EqualityChainClosure(rule) = &application.rule {
                if rule.end_object_index < rule.start_object_index + 2 {
                    return Err(format!(
                        "{result_layer} application {application_index} does not span a non-adjacent equality"
                    ));
                }
                let mut expected_left: Option<Obj> = None;
                let mut expected_right: Option<Obj> = None;
                let mut proof_parts = Vec::with_capacity(application.premises.len());
                let mut native_proof_parts = Some(Vec::with_capacity(application.premises.len()));
                for (premise_index, premise) in application.premises.iter().enumerate() {
                    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &premise.fact else {
                        return Err(format!(
                            "{result_layer} application {application_index} premise {premise_index} is not equality"
                        ));
                    };
                    if let Some(previous_right) = expected_right.as_ref() {
                        if obj_equality_key(previous_right) != obj_equality_key(&equality.left) {
                            return Err(format!(
                                "{result_layer} application {application_index} equality premises are not endpoint-contiguous"
                            ));
                        }
                    } else {
                        expected_left = Some(equality.left.clone());
                    }
                    expected_right = Some(equality.right.clone());
                    let premise_fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    proof_parts.push(resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?);
                    if let Some(parts) = native_proof_parts.as_mut() {
                        if let Some(binding) = self
                            .environment_stack
                            .native_equality_proofs
                            .get(&premise_fact_id)
                        {
                            if binding.fact.to_string() != premise.fact.to_string() {
                                return Err(format!(
                                    "{result_layer} application {application_index} native equality premise {premise_index} changed its FactId proposition"
                                ));
                            }
                            parts.push(binding.proof_expression.clone());
                        } else {
                            native_proof_parts = None;
                        }
                    }
                }
                let Fact::AtomicFact(AtomicFact::EqualFact(conclusion_equality)) =
                    &conclusion.fact
                else {
                    return Err(format!(
                        "{result_layer} application {application_index} equality closure has a non-equality conclusion"
                    ));
                };
                if obj_equality_key(expected_left.as_ref().ok_or_else(|| {
                    format!(
                        "{result_layer} application {application_index} retained no equality premises"
                    )
                })?) != obj_equality_key(&conclusion_equality.left)
                    || obj_equality_key(expected_right.as_ref().ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} retained no equality endpoint"
                        )
                    })?) != obj_equality_key(&conclusion_equality.right)
                {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its equality endpoints"
                    ));
                }
                if !conclusion_already_visible {
                    let mut proof = proof_parts[0].clone();
                    for next in proof_parts.iter().skip(1) {
                        proof = format!("Litex.Same.trans ({proof}) ({next})");
                    }
                    if let Some(native_parts) = native_proof_parts {
                        let mut native_proof = native_parts[0].clone();
                        for next in native_parts.iter().skip(1) {
                            native_proof = format!("Eq.trans ({native_proof}) ({next})");
                        }
                        self.retain_native_equality_proof_in_current_environment(
                            conclusion_fact_id,
                            &conclusion.fact,
                            native_proof,
                        )?;
                    }
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::ConjunctionImpliesComponent(rule) = &application.rule {
                validate_conjunction_component_inference_target(
                    rule,
                    &premise.fact,
                    &conclusion.fact,
                )?;
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    let projection = conjunction_projection(
                        &format!("({premise_name})"),
                        rule.component_index,
                        rule.component_count,
                    )?;
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            projection,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(rule) =
                &application.rule
            {
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    let proof = render_closed_positive_power_equality_membership_inference(
                        rule,
                        &premise.fact,
                        &conclusion.fact,
                        &premise_name,
                        &self.environment_stack,
                    )?;
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if let InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
                rule,
            ) = &application.rule
            {
                let base_positive = &application.premises[1];
                let base_in_z = &application.premises[2];
                for (premise_index, additional) in
                    application.premises.iter().enumerate().skip(1)
                {
                    let fact_id = additional.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} premise {premise_index} has no FactId"
                        )
                    })?;
                    let key = (fact_id, additional.fact.to_string());
                    let visible = allowed_sources.iter().any(|(allowed_fact_id, fact)| {
                        *allowed_fact_id == fact_id
                            && fact.to_string() == additional.fact.to_string()
                    }) || compiled_conclusions.contains(&key)
                        || self
                            .environment_stack
                            .fact_propositions
                            .get(&fact_id)
                            .is_some_and(|fact| fact.to_string() == additional.fact.to_string());
                    if !visible {
                        return Err(format!(
                            "{result_layer} application {application_index} premise {premise_index} is not an exact visible root or earlier typed conclusion"
                        ));
                    }
                }
                if !conclusion_already_visible {
                    let equality_proof = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let base_positive_fact_id = base_positive.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} positivity premise has no FactId"
                        )
                    })?;
                    let base_positive_proof = resolve_fact_citation(
                        &base_positive_fact_id,
                        &base_positive.fact,
                        &self.environment_stack,
                    )?;
                    let base_in_z_fact_id = base_in_z.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} Z premise has no FactId"
                        )
                    })?;
                    resolve_fact_citation(
                        &base_in_z_fact_id,
                        &base_in_z.fact,
                        &self.environment_stack,
                    )?;
                    let (expected_conclusion, proof) =
                        render_positive_integer_base_natural_power_equality_membership_inference(
                            rule,
                            &premise.fact,
                            &base_positive.fact,
                            &base_in_z.fact,
                            &equality_proof,
                            &base_positive_proof,
                            &self.environment_stack,
                        )?;
                    if expected_conclusion.to_string() != conclusion.fact.to_string() {
                        return Err(format!(
                            "{result_layer} application {application_index} changed its transported R+ conclusion"
                        ));
                    }
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if matches!(
                application.rule,
                InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero
                    | InferRule::StrictOrderComparedToZeroImpliesWeakOrder
                    | InferRule::NumericOrderBoundImpliesZeroSign
            ) {
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    if matches!(
                        application.rule,
                        InferRule::NumericOrderBoundImpliesZeroSign
                    ) {
                        let conclusion_proposition =
                            render_fact(&conclusion.fact, &self.environment_stack)?;
                        let conclusion_name = self.next_local_inference_fact_proof_name();
                        let proof = render_numeric_order_bound_implies_zero_sign_inference(
                            &premise.fact,
                            &conclusion.fact,
                            &premise_name,
                            &self.environment_stack,
                        )?;
                        self.retain_compiled_inference_fact_proof_step_in_current_environment(
                            &mut compiled_inference_fact_proof_steps,
                            CompiledInferenceFactProofStep::new(
                                conclusion_fact_id,
                                conclusion.fact.clone(),
                                conclusion_name,
                                conclusion_proposition,
                                proof,
                            ),
                            availability,
                        );
                    } else {
                        validate_order_sign_inference_target(
                            &application.rule,
                            &premise.fact,
                            &conclusion.fact,
                        )?;
                        let transported_premise =
                            transport_zero_ended_order_fact_proof_to_current_numeric_representation(
                                &premise.fact,
                                &premise_name,
                                &self.environment_stack,
                            )?;
                        let conclusion_proposition =
                            render_fact(&conclusion.fact, &self.environment_stack)?;
                        let conclusion_name = self.next_local_inference_fact_proof_name();
                        let proof = match application.rule {
                        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
                            let (source_left, source_right, _) =
                                order_relation_parts(&premise.fact)?;
                            if is_literal_zero(source_left) {
                                format!("Litex.Positive.toNonnegative ({transported_premise})")
                            } else if is_literal_zero(source_right) {
                                format!("Litex.Negative.toNonpositive ({transported_premise})")
                            } else {
                                return Err(format!(
                                    "{result_layer} application {application_index} strict-to-weak premise is not compared with zero"
                                ));
                            }
                        }
                        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
                            let (source_left, source_right, source_is_strict) =
                                order_relation_parts(&premise.fact)?;
                            if is_literal_zero(source_left) {
                                let theorem = if source_is_strict {
                                    "complexNegativeOneMulNegative"
                                } else {
                                    "complexNegativeOneMulNonpositive"
                                };
                                format!("Litex.Rules.{theorem} ({transported_premise})")
                            } else if is_literal_zero(source_right) {
                                let nonpositive_premise = if source_is_strict {
                                    format!("Litex.Negative.toNonpositive ({transported_premise})")
                                } else {
                                    transported_premise
                                };
                                format!(
                                    "Litex.Rules.complexNegativeOneMulNonnegative ({nonpositive_premise})"
                                )
                            } else {
                                return Err(format!(
                                    "{result_layer} application {application_index} negative-one premise is not compared with zero"
                                ));
                            }
                        }
                            _ => unreachable!("order-sign inference was matched above"),
                        };
                        self.retain_compiled_inference_fact_proof_step_in_current_environment(
                            &mut compiled_inference_fact_proof_steps,
                            CompiledInferenceFactProofStep::new(
                                conclusion_fact_id,
                                conclusion.fact.clone(),
                                conclusion_name,
                                conclusion_proposition,
                                proof,
                            ),
                            availability,
                        );
                    }
                }
            } else if matches!(
                application.rule,
                InferRule::SetBuilderBaseMembershipProjection
                    | InferRule::SetBuilderPredicateProjection { .. }
            ) {
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let proof = match &application.rule {
                        InferRule::SetBuilderBaseMembershipProjection => {
                            let (source_element, source_set) = membership_parts(&premise.fact)?;
                            let Obj::SetBuilder(builder) = source_set else {
                                return Err(format!(
                                    "{result_layer} application {application_index} set-builder base projection cites another set constructor"
                                ));
                            };
                            let (target_element, target_set) = membership_parts(&conclusion.fact)?;
                            if obj_equality_key(source_element) != obj_equality_key(target_element)
                                || obj_equality_key(builder.param_set.as_ref())
                                    != obj_equality_key(target_set)
                            {
                                return Err(format!(
                                    "{result_layer} application {application_index} changed its set-builder base projection"
                                ));
                            }
                            format!("Litex.Rules.inBaseOfInSetBuilder ({premise_name})")
                        }
                        InferRule::SetBuilderPredicateProjection { clause_index } => {
                            render_set_builder_predicate_projection_from_fact_and_proof(
                                &conclusion.fact,
                                *clause_index,
                                &premise.fact,
                                &premise_name,
                                &self.environment_stack,
                            )?
                        }
                        _ => unreachable!("set-builder inference was matched above"),
                    };
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if matches!(
                application.rule,
                InferRule::FunctionRangeMembershipImpliesCodomainMembership
            ) {
                let (source_element, source_set) = membership_parts(&premise.fact)?;
                let Obj::FnRange(range) = source_set else {
                    return Err(format!(
                        "{result_layer} application {application_index} function-range codomain projection cites another set constructor"
                    ));
                };
                let (target_element, target_set) = membership_parts(&conclusion.fact)?;
                if obj_equality_key(source_element) != obj_equality_key(target_element) {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its function-range member"
                    ));
                }
                let function_object =
                    LeanTargetObjectRepresentation::lower(range.function.as_ref())?;
                let function = resolve_exact_function_range_type(
                    &function_object,
                    &self.environment_stack,
                )?;
                if LeanTargetObjectRepresentation::lower(target_set)? != *function.return_set {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its function codomain"
                    ));
                }
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let theorem = if function.domain_facts.is_empty() {
                        "Litex.fnRangeOwnSubsetCodomain"
                    } else {
                        "Litex.fnWhereRangeOwnSubsetCodomain"
                    };
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            format!("({theorem} _) _ ({premise_name})"),
                        ),
                        availability,
                    );
                }
            } else if let InferRule::ListSetMembershipImpliesEqualityAlternatives(rule) =
                &application.rule
            {
                let (_, source_set) = membership_parts(&premise.fact)?;
                let Obj::ListSet(list_set) = source_set else {
                    return Err(format!(
                        "{result_layer} application {application_index} literal alternatives cite another set constructor"
                    ));
                };
                if rule.element_count == 0 || rule.element_count != list_set.list.len() {
                    return Err(format!(
                        "{result_layer} application {application_index} changed its literal alternatives arity"
                    ));
                }
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    let proof = render_list_set_membership_elimination_from_fact_and_proof(
                        &conclusion.fact,
                        &premise.fact,
                        &premise_name,
                        &self.environment_stack,
                    )?;
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            } else if matches!(
                application.rule,
                InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_)
            ) {
                if let InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(
                    rule,
                ) = &application.rule
                {
                    let equality_premise = &application.premises[1];
                    let equality_fact_id = equality_premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} application {application_index} set equality has no FactId"
                        )
                    })?;
                    resolve_fact_citation(
                        &equality_fact_id,
                        &equality_premise.fact,
                        &self.environment_stack,
                    )?;
                    validate_membership_in_equal_set_inference_target(
                        rule,
                        &premise.fact,
                        &equality_premise.fact,
                        &conclusion.fact,
                    )?;
                    if !conclusion_already_visible {
                        let premise_name = resolve_fact_citation(
                            &premise_fact_id,
                            &premise.fact,
                            &self.environment_stack,
                        )?;
                        let (source_element, source_set) = membership_parts(&premise.fact)?;
                        let (target_element, target_set) = membership_parts(&conclusion.fact)?;
                        if obj_equality_key(source_element) != obj_equality_key(target_element) {
                            return Err(format!(
                                "{result_layer} application {application_index} changed its membership element"
                            ));
                        }
                        let transparent_set = [
                            (source_set, target_set),
                            (target_set, source_set),
                        ]
                        .into_iter()
                        .find_map(|(candidate_symbol, expected_value)| {
                            let Ok(LeanTargetObjectRepresentation::Symbol {
                                symbol_id,
                                ..
                            }) = LeanTargetObjectRepresentation::lower(candidate_symbol)
                            else {
                                return None;
                            };
                            let definition = self
                                .environment_stack
                                .transparent_object_definitions
                                .get(&symbol_id)?;
                            if definition.defining_equality_fact_id != equality_fact_id
                                || definition.defining_equality.to_string()
                                    != equality_premise.fact.to_string()
                                || obj_equality_key(&definition.value)
                                    != obj_equality_key(expected_value)
                            {
                                return None;
                            }
                            Some(candidate_symbol)
                        })
                        .ok_or_else(|| {
                            format!(
                                "{result_layer} application {application_index} equal-set membership has no exact transparent definition adapter"
                            )
                        })?;
                        let transparent_set_name =
                            render_obj(transparent_set, &self.environment_stack)?;
                        let conclusion_proposition =
                            render_fact(&conclusion.fact, &self.environment_stack)?;
                        let conclusion_name = self.next_local_inference_fact_proof_name();
                        self.retain_compiled_inference_fact_proof_step_in_current_environment(
                            &mut compiled_inference_fact_proof_steps,
                            CompiledInferenceFactProofStep::new(
                                conclusion_fact_id,
                                conclusion.fact.clone(),
                                conclusion_name,
                                conclusion_proposition,
                                format!(
                                    "by\n  simpa [{transparent_set_name}] using ({premise_name})"
                                ),
                            ),
                            availability,
                        );
                    }
                }
            } else if matches!(
                application.rule,
                InferRule::SubsetImpliesElementwiseMembershipForall(_)
                    | InferRule::SupersetImpliesElementwiseMembershipForall(_)
            ) {
                // Litex.Subset is definitionally the elementwise universal
                // proposition retained by this typed inference.  Replay the
                // exact Result edge under its own FactId so later theorem
                // requirements can cite it without reconstructing search.
                validate_set_inclusion_elementwise_forall_inference_target(
                    &application.rule,
                    &premise.fact,
                    &conclusion.fact,
                )?;
                if !conclusion_already_visible {
                    let premise_name = resolve_fact_citation(
                        &premise_fact_id,
                        &premise.fact,
                        &self.environment_stack,
                    )?;
                    // `Litex.Subset` is definitionally this forall. Preserve
                    // the inferred FactId as an alias of the exact premise
                    // proof instead of emitting an eta-expanded theorem that
                    // can accidentally monomorphize a user set's universe.
                    render_fact(&conclusion.fact, &self.environment_stack)?;
                    let lean_reference = match availability {
                        CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName => {
                            premise_name
                        }
                        CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression => {
                            format!("({premise_name})")
                        }
                    };
                    self.environment_stack
                        .fact_names
                        .insert(conclusion_fact_id, lean_reference);
                    self.environment_stack
                        .fact_propositions
                        .insert(conclusion_fact_id, conclusion.fact.clone());
                }
            } else {
                let premise_name = resolve_fact_citation(
                    &premise_fact_id,
                    &premise.fact,
                    &self.environment_stack,
                )?;
                let (premise_element, premise_set) = membership_parts(&premise.fact)?;
                if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                    LeanTargetObjectRepresentation::lower(premise_element)?
                {
                    let source_name = render_obj(premise_element, &self.environment_stack)?;
                    let already_exact = self
                        .environment_stack
                        .exact_carrier_values
                        .get(&symbol_id)
                        .is_some_and(|exact| exact == &source_name);
                    if !already_exact {
                        let lowered_set = LeanTargetObjectRepresentation::lower(premise_set)?;
                        install_numeric_representations_from_membership(
                            symbol_id,
                            &lowered_set,
                            &source_name,
                            &premise_name,
                            &mut self.environment_stack,
                        );
                    }
                }
                let lean_theorem_name = validate_standard_numeric_membership_inference_target(
                    &application.rule,
                    &premise.fact,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                if !conclusion_already_visible {
                    let conclusion_proposition =
                        render_fact(&conclusion.fact, &self.environment_stack)?;
                    let conclusion_name = self.next_local_inference_fact_proof_name();
                    let proof = format!("Litex.Rules.{lean_theorem_name} ({premise_name})");
                    self.retain_compiled_inference_fact_proof_step_in_current_environment(
                        &mut compiled_inference_fact_proof_steps,
                        CompiledInferenceFactProofStep::new(
                            conclusion_fact_id,
                            conclusion.fact.clone(),
                            conclusion_name,
                            conclusion_proposition,
                            proof,
                        ),
                        availability,
                    );
                }
            }
            if !conclusion.infers.is_empty() {
                compiled_inference_fact_proof_steps.extend(
                    self.compile_typed_inference_results_in_current_compiler_environment(
                        &conclusion.infers,
                        &[(conclusion_fact_id, conclusion.fact.clone())],
                        availability,
                        &format!("{result_layer} application {application_index} conclusion"),
                        force_replay_visible_conclusions,
                    )?,
                );
                let mut recursively_compiled = HashSet::new();
                collect_supported_typed_infer_conclusions(
                    &conclusion.infers,
                    &mut recursively_compiled,
                );
                compiled_conclusions.extend(
                    recursively_compiled
                        .into_iter()
                        .filter(|conclusion| advertised_conclusions.contains(conclusion)),
                );
            }
        }

        // Only typed applications become Lean proof steps. Legacy flattened
        // store effects remain inert; if a later Result actually cites one,
        // exact FactId resolution will still fail closed at that use site.
        Ok(compiled_inference_fact_proof_steps)
    }
}
