//! Combined and shared verification proof composition.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_combined_fact_proof_from_result(
        &mut self,
        target: &Fact,
        combined: &SuccessCombinedFactProofResult,
    ) -> Result<Option<String>, String> {
        if let Some(primary) = combined.primary.as_ref() {
            if primary.fact().to_string() != target.to_string() {
                return Err("combined primary proof changed its target".into());
            }
            for (index, step) in combined.steps.iter().enumerate() {
                let Some(factual) = step.factual_success() else {
                    return Err(format!("combined proof step {index} is not factual"));
                };
                if factual.store.fact.to_string() != factual.fact().to_string() {
                    return Err(format!(
                        "combined proof step {index} changed between verification and store"
                    ));
                }
                let Some(proof) = self.construct_lean_proof_from_direct_fact_result(factual)?
                else {
                    return Ok(None);
                };
                let fact_id = factual
                    .store
                    .fact_id
                    .ok_or_else(|| format!("combined proof step {index} has no frozen FactId"))?;
                let fact = factual.fact();
                if let Some(native_equality) =
                    self.construct_lean_native_equality_proof_from_direct_fact_result(factual)?
                {
                    self.retain_native_equality_proof_in_current_environment(
                        fact_id,
                        &fact,
                        native_equality,
                    )?;
                }
                if let Some(existing) = self.environment_stack.fact_propositions.get(&fact_id) {
                    if existing.to_string() != fact.to_string() {
                        return Err(format!(
                            "combined proof step {index} reused `{fact_id}` for another proposition"
                        ));
                    }
                } else {
                    self.environment_stack
                        .fact_names
                        .insert(fact_id, format!("({proof})"));
                    self.environment_stack
                        .fact_propositions
                        .insert(fact_id, fact);
                }
            }
            return self.construct_lean_proof_from_shared_verify_fact_result(primary);
        }

        let components = conjunction_components(target)?;
        if components.len() != combined.steps.len() {
            return Err("combined fact proof changed its component arity".into());
        }
        let mut proofs = Vec::with_capacity(components.len());
        for (component, step) in components.iter().zip(combined.steps.iter()) {
            let factual = step
                .factual_success()
                .ok_or_else(|| "combined proof child is not factual".to_string())?;
            if factual.fact().to_string() != component.to_string() {
                return Err("combined proof child changed its component".into());
            }
            let proof = self.construct_lean_proof_from_direct_fact_result(factual)?;
            let Some(proof) = proof else {
                return Ok(None);
            };
            if factual.store.fact.to_string() != component.to_string() {
                return Err("combined proof component changed in its store Result".into());
            }
            if let Some(fact_id) = factual.store.fact_id {
                if let Some(native_equality) =
                    self.construct_lean_native_equality_proof_from_direct_fact_result(factual)?
                {
                    self.retain_native_equality_proof_in_current_environment(
                        fact_id,
                        component,
                        native_equality,
                    )?;
                }
                if let Some(existing) = self.environment_stack.fact_propositions.get(&fact_id) {
                    if existing.to_string() != component.to_string() {
                        return Err(format!(
                            "combined proof component reused `{fact_id}` for another proposition"
                        ));
                    }
                } else {
                    self.environment_stack
                        .fact_names
                        .insert(fact_id, format!("({proof})"));
                    self.environment_stack
                        .fact_propositions
                        .insert(fact_id, component.clone());
                }
            }
            proofs.push(proof);
        }
        Ok(Some(right_associated_conjunction_proof(&proofs)?))
    }

    pub(in super::super) fn construct_lean_proof_from_shared_verify_fact_result(
        &mut self,
        verification: &SuccessVerifyFactResult,
    ) -> Result<Option<String>, String> {
        let source_fact = verification.fact();
        match verification.proof() {
            SuccessFactProofResult::StoredFactCitation(citation) => {
                self.construct_lean_stored_fact_citation_proof_from_result(&source_fact, citation)
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => self
                .construct_lean_checked_function_definition_reduction_from_result(
                    &source_fact,
                    &result.verification,
                )
                .map(Some),
            SuccessFactProofResult::DefinitionReduction(_)
            | SuccessFactProofResult::DiagnosticOnly(_) => Ok(None),
            SuccessFactProofResult::BuiltinRule(builtin)
            | SuccessFactProofResult::BuiltinStrategy(builtin) => {
                if let Some(BuiltinRuleEvidence::ListSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_list_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::LiteralSetNonempty)
                ) {
                    return self.construct_lean_literal_set_nonempty_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::LiteralSetSubset)
                ) {
                    return self.construct_lean_literal_set_subset_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::SetBuilderSubsetBase)
                ) {
                    return self.construct_lean_set_builder_subset_base_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::SetBuilderInPowerSetViaParamSubset)
                ) {
                    return self
                        .construct_lean_set_builder_in_power_set_via_param_subset_from_result(
                            &source_fact,
                            &builtin.subgoals,
                        );
                }
                if let Some(BuiltinRuleEvidence::RefinedNumericMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_refined_numeric_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::NotEqualSymmetry)
                ) {
                    return self.construct_lean_not_equal_symmetry_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::DisjunctionIntroduction(_))
                ) {
                    let Some(BuiltinRuleEvidence::DisjunctionIntroduction(evidence)) =
                        builtin.evidence.typed()
                    else {
                        unreachable!("disjunction evidence checked above")
                    };
                    return self.construct_lean_disjunction_introduction_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_definition_projection_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::SetBuilderMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_builder_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::TupleCartesianMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_tuple_cartesian_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::IntegerRangeSumPointwiseOrder(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_integer_range_sum_pointwise_order_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_application_return_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionApplicationInRange(evidence)) =
                    builtin.evidence.typed()
                {
                    return self
                        .construct_lean_function_application_in_range_from_result(
                            &source_fact,
                            evidence,
                            &builtin.subgoals,
                        )
                        .map(Some);
                }
                if let Some(BuiltinRuleEvidence::FunctionRangeSubset(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_range_subset_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RealIntervalSubsetReal(evidence)) =
                    builtin.evidence.typed()
                {
                    return self
                        .construct_lean_real_interval_subset_real_from_result(
                            &source_fact,
                            evidence,
                            &builtin.subgoals,
                        )
                        .map(Some);
                }
                if let Some(BuiltinRuleEvidence::Arithmetic(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_arithmetic_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_real_arithmetic_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::IntegerMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_integer_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::IntegerRangeSumMembership)
                ) {
                    return self.construct_lean_integer_range_sum_membership_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::NaturalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_natural_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::PositiveNaturalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_positive_natural_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RationalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_rational_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Set(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_set_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::KnownEqualityPath(evidence)) =
                    builtin.evidence.typed()
                {
                    return Ok(Some(self.construct_lean_known_equality_path_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    )?));
                }
                if let Some(BuiltinRuleEvidence::SetRelationDuality(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_relation_duality_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    if !builtin.subgoals.is_empty() {
                        return Err(
                            "shared registered reflexive-predicate proof retained child Results"
                                .into(),
                        );
                    }
                    return Ok(Some(
                        construct_lean_registered_reflexive_predicate_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    ));
                }
                if let Some(BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_symmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_antisymmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::StructuralDefinitionCongruence(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_structural_definition_congruence_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::StructuralKnownEqualityCongruence(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_structural_known_equality_congruence_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::IntegralPolynomialNormalization(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_integral_polynomial_normalization_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_complex_algebraic_normalization_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RationalAlgebraicNormalization(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_rational_algebraic_normalization_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::AbsoluteValue(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_absolute_value_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Extrema(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_extrema_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Aggregate(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_aggregate_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(evidence) = builtin.evidence.typed() {
                    if let Some(limitation) = direct_builtin_rule_compiler_limitation(evidence) {
                        let children = builtin
                            .subgoals
                            .iter()
                            .filter_map(StmtResult::factual_success)
                            .map(|child| child.fact().to_string())
                            .collect::<Vec<_>>()
                            .join("; ");
                        return Err(format!(
                            "{limitation}; target `{source_fact}`; children [{children}]"
                        ));
                    }
                }
                if !builtin.subgoals.is_empty() {
                    return Ok(None);
                }
                match builtin.evidence.typed() {
                    Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) => {
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "shared object-reflexivity evidence targets a non-equality fact"
                                    .into(),
                            );
                        };
                        if evidence.expected_target.to_string() != source_fact.to_string()
                            || obj_equality_key(&equality.left) != obj_equality_key(&equality.right)
                        {
                            return Err(
                                "shared object-reflexivity evidence changed its target".into()
                            );
                        }
                        Ok(Some(format!(
                            "Litex.Same.refl {}",
                            render_obj(&equality.left, &self.environment_stack)?
                        )))
                    }
                    Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared rational-normalization evidence changed its target".into(),
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                        if evidence.left_evaluation.value.normalized_value
                            != evidence.right_evaluation.value.normalized_value
                        {
                            return Err(
                                "shared rational-normalization retained unequal normal forms"
                                    .into(),
                            );
                        }
                        Ok(Some(
                            "Litex.Same.ofEq (by norm_num [Litex.abs, Litex.min, Litex.max, Litex.tupleDim, Litex.TupleShape.dimension])"
                                .into(),
                        ))
                    }
                    Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) => {
                        self.construct_lean_complex_algebraic_normalization_from_result(
                            &source_fact,
                            evidence,
                            &builtin.subgoals,
                        )
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) => {
                        validate_closed_numeric_comparison_builtin_rule_evidence(
                            &source_fact,
                            evidence,
                        )?;
                        Ok(Some(render_closed_numeric_comparison_fact_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::OrderReflexivity(evidence)) => Ok(Some(
                        construct_lean_order_reflexivity_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::RuntimeResolvedNumericComparison(evidence)) => self
                        .construct_lean_runtime_resolved_numeric_comparison_from_assignment_result(
                            &source_fact,
                            evidence,
                        )
                        .map(Some),
                    Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared closed-numeric-membership changed its target".into()
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.evaluation)?;
                        Ok(Some(render_closed_numeric_membership_from_result(
                            &source_fact,
                            evidence.target_set,
                            &evidence.evaluation,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericNonmembership(evidence)) => self
                        .construct_lean_closed_numeric_nonmembership_from_result(
                            &source_fact,
                            evidence,
                        ),
                    Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) => Ok(Some(
                        self.construct_lean_standard_set_nonempty_from_result(
                            &source_fact,
                            evidence,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::NativeConstantMembership(rule)) => Ok(Some(
                        self.construct_lean_native_constant_membership_from_result(
                            &source_fact,
                            *rule,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::StandardSetSubset) => Ok(Some(
                        self.construct_lean_standard_set_subset_from_result(&source_fact)?,
                    )),
                    Some(BuiltinRuleEvidence::PrimeU64Reflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            true,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::CoprimeNaturalReflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            false,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::FiniteSet(rule)) => Ok(Some(
                        self.construct_lean_finite_set_from_result(&source_fact, *rule)?,
                    )),
                    Some(BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule)) => Ok(
                        Some(self.construct_lean_complex_membership_closure_from_result(
                            &source_fact,
                            *rule,
                        )?),
                    ),
                    Some(BuiltinRuleEvidence::TupleLiteralShape) => Ok(Some(
                        self.construct_lean_tuple_literal_shape_from_result(&source_fact)?,
                    )),
                    None => Ok(None),
                    Some(evidence) => unreachable!(
                        "typed shared builtin evidence must be handled before the terminal direct compiler dispatch: {evidence:?}"
                    ),
                }
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                self.construct_lean_combined_fact_proof_from_result(&source_fact, combined)
            }
            SuccessFactProofResult::KnownForallInstantiation(instantiation) => self
                .construct_lean_known_forall_instantiation_from_result(&source_fact, instantiation),
            SuccessFactProofResult::Transform(transformation) => self
                .construct_lean_single_fact_transformation_from_result(
                    &source_fact,
                    transformation,
                ),
            SuccessFactProofResult::Reuse(reuse) => {
                self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())
            }
            SuccessFactProofResult::ForallProof(_) => Ok(None),
        }
    }
}
