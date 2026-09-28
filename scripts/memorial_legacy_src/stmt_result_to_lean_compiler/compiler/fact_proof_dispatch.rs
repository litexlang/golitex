use super::*;

impl StmtResultToLeanCompiler {
    /// Returns `None` when the factual proof family explicitly carries a
    /// diagnostic-only Result or has no implemented Lean consumer. A matched
    /// typed certificate that is internally inconsistent is an error, never a
    /// fallback selected from its label.
    pub(super) fn construct_lean_proof_from_direct_fact_result(
        &mut self,
        result: &VerifiedFactResult,
    ) -> Result<Option<String>, String> {
        let source_fact = result.fact();
        match result.proof() {
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
                    Some(BuiltinRuleEvidence::EqualitySymmetry)
                ) {
                    return self.construct_lean_equality_symmetry_from_result(
                        &source_fact,
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
                if let Some(BuiltinRuleEvidence::Arithmetic(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_arithmetic_builtin_from_result(
                        &source_fact,
                        *rule,
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
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    if !builtin.subgoals.is_empty() {
                        return Err(
                            "registered reflexive-predicate proof retained child Results".into(),
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
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactByKnownDirectSuperset
                    ))
                ) {
                    return self.construct_lean_direct_superset_membership_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(evidence) = builtin.evidence.typed() {
                    if let Some(limitation) = direct_builtin_rule_compiler_limitation(evidence) {
                        let children = builtin
                            .subgoals
                            .iter()
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
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err("object-reflexivity evidence changed its target".into());
                        }
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "object-reflexivity evidence targets a non-equality fact".into()
                            );
                        };
                        if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
                            return Err(
                                "object-reflexivity evidence changed its equality endpoints".into(),
                            );
                        }
                        validate_atomic_fact_well_definedness_result(
                            &result.checked,
                            &source_fact,
                        )?;
                        let rendered_object = self
                            .render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.left,
                            )?;
                        let proposition = self
                            .render_fact_using_well_definedness_result(
                                &result.checked,
                                &source_fact,
                            )?;
                        let reflexive_term = if matches!(&equality.left, Obj::Atom(_))
                            && proposition.contains("FnTelescope.Carrier")
                        {
                            format!("(fun {{α}} => {rendered_object})")
                        } else {
                            rendered_object.clone()
                        };
                        let proof = if proposition.contains("ComplexObserver.none") {
                            format!("Litex.Same.reflNoObservation {reflexive_term}")
                        } else {
                            format!("Litex.Same.refl {reflexive_term}")
                        };
                        Ok(Some(proof))
                    }
                    Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err("rational-normalization evidence changed its target".into());
                        }
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "rational-normalization evidence targets a non-equality fact"
                                    .into(),
                            );
                        };
                        if obj_equality_key(&equality.left)
                            != obj_equality_key(&evidence.left_evaluation.expression)
                            || obj_equality_key(&equality.right)
                                != obj_equality_key(&evidence.right_evaluation.expression)
                        {
                            return Err(
                                "rational-normalization evidence changed an equality endpoint"
                                    .into(),
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                        if evidence.left_evaluation.value.normalized_value
                            != evidence.right_evaluation.value.normalized_value
                        {
                            return Err(
                                "rational-normalization evidence retained unequal normal forms"
                                    .into(),
                            );
                        }
                        validate_atomic_fact_well_definedness_result(
                            &result.checked,
                            &source_fact,
                        )?;
                        self.render_object_using_well_definedness_from_fact_result(
                            result,
                            &equality.left,
                        )?;
                        self.render_object_using_well_definedness_from_fact_result(
                            result,
                            &equality.right,
                        )?;
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
                    Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "closed-numeric-membership evidence changed its target".into()
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.evaluation)?;
                        validate_atomic_fact_well_definedness_result(
                            &result.checked,
                            &source_fact,
                        )?;
                        Ok(Some(render_closed_numeric_membership_from_result(
                            &source_fact,
                            evidence.target_set,
                            &evidence.evaluation,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericNonmembership(evidence)) => {
                        validate_atomic_fact_well_definedness_result(
                            &result.checked,
                            &source_fact,
                        )?;
                        self.construct_lean_closed_numeric_nonmembership_from_result(
                            &source_fact,
                            evidence,
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
                        "typed builtin evidence must be handled before the terminal direct compiler dispatch: {evidence:?}"
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
            // A statement-level `ForallProof` owns a compiler environment and
            // is consumed by `compile_direct_forall_fact_result`, not by this
            // proof-expression constructor.
            SuccessFactProofResult::ForallProof(_) => Ok(None),
        }
    }

    pub(super) fn construct_lean_literal_set_nonempty_from_result(
        &self,
        source_fact: &Fact,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if !subgoals.is_empty() {
            return Err("literal-set nonempty evidence unexpectedly retained subgoals".into());
        }
        let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = source_fact else {
            return Err("literal-set nonempty evidence targets another fact family".into());
        };
        let Obj::ListSet(list_set) = &nonempty.set else {
            return Err("literal-set nonempty evidence targets a nonliteral set".into());
        };
        let Some(first) = list_set.list.first() else {
            return Err("literal-set nonempty evidence targets the empty literal".into());
        };
        let rendered_first = render_obj(first.as_ref(), &self.environment_stack)?;
        Ok(Some(format!(
            "Litex.SetRules.unionNonemptyLeft (Litex.Rules.singletonNonempty {rendered_first})"
        )))
    }

    pub(super) fn construct_lean_set_builder_subset_base_from_result(
        &self,
        source_fact: &Fact,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if !subgoals.is_empty() {
            return Err("set-builder base-subset evidence unexpectedly retained subgoals".into());
        }
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = source_fact else {
            return Err("set-builder base-subset evidence targets another fact family".into());
        };
        let Obj::SetBuilder(builder) = &subset.left else {
            return Err("set-builder base-subset evidence targets another set constructor".into());
        };
        if !objs_equal_with_nested_binder_alpha_equivalence(
            builder.param_set.as_ref(),
            &subset.right,
        ) {
            return Err("set-builder base-subset evidence changed its base carrier".into());
        }
        render_fact(source_fact, &self.environment_stack)?;
        Ok(Some("Litex.Rules.setBuilderSubsetBase".into()))
    }

    pub(super) fn construct_lean_set_builder_in_power_set_via_param_subset_from_result(
        &mut self,
        source_fact: &Fact,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        let (element, target) = membership_parts(source_fact)?;
        let Obj::SetBuilder(builder) = element else {
            return Err(
                "set-builder power-set evidence targets another element constructor".into(),
            );
        };
        let Obj::PowerSet(power_set) = target else {
            return Err("set-builder power-set evidence targets another carrier".into());
        };
        let [child] = subgoals else {
            return Err(
                "set-builder power-set evidence must retain one parameter-subset child".into(),
            );
        };
        let child = child
            .verified()
            .ok_or_else(|| "set-builder power-set child is not factual".to_string())?;
        let child_fact = child.fact();
        let (child_left, child_right) = subset_parts(&child_fact)?;
        if !objs_equal_with_nested_binder_alpha_equivalence(builder.param_set.as_ref(), child_left)
            || !objs_equal_with_nested_binder_alpha_equivalence(power_set.set.as_ref(), child_right)
        {
            return Err("set-builder power-set evidence changed its subset endpoints".into());
        }
        let Some(child_proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
            return Ok(None);
        };
        render_fact(source_fact, &self.environment_stack)?;
        Ok(Some(format!(
            "Litex.Rules.setBuilderInPowerSetViaParamSubset ({child_proof})"
        )))
    }

    /// Compile against this exact Result's WD tree and process-local stores.
    /// Neither the occurrence context nor its temporary FactIds escape into a
    /// sibling or later source statement.
    pub(super) fn construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
        &mut self,
        result: &VerifiedFactResult,
    ) -> Result<Option<String>, String> {
        self.with_verified_fact_well_definedness_context(result, |compiler| {
            compiler.construct_lean_proof_from_direct_fact_result(result)
        })
    }

    pub(super) fn construct_lean_literal_set_subset_from_result(
        &mut self,
        source_fact: &Fact,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = source_fact else {
            return Err("literal-set-subset evidence targets a non-subset fact".into());
        };
        let Obj::ListSet(list) = &subset.left else {
            return Err("literal-set-subset evidence lost its literal left set".into());
        };
        if list.list.len() != subgoals.len() {
            return Err("literal-set-subset evidence changed its member arity".into());
        }
        let target = render_obj(&subset.right, &self.environment_stack)?;
        let mut tail = "Litex.Set.empty".to_string();
        let mut proof = format!("Litex.Rules.emptySubset {target}");
        for (item, subgoal) in list.list.iter().zip(subgoals.iter()).rev() {
            let item = item.as_ref();
            let expected: Fact = self
                .runtime
                .new_in_fact(item.clone(), subset.right.clone(), subset.line_file.clone())
                .into();
            let subgoal = subgoal
                .verified()
                .ok_or_else(|| "literal-set-subset member subgoal is not factual".to_string())?;
            validate_scoped_fact_check_result(
                subgoal,
                &expected,
                "literal-set-subset member subgoal",
            )?;
            let item_proof = self
                .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(subgoal)?
                .ok_or_else(|| {
                    "literal-set-subset member subgoal has no typed proof consumer".to_string()
                })?;
            let rendered_item = render_obj(item, &self.environment_stack)?;
            let singleton = format!("Litex.Set.singleton {rendered_item}");
            let singleton_proof =
                format!("Litex.Rules.singletonSubset {rendered_item} {target} ({item_proof})");
            proof = format!(
                "Litex.Rules.coproductSubset {singleton} {tail} {target} ({singleton_proof}) ({proof})"
            );
            tail = format!("Litex.Set.coproduct {singleton} {tail}");
        }
        Ok(Some(proof))
    }
}
