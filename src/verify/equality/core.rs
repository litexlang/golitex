//! Equality verification and checked normalization routes.

use crate::common::fact_id::FactId;
use crate::error::RuntimeError;
use crate::fact::{AtomicFact, EqualFact, Fact, NotEqualFact};
use crate::infer::SuccessInferResult;
use crate::obj::{
    obj_equality_key, objs_equal_with_nested_binder_alpha_equivalence, AnonymousFn, FnObjHead, Mul,
    Number, Obj,
};
use crate::rational_expression::{
    complex_algebraic_normalization_nonzero_requirements,
    objs_equal_by_complex_rational_expression_evaluation,
    objs_equal_by_rational_expression_evaluation, objs_form_verified_integral_polynomial_identity,
};
use crate::result::{
    BuiltinRuleEvidence, CheckedFunctionDefinitionReductionEvidence,
    ComplexAlgebraicNormalizationBuiltinRuleEvidence, EqualityTransportEvidence,
    EqualityTransportStep, FactTransformationRule,
    IntegralPolynomialNormalizationBuiltinRuleEvidence,
    NestedCheckedFunctionDefinitionReductionEvidence, RationalNormalizationBuiltinRuleEvidence,
    StmtResult, StructuralDefinitionCongruenceBuiltinRuleEvidence,
    StructuralKnownEqualityCongruenceBuiltinRuleEvidence, SuccessFactProofResult,
    SuccessFactStmtResult, SuccessTransformFactResult, UncataloguedBuiltinRule,
    UnknownGenericStmtResult,
};
use crate::runtime::Runtime;
use crate::verify::{BuiltinRuleSearchState, VerifyState};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EqualitySide {
    Left,
    Right,
}

impl EqualitySide {
    const BOTH: [Self; 2] = [Self::Left, Self::Right];

    fn select<'a>(self, equal_fact: &'a EqualFact) -> (&'a Obj, &'a Obj) {
        match self {
            Self::Left => (&equal_fact.left, &equal_fact.right),
            Self::Right => (&equal_fact.right, &equal_fact.left),
        }
    }

    fn is_left(self) -> bool {
        self == Self::Left
    }
}

impl Runtime {
    pub fn verify_equal_fact_with_bounded_builtin_routes(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let zero_premise_result =
            self.verify_equal_fact_with_zero_premise_verification(equal_fact)?;
        if zero_premise_result.is_success() {
            return Ok(zero_premise_result);
        }

        let builtin_state = BuiltinRuleSearchState::initial();
        self.verify_equal_fact_with_one_premise_producing_builtin_rule(equal_fact, &builtin_state)
    }

    pub fn verify_equal_fact_with_known_fact(&mut self, equal_fact: &EqualFact) -> StmtResult {
        let result = self.verify_equal_fact_by_known_equality_without_direct_evaluation(equal_fact);
        self.cache_successful_atomic_fact_for_statement(&equal_fact.clone().into(), result)
    }

    // A premise is a child fact that a rule must verify before concluding its parent fact.
    // Zero-premise equality verification closes the current equality without generating a new
    // proof obligation: it tries known equality, direct evaluation, and terminating congruence.
    // This phase must stay separate because a surrounding builtin rule may already have consumed
    // the one allowed premise-producing step. For example, after using a rule whose child is
    // `(-1 * sqrt(2)) ^ 2 = 2`, that closed child must still be calculable without recursively
    // opening another mathematical rule.
    pub fn verify_equal_fact_with_zero_premise_verification(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_equal_fact_with_known_fact(equal_fact);
        if known_result.is_success() {
            return Ok(known_result);
        }

        let direct_evaluation_result = self.verify_equal_fact_by_direct_evaluation(equal_fact);
        if direct_evaluation_result.is_success() {
            return Ok(self.cache_successful_atomic_fact_for_statement(
                &equal_fact.clone().into(),
                direct_evaluation_result,
            ));
        }

        let known_equality_evaluation_result =
            self.verify_equal_fact_by_known_equality_then_direct_evaluation(equal_fact);
        if known_equality_evaluation_result.is_success() {
            return Ok(self.cache_successful_atomic_fact_for_statement(
                &equal_fact.clone().into(),
                known_equality_evaluation_result,
            ));
        }

        // A generated builtin premise can compare the very same checked
        // application that occurred in its parent goal (for example,
        // `f(y) $in {0}` generates `f(y) = 0`).  Preserve the checked
        // definition reduction as a real proof node here instead of letting
        // the terminating boolean comparator erase that evidence.
        let after_parent_well_definedness = VerifyState::after_well_definedness();
        for definition_side in EqualitySide::BOTH {
            let (application, _) = definition_side.select(equal_fact);
            if self
                .checked_function_definition_reduction_source(application)?
                .is_none()
            {
                continue;
            }
            if let Some(result) = self.try_reduce_one_checked_definition_side(
                equal_fact,
                definition_side,
                &after_parent_well_definedness,
            )? {
                return Ok(self.cache_successful_atomic_fact_for_statement(
                    &equal_fact.clone().into(),
                    result,
                ));
            }
        }

        // Named applications must reach the checked-definition route below,
        // which freezes the defining FactId and exact reduction.  Letting the
        // boolean structural shortcut consume them would retain only a label
        // and make the successful Result unusable after Runtime is dropped.
        if self
            .checked_function_definition_reduction_source(&equal_fact.left)?
            .is_some()
            || self
                .checked_function_definition_reduction_source(&equal_fact.right)?
                .is_some()
        {
            return Ok(direct_evaluation_result);
        }

        // Prefer an exact earlier equality Result at a changed leaf over a
        // second definition unfolding. This keeps proof-step provenance (for
        // example a preceding `odd(n+1) = ...` line) visible to the compiler.
        let mut congruence_subgoals = Vec::new();
        if self.collect_known_addition_congruence_results(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact.line_file.clone(),
            &mut congruence_subgoals,
        ) && !congruence_subgoals.is_empty()
        {
            let target: Fact = equal_fact.clone().into();
            let result =
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target.clone(),
                    "known equalities under reviewed addition congruence".to_string(),
                    BuiltinRuleEvidence::StructuralKnownEqualityCongruence(
                        StructuralKnownEqualityCongruenceBuiltinRuleEvidence {
                            expected_target: target,
                        },
                    ),
                    congruence_subgoals,
                )
                .into();
            return Ok(
                self.cache_successful_atomic_fact_for_statement(&equal_fact.clone().into(), result)
            );
        }

        let mut nested_reductions = Vec::new();
        if self.collect_checked_definition_structural_reductions(
            &equal_fact.left,
            &equal_fact.right,
            &mut nested_reductions,
        )? && !nested_reductions.is_empty()
        {
            let target: Fact = equal_fact.clone().into();
            let result =
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target.clone(),
                    "checked definition reductions under structural congruence".to_string(),
                    BuiltinRuleEvidence::StructuralDefinitionCongruence(
                        StructuralDefinitionCongruenceBuiltinRuleEvidence {
                            expected_target: target,
                            reductions: nested_reductions,
                        },
                    ),
                    Vec::new(),
                )
                .into();
            return Ok(
                self.cache_successful_atomic_fact_for_statement(&equal_fact.clone().into(), result)
            );
        }

        if !self.equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(equal_fact)? {
            return Ok(direct_evaluation_result);
        }

        let result: StmtResult =
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "structural equality with terminating reductions".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyEqualFactWithZeroPremiseVerification,
                ),
                Vec::new(),
            )
            .into();
        Ok(self.cache_successful_atomic_fact_for_statement(&equal_fact.clone().into(), result))
    }

    // Direct evaluation is the computation arm of zero-premise verification. It may normalize
    // the two objects, but it cannot generate premises or apply another mathematical rule.
    pub fn verify_equal_fact_by_direct_evaluation(&self, equal_fact: &EqualFact) -> StmtResult {
        if let (Some(left_evaluation), Some(right_evaluation)) = (
            equal_fact
                .left
                .evaluate_to_normalized_decimal_number_with_result(),
            equal_fact
                .right
                .evaluate_to_normalized_decimal_number_with_result(),
        ) {
            if left_evaluation.value.normalized_value == right_evaluation.value.normalized_value {
                let target: Fact = equal_fact.clone().into();
                return SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target.clone(),
                    "calculation".to_string(),
                    BuiltinRuleEvidence::RationalNormalization(
                        RationalNormalizationBuiltinRuleEvidence::new(
                            target,
                            left_evaluation,
                            right_evaluation,
                        ),
                    ),
                    Vec::new(),
                )
                .into();
            }
        }
        let complex_normalization_succeeds = objs_equal_by_complex_rational_expression_evaluation(
            &equal_fact.left,
            &equal_fact.right,
        );
        if complex_normalization_succeeds {
            let nonzero_requirements = complex_algebraic_normalization_nonzero_requirements(
                &equal_fact.left,
                &equal_fact.right,
            );
            if !nonzero_requirements.is_empty() {
                // This identity is computationally valid only under retained
                // nonzero premises. Leave it to the bounded premise-producing
                // phase below instead of erasing those dependencies through
                // the ordinary rational-normalization fallback.
                return UnknownGenericStmtResult::new().into();
            }
            let target: Fact = equal_fact.clone().into();
            return SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                target.clone(),
                "exact complex algebraic normalization".to_string(),
                BuiltinRuleEvidence::ComplexAlgebraicNormalization(
                    ComplexAlgebraicNormalizationBuiltinRuleEvidence::new(target, Vec::new()),
                ),
                Vec::new(),
            )
            .into();
        }
        if objs_form_verified_integral_polynomial_identity(&equal_fact.left, &equal_fact.right) {
            let target: Fact = equal_fact.clone().into();
            return SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                target.clone(),
                "exact integral polynomial normalization".to_string(),
                BuiltinRuleEvidence::IntegralPolynomialNormalization(
                    IntegralPolynomialNormalizationBuiltinRuleEvidence {
                        expected_target: target,
                    },
                ),
                Vec::new(),
            )
            .into();
        }
        // Resolving an equality-class representative can expose these abs
        // identities, but their validity depends on a retained order premise.
        // Let the bounded premise-producing phase emit the registered rule
        // Result instead of reporting a premise-free diagnostic calculation.
        if equal_fact_has_abs_sign_selection_shape(equal_fact) {
            return UnknownGenericStmtResult::new().into();
        }
        let left_resolved = self.resolve_obj(&equal_fact.left);
        let right_resolved = self.resolve_obj(&equal_fact.right);
        let reason = if equal_fact
            .left
            .two_objs_can_be_calculated_and_equal_by_calculation(&equal_fact.right)
            || left_resolved.two_objs_can_be_calculated_and_equal_by_calculation(&right_resolved)
        {
            "calculation"
        } else if objs_equal_by_rational_expression_evaluation(&equal_fact.left, &equal_fact.right)
            || objs_equal_by_rational_expression_evaluation(&left_resolved, &right_resolved)
        {
            "calculation and rational expression simplification"
        } else if equal_fact_sides_match_by_bounded_symbolic_normalization(equal_fact)
            || equal_fact_sides_match_by_bounded_symbolic_normalization(&EqualFact::new(
                left_resolved,
                right_resolved,
                equal_fact.line_file.clone(),
            ))
        {
            // Bounded, obligation-free symbolic normalization. Example:
            // `a * t + 0 = a * t` and `abs(x - y) = abs(y - x)`.
            "bounded symbolic normalization"
        } else {
            return UnknownGenericStmtResult::new().into();
        };
        SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            equal_fact.clone().into(),
            reason.to_string(),
            BuiltinRuleEvidence::Uncatalogued(
                UncataloguedBuiltinRule::VerifyEqualFactByDirectEvaluation,
            ),
            Vec::new(),
        )
        .into()
    }

    fn collect_checked_definition_structural_reductions(
        &mut self,
        left: &Obj,
        right: &Obj,
        reductions: &mut Vec<NestedCheckedFunctionDefinitionReductionEvidence>,
    ) -> Result<bool, RuntimeError> {
        if objs_equal_with_nested_binder_alpha_equivalence(left, right) {
            return Ok(true);
        }

        let checkpoint = reductions.len();
        if let Some((definition_object, defining_equality, defining_equality_fact_id)) =
            self.checked_function_definition_reduction_source(left)?
        {
            if let Some(reduced) = self.reduce_direct_known_fn_application_once(
                left,
                &VerifyState::after_well_definedness(),
            )? {
                reductions.push(NestedCheckedFunctionDefinitionReductionEvidence {
                    definition_object,
                    defining_equality,
                    defining_equality_fact_id,
                    application: left.clone(),
                    reduced: reduced.clone(),
                });
                if self
                    .collect_checked_definition_structural_reductions(&reduced, right, reductions)?
                {
                    return Ok(true);
                }
                reductions.truncate(checkpoint);
            }
        }

        if let Some((definition_object, defining_equality, defining_equality_fact_id)) =
            self.checked_function_definition_reduction_source(right)?
        {
            if let Some(reduced) = self.reduce_direct_known_fn_application_once(
                right,
                &VerifyState::after_well_definedness(),
            )? {
                reductions.push(NestedCheckedFunctionDefinitionReductionEvidence {
                    definition_object,
                    defining_equality,
                    defining_equality_fact_id,
                    application: right.clone(),
                    reduced: reduced.clone(),
                });
                if self
                    .collect_checked_definition_structural_reductions(left, &reduced, reductions)?
                {
                    return Ok(true);
                }
                reductions.truncate(checkpoint);
            }
        }

        let structurally_equal: Result<bool, RuntimeError> =
            Self::same_shape_and_corresponding_args_match(left, right, &mut |left, right| {
                self.collect_checked_definition_structural_reductions(left, right, reductions)
            });
        match structurally_equal {
            Ok(true) => Ok(true),
            Ok(false) => {
                reductions.truncate(checkpoint);
                Ok(false)
            }
            Err(error) => {
                reductions.truncate(checkpoint);
                Err(error)
            }
        }
    }

    // Reusing an already stored equality and then normalizing its representative still creates
    // no new premise. Example: from `a^2 + a*a + b = 0`, normalize the known left representative
    // to close `0 = 2*a^2 + b`. Keep this after direct evaluation of the submitted equality so a
    // self-contained calculation does not acquire unrelated known-equality provenance.
    pub fn verify_equal_fact_by_known_equality_then_direct_evaluation(
        &mut self,
        equal_fact: &EqualFact,
    ) -> StmtResult {
        let left_representatives =
            self.get_all_obj_representatives_equal_to_given(&equal_fact.left);
        let left_match = left_representatives.into_iter().find(|representative| {
            objs_equal_by_rational_expression_evaluation(representative, &equal_fact.right)
        });
        let known_fact = if let Some(representative) = left_match {
            EqualFact::new(
                equal_fact.left.clone(),
                representative,
                equal_fact.line_file.clone(),
            )
        } else {
            let Some(representative) = self
                .get_all_obj_representatives_equal_to_given(&equal_fact.right)
                .into_iter()
                .find(|representative| {
                    objs_equal_by_rational_expression_evaluation(&equal_fact.left, representative)
                })
            else {
                return UnknownGenericStmtResult::new().into();
            };
            EqualFact::new(
                equal_fact.right.clone(),
                representative,
                equal_fact.line_file.clone(),
            )
        };
        let known_result = self.verify_equal_fact_with_known_fact(&known_fact);
        if !known_result.is_success() {
            return UnknownGenericStmtResult::new().into();
        }
        // Resolution may rediscover the submitted equality itself (for
        // example `0 <= x` stores the exact inferred fact `abs(x) = x`). In
        // that case the stored citation is already the complete proof. Do not
        // wrap it in a diagnostic-only "normalization" node and erase its
        // FactId provenance.
        if known_fact.to_string() == equal_fact.to_string() {
            return known_result;
        }
        SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            equal_fact.clone().into(),
            "calculation and rational expression simplification".to_string(),
            BuiltinRuleEvidence::Uncatalogued(
                UncataloguedBuiltinRule::VerifyEqualFactByKnownEqualityThenDirectEvaluation,
            ),
            vec![known_result],
        )
        .into()
    }

    // This bounded phase may generate premises, so entering it consumes the available
    // builtin-rule step before any child equality is checked.
    pub fn verify_equal_fact_with_one_premise_producing_builtin_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        if !builtin_state.can_apply_rule() {
            return Ok(UnknownGenericStmtResult::new().into());
        }
        let child_state = builtin_state.after_applying_rule();
        let goal: AtomicFact = equal_fact.clone().into();
        if let Some(result) = self
            .try_verify_equal_fact_by_complex_algebraic_normalization_with_nonzero_premises(
                equal_fact,
                &child_state,
            )?
        {
            return Ok(self.cache_successful_atomic_fact_for_statement(&goal, result));
        }
        if let Some(result) =
            self.try_verify_atomic_fact_from_known_set_builder_membership(&goal)?
        {
            return Ok(self.cache_successful_atomic_fact_for_statement(&goal, result));
        }
        let result = self.verify_equal_fact_by_builtin_rules(equal_fact, &child_state)?;
        Ok(self.cache_successful_atomic_fact_for_statement(&goal, result))
    }

    fn try_verify_equal_fact_by_complex_algebraic_normalization_with_nonzero_premises(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !objs_equal_by_complex_rational_expression_evaluation(
            &equal_fact.left,
            &equal_fact.right,
        ) {
            return Ok(None);
        }
        let required_objects = complex_algebraic_normalization_nonzero_requirements(
            &equal_fact.left,
            &equal_fact.right,
        );
        if required_objects.is_empty() {
            return Ok(None);
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let required_facts = required_objects
            .into_iter()
            .map(|object| {
                AtomicFact::NotEqualFact(NotEqualFact::new(
                    object,
                    zero.clone(),
                    equal_fact.line_file.clone(),
                ))
            })
            .collect::<Vec<_>>();
        let mut subgoals = Vec::with_capacity(required_facts.len());
        for premise in &required_facts {
            let result = self.verify_atomic_fact_as_builtin_rule_premise(premise, builtin_state)?;
            if !result.is_success() {
                return Ok(None);
            }
            subgoals.push(result);
        }

        let target: Fact = equal_fact.clone().into();
        let expected_nonzero_premises = required_facts
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        Ok(Some(
            SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                target.clone(),
                "exact complex algebraic normalization with nonzero premises".to_string(),
                BuiltinRuleEvidence::ComplexAlgebraicNormalization(
                    ComplexAlgebraicNormalizationBuiltinRuleEvidence::new(
                        target,
                        expected_nonzero_premises,
                    ),
                ),
                subgoals,
            )
            .into(),
        ))
    }

    pub fn verify_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let builtin_goal: AtomicFact = equal_fact.clone().into();
        let mut result = self.verify_equal_fact_with_bounded_builtin_routes(equal_fact)?;
        if result.is_success() {
            return Ok(result);
        }

        result = self.verify_atomic_fact_with_builtin_strategy(&builtin_goal)?;
        if result.is_success() {
            return Ok(result);
        }

        result =
            self.verify_equality_after_one_checked_definition_reduction(equal_fact, verify_state)?;
        if result.is_success() {
            return Ok(result);
        }

        if verify_state.is_initial_round() {
            let verified_by_arg_to_arg = self
                .verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(
                    equal_fact,
                    verify_state,
                )?;
            if verified_by_arg_to_arg {
                return Ok(
                    (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        equal_fact.clone().into(),
                        same_shape_and_equal_args_reason(equal_fact),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyEqualFact),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if verify_state.is_initial_round() {
            let next_round_state = verify_state.with_next_round();
            result = self.verify_equal_fact_with_known_forall(equal_fact, &next_round_state)?;
            if result.is_success() {
                return Ok(result);
            }

            if let Some(result) = self
                .try_verify_equal_fact_by_transforming_known_equal_representatives(
                    equal_fact,
                    &next_round_state,
                )?
            {
                return Ok(result);
            }
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    /// Composition mode: `Wrap`.
    ///
    /// A target may use checked surface definitions while a known theorem is
    /// stated with their expanded values. Verify the expanded equality first,
    /// then retain the exact stored equality edges that rewrite that child
    /// result back to the submitted target. This is deliberately a recursive
    /// result node; no proposition-string rediscovery is needed by consumers.
    fn try_verify_equal_fact_by_transforming_known_equal_representatives(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let mut left_candidates = vec![equal_fact.left.clone()];
        left_candidates.extend(self.get_all_obj_representatives_equal_to_given(&equal_fact.left));
        let mut right_candidates = vec![equal_fact.right.clone()];
        right_candidates.extend(self.get_all_obj_representatives_equal_to_given(&equal_fact.right));

        let target_left_key = obj_equality_key(&equal_fact.left);
        let target_right_key = obj_equality_key(&equal_fact.right);
        for left in left_candidates {
            for right in right_candidates.iter() {
                if obj_equality_key(&left) == target_left_key
                    && obj_equality_key(right) == target_right_key
                {
                    continue;
                }

                let source_fact =
                    EqualFact::new(left.clone(), right.clone(), equal_fact.line_file.clone());
                let source_result =
                    self.verify_equal_fact_with_known_forall(&source_fact, verify_state)?;
                let Some(source_success) = source_result.into_factual_success() else {
                    continue;
                };

                let mut rewrite_steps = Vec::new();
                if obj_equality_key(&left) != target_left_key {
                    let Some(path) = self.compiler_known_equality_path(&EqualFact::new(
                        left.clone(),
                        equal_fact.left.clone(),
                        equal_fact.line_file.clone(),
                    )) else {
                        continue;
                    };
                    rewrite_steps.extend(path.into_iter().map(|step| {
                        EqualityTransportStep::new(
                            step.from,
                            step.to,
                            step.equality,
                            step.source_fact_id,
                        )
                    }));
                }
                if obj_equality_key(right) != target_right_key {
                    let Some(path) = self.compiler_known_equality_path(&EqualFact::new(
                        right.clone(),
                        equal_fact.right.clone(),
                        equal_fact.line_file.clone(),
                    )) else {
                        continue;
                    };
                    rewrite_steps.extend(path.into_iter().map(|step| {
                        EqualityTransportStep::new(
                            step.from,
                            step.to,
                            step.equality,
                            step.source_fact_id,
                        )
                    }));
                }
                if rewrite_steps.is_empty() {
                    continue;
                }

                let proof = SuccessFactProofResult::Transform(Box::new(
                    SuccessTransformFactResult::from_shared(
                        FactTransformationRule::EqualityRewrite(EqualityTransportEvidence::new(
                            rewrite_steps,
                        )),
                        source_success.verification,
                    ),
                ));
                return Ok(Some(
                    SuccessFactStmtResult::new(
                        equal_fact.clone().into(),
                        SuccessInferResult::new(),
                        proof,
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    fn verify_equality_after_one_checked_definition_reduction(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // The goal's well-definedness check already discharged the selected
        // function application's carrier and domain obligations. Definition
        // reduction therefore performs substitution only and never opens a
        // second proof-search root.
        if !verify_state.is_initial_round() || !verify_state.well_definedness_verified {
            return Ok((UnknownGenericStmtResult::new()).into());
        }

        if let Some(result) = self.try_reduce_one_checked_definition_side(
            equal_fact,
            EqualitySide::Left,
            verify_state,
        )? {
            return Ok(result);
        }
        if let Some(result) = self.try_reduce_one_checked_definition_side(
            equal_fact,
            EqualitySide::Right,
            verify_state,
        )? {
            return Ok(result);
        }
        Ok((UnknownGenericStmtResult::new()).into())
    }

    fn try_reduce_one_checked_definition_side(
        &mut self,
        equal_fact: &EqualFact,
        definition_side: EqualitySide,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (application_side, other_side) = definition_side.select(equal_fact);
        let line_file = equal_fact.line_file.clone();
        // Reduce exactly one checked definition already present in the goal.
        // Comparison remains limited to known facts, terminating computation,
        // and constructor descent.
        let reduced = match self
            .reduce_direct_known_fn_application_once(application_side, verify_state)?
        {
            Some(reduced) => reduced,
            None => {
                let Some(set_builder) = self.get_obj_equal_to_set_builder(application_side) else {
                    return Ok(None);
                };
                set_builder.into()
            }
        };
        let mut comparison_candidates = vec![reduced.clone()];
        if let Some(beta_reduced) =
            self.beta_reduce_complete_anonymous_application_once(&reduced)?
        {
            if !objs_equal_with_nested_binder_alpha_equivalence(&reduced, &beta_reduced) {
                comparison_candidates.push(beta_reduced);
            }
        }

        for comparison_candidate in comparison_candidates {
            let alpha_equal =
                objs_equal_with_nested_binder_alpha_equivalence(&comparison_candidate, other_side);
            let compared_equal = alpha_equal
                || self.equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
                    &EqualFact::new_from_refs(&comparison_candidate, other_side, line_file.clone()),
                )?;
            if !compared_equal {
                continue;
            }

            let reason = format!(
                "one checked definition reduction `{}` = `{}`",
                application_side, comparison_candidate
            );
            let checked_definition_source =
                self.checked_function_definition_reduction_source(application_side)?;
            return Ok(Some(Self::checked_definition_reduction_success(
                equal_fact,
                application_side,
                &comparison_candidate,
                other_side,
                definition_side,
                alpha_equal,
                checked_definition_source,
                &reason,
            )));
        }
        Ok(None)
    }

    fn checked_definition_reduction_success(
        equal_fact: &EqualFact,
        application_side: &Obj,
        reduced_side: &Obj,
        other_side: &Obj,
        definition_side: EqualitySide,
        reduced_matches_other_by_alpha: bool,
        checked_definition_source: Option<(Obj, Fact, FactId)>,
        reason: &str,
    ) -> StmtResult {
        let fact: Fact = equal_fact.clone().into();
        let msg = format!(
            "{}; reduced goal side `{}` is compared with `{}` using stored equalities, terminating computation, anonymous-function beta reduction, or constructor descent",
            reason, application_side, reduced_side
        );
        let verified_by = match checked_definition_source {
            Some((definition_object, defining_equality, defining_equality_fact_id)) => {
                SuccessFactProofResult::fact_with_checked_function_definition_reduction(
                    fact.clone(),
                    CheckedFunctionDefinitionReductionEvidence {
                        definition_object,
                        defining_equality,
                        defining_equality_fact_id,
                        application_side: application_side.clone(),
                        reduced: reduced_side.clone(),
                        other_side: other_side.clone(),
                        application_is_left: definition_side.is_left(),
                        reduced_matches_other_by_alpha,
                    },
                    Some(msg),
                )
            }
            None => SuccessFactProofResult::diagnostic(msg),
        };
        SuccessFactStmtResult::new_with_verified_by_known_fact(fact, verified_by, Vec::new()).into()
    }

    fn checked_function_definition_reduction_source(
        &self,
        application: &Obj,
    ) -> Result<Option<(Obj, Fact, FactId)>, RuntimeError> {
        let Obj::FnObj(function_application) = application else {
            return Ok(None);
        };
        if function_application.body.is_empty() {
            return Ok(None);
        }
        let definition_object: Obj = match function_application.head.as_ref() {
            FnObjHead::Identifier(_) | FnObjHead::IdentifierWithMod(_) => {
                (*function_application.head).clone().into()
            }
            _ => return Ok(None),
        };
        let Some((body, equal_to, line_file)) =
            self.get_known_fn_body_and_equal_to_for_obj(&definition_object)
        else {
            return Ok(None);
        };
        let anonymous_function = AnonymousFn {
            body,
            equal_to: Box::new(equal_to),
            source_occurrence_id: None,
        };
        let defining_equality: Fact = EqualFact::new(
            definition_object.clone(),
            anonymous_function.into(),
            line_file,
        )
        .into();
        let Some(defining_equality_fact_id) = self.known_fact_id_for_fact(&defining_equality)?
        else {
            return Ok(None);
        };
        Ok(Some((
            definition_object,
            defining_equality,
            defining_equality_fact_id,
        )))
    }

    fn verify_two_equal_fact_premises_for_corresponding_binary_args(
        &mut self,
        left_args_equal_fact: &EqualFact,
        right_args_equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let result = self.verify_equal_fact_by_builtin_rules_and_known_equalities(
            left_args_equal_fact,
            verify_state,
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        let result = self.verify_equal_fact_by_builtin_rules_and_known_equalities(
            right_args_equal_fact,
            verify_state,
        )?;
        if result.is_unknown() {
            return Ok(false);
        }
        Ok(true)
    }

    fn verify_equal_fact_for_corresponding_unary_args(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let result =
            self.verify_equal_fact_by_builtin_rules_and_known_equalities(equal_fact, verify_state)?;
        if result.is_success() {
            return Ok(true);
        }
        Ok(false)
    }

    fn verify_equal_fact_for_iterated_operator_functions(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        // Iterated operators such as sum/product compare their summand
        // functions extensionally. Example:
        // `sum(1, n, fn(x Z) Z {f(x)}) = sum(1, n, fn(y Z) Z {f(y)})`.
        self.verify_equal_fact_for_corresponding_unary_args(equal_fact, verify_state)
    }

    pub fn verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let left_obj = &equal_fact.left;
        let right_obj = &equal_fact.right;
        let equality_line_file = equal_fact.line_file.clone();
        match (left_obj, right_obj) {
            (Obj::Sum(left), Obj::Sum(right)) => {
                if !self.verify_two_equal_fact_premises_for_corresponding_binary_args(
                    &EqualFact::new_from_refs(
                        &left.start,
                        &right.start,
                        equality_line_file.clone(),
                    ),
                    &EqualFact::new_from_refs(&left.end, &right.end, equality_line_file.clone()),
                    verify_state,
                )? {
                    return Ok(false);
                }
                self.verify_equal_fact_for_iterated_operator_functions(
                    &EqualFact::new_from_refs(
                        left.func.as_ref(),
                        right.func.as_ref(),
                        equality_line_file,
                    ),
                    verify_state,
                )
            }
            (Obj::SumOfFiniteSet(left), Obj::SumOfFiniteSet(right)) => {
                if !self
                    .verify_equal_fact_by_builtin_rules_and_known_equalities(
                        &EqualFact::new_from_refs(
                            left.set.as_ref(),
                            right.set.as_ref(),
                            equality_line_file.clone(),
                        ),
                        verify_state,
                    )?
                    .is_success()
                {
                    return Ok(false);
                }
                self.verify_equal_fact_for_iterated_operator_functions(
                    &EqualFact::new_from_refs(
                        left.func.as_ref(),
                        right.func.as_ref(),
                        equality_line_file,
                    ),
                    verify_state,
                )
            }
            (Obj::ProductOfFiniteSet(left), Obj::ProductOfFiniteSet(right)) => {
                if !self
                    .verify_equal_fact_by_builtin_rules_and_known_equalities(
                        &EqualFact::new_from_refs(
                            left.set.as_ref(),
                            right.set.as_ref(),
                            equality_line_file.clone(),
                        ),
                        verify_state,
                    )?
                    .is_success()
                {
                    return Ok(false);
                }
                self.verify_equal_fact_for_iterated_operator_functions(
                    &EqualFact::new_from_refs(
                        left.func.as_ref(),
                        right.func.as_ref(),
                        equality_line_file,
                    ),
                    verify_state,
                )
            }
            (Obj::Product(left), Obj::Product(right)) => {
                if !self.verify_two_equal_fact_premises_for_corresponding_binary_args(
                    &EqualFact::new_from_refs(
                        &left.start,
                        &right.start,
                        equality_line_file.clone(),
                    ),
                    &EqualFact::new_from_refs(&left.end, &right.end, equality_line_file.clone()),
                    verify_state,
                )? {
                    return Ok(false);
                }
                self.verify_equal_fact_for_iterated_operator_functions(
                    &EqualFact::new_from_refs(
                        left.func.as_ref(),
                        right.func.as_ref(),
                        equality_line_file,
                    ),
                    verify_state,
                )
            }
            _ => Self::same_shape_and_corresponding_args_match(
                left_obj,
                right_obj,
                &mut |left_arg, right_arg| {
                    self.verify_equal_fact_by_builtin_rules_and_known_equalities(
                        &EqualFact::new_from_refs(left_arg, right_arg, equality_line_file.clone()),
                        verify_state,
                    )
                    .map(|result| result.is_success())
                },
            ),
        }
    }

    fn verify_equal_fact_by_builtin_rules_and_known_equalities(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let result = self.verify_equal_fact_with_bounded_builtin_routes(equal_fact)?;
        if result.is_success() {
            return Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "builtin rules".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyEqualFactByBuiltinRulesAndKnownEqualities01,
                    ),
                    Vec::new(),
                ))
                .into(),
            );
        }

        let verified_by_arg_to_arg = self
            .verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(
                equal_fact,
                verify_state,
            )?;
        if verified_by_arg_to_arg {
            return Ok(
                (SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    same_shape_and_equal_args_reason(equal_fact),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyEqualFactByBuiltinRulesAndKnownEqualities02,
                    ),
                    Vec::new(),
                ))
                .into(),
            );
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }
}

fn equal_fact_has_abs_sign_selection_shape(equal_fact: &EqualFact) -> bool {
    fn is_negation_of(candidate: &Obj, argument: &Obj) -> bool {
        let Obj::Mul(product) = candidate else {
            return false;
        };
        let is_negative_one =
            |object: &Obj| matches!(object, Obj::Number(number) if number.normalized_value == "-1");
        (is_negative_one(product.left.as_ref())
            && objs_equal_with_nested_binder_alpha_equivalence(product.right.as_ref(), argument))
            || (is_negative_one(product.right.as_ref())
                && objs_equal_with_nested_binder_alpha_equivalence(product.left.as_ref(), argument))
    }

    let matches = |absolute_value: &Obj, selected_value: &Obj| {
        let Obj::Abs(absolute_value) = absolute_value else {
            return false;
        };
        objs_equal_with_nested_binder_alpha_equivalence(absolute_value.arg.as_ref(), selected_value)
            || is_negation_of(selected_value, absolute_value.arg.as_ref())
    };
    matches(&equal_fact.left, &equal_fact.right) || matches(&equal_fact.right, &equal_fact.left)
}

fn equal_fact_sides_match_by_bounded_symbolic_normalization(equal_fact: &EqualFact) -> bool {
    // Absolute value is invariant under sign change. This remains a bounded
    // computation leaf: it creates no proof obligations and applies no rules.
    // Example: `abs(x - y) = abs(y - x)`.
    let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (&equal_fact.left, &equal_fact.right) else {
        return false;
    };
    let negative_one: Obj = Number::new("-1".to_string()).into();
    let negated_right: Obj = Mul::new(negative_one, right_abs.arg.as_ref().clone()).into();
    objs_equal_by_rational_expression_evaluation(left_abs.arg.as_ref(), &negated_right)
}

fn same_shape_and_equal_args_reason(equal_fact: &EqualFact) -> String {
    match (&equal_fact.left, &equal_fact.right) {
        (Obj::FnObj(_), Obj::FnObj(_)) => {
            "the function parts are equal, and the function arguments are equal one by one"
                .to_string()
        }
        _ => "the corresponding builtin-object arguments are equal one by one".to_string(),
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verify/equality/core.rs"]
mod tests;
