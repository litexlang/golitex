use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_equal_fact_with_direct_routes(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let zero_premise_result =
            self.verify_equal_fact_with_zero_premise_verification(equal_fact)?;
        if zero_premise_result.is_true() {
            return Ok(zero_premise_result);
        }

        let builtin_state = UseBuiltinRuleVerifyState::new();
        self.verify_equal_fact_with_one_premise_producing_builtin_rule(equal_fact, &builtin_state)
    }

    pub(crate) fn verify_equal_fact_with_known_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> StmtResult {
        let result = self.verify_equal_fact_by_known_equality_without_direct_evaluation(equal_fact);
        self.remember_successful_atomic_fact_for_statement(&equal_fact.clone().into(), result)
    }

    // A premise is a child fact that a rule must verify before concluding its parent fact.
    // Zero-premise equality verification closes the current equality without generating a new
    // proof obligation: it tries known equality, direct evaluation, and terminating congruence.
    // This phase must stay separate because a surrounding builtin rule may already have consumed
    // the one allowed premise-producing step. For example, after using a rule whose child is
    // `(-1 * sqrt(2)) ^ 2 = 2`, that closed child must still be calculable without recursively
    // opening another mathematical rule.
    pub(crate) fn verify_equal_fact_with_zero_premise_verification(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_equal_fact_with_known_fact(equal_fact);
        if known_result.is_true() {
            return Ok(known_result);
        }

        let direct_evaluation_result = self.verify_equal_fact_by_direct_evaluation(equal_fact);
        if direct_evaluation_result.is_true() {
            return Ok(self.remember_successful_atomic_fact_for_statement(
                &equal_fact.clone().into(),
                direct_evaluation_result,
            ));
        }

        let known_equality_evaluation_result =
            self.verify_equal_fact_by_known_equality_then_direct_evaluation(equal_fact);
        if known_equality_evaluation_result.is_true() {
            return Ok(self.remember_successful_atomic_fact_for_statement(
                &equal_fact.clone().into(),
                known_equality_evaluation_result,
            ));
        }

        if !self.equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(equal_fact)? {
            return Ok(direct_evaluation_result);
        }

        let result: StmtResult =
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                equal_fact.clone().into(),
                "structural equality with terminating reductions".to_string(),
                Vec::new(),
            )
            .into();
        Ok(self.remember_successful_atomic_fact_for_statement(&equal_fact.clone().into(), result))
    }

    // Direct evaluation is the computation arm of zero-premise verification. It may normalize
    // the two objects, but it cannot generate premises or apply another mathematical rule.
    pub(crate) fn verify_equal_fact_by_direct_evaluation(
        &self,
        equal_fact: &EqualFact,
    ) -> StmtResult {
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
            return StmtUnknown::new().into();
        };
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            equal_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        )
        .into()
    }

    // Reusing an already stored equality and then normalizing its representative still creates
    // no new premise. Example: from `a^2 + a*a + b = 0`, normalize the known left representative
    // to close `0 = 2*a^2 + b`. Keep this after direct evaluation of the submitted equality so a
    // self-contained calculation does not acquire unrelated known-equality provenance.
    pub(crate) fn verify_equal_fact_by_known_equality_then_direct_evaluation(
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
                return StmtUnknown::new().into();
            };
            EqualFact::new(
                equal_fact.right.clone(),
                representative,
                equal_fact.line_file.clone(),
            )
        };
        let known_result = self.verify_equal_fact_with_known_fact(&known_fact);
        if !known_result.is_true() {
            return StmtUnknown::new().into();
        }
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            equal_fact.clone().into(),
            "calculation and rational expression simplification".to_string(),
            vec![known_result],
        )
        .into()
    }

    // This bounded phase may generate premises, so entering it consumes the available
    // builtin-rule step before any child equality is checked.
    pub(crate) fn verify_equal_fact_with_one_premise_producing_builtin_rule(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if !builtin_state.can_apply_builtin_rule() {
            return Ok(StmtUnknown::new().into());
        }
        let child_state = builtin_state.after_applying_builtin_rule();
        let goal: AtomicFact = equal_fact.clone().into();
        if let Some(result) =
            self.try_verify_atomic_fact_with_local_builtin_catalog(&goal, &child_state)?
        {
            return Ok(self.remember_successful_atomic_fact_for_statement(&goal, result));
        }
        if let Some(result) =
            self.try_verify_atomic_fact_from_known_set_builder_membership(&goal)?
        {
            return Ok(self.remember_successful_atomic_fact_for_statement(&goal, result));
        }
        let result = self.verify_equal_fact_by_builtin_rules(equal_fact, &child_state)?;
        Ok(self.remember_successful_atomic_fact_for_statement(&goal, result))
    }

    pub fn verify_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let builtin_goal: AtomicFact = equal_fact.clone().into();
        let mut result = self.verify_equal_fact_with_direct_routes(equal_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_atomic_fact_with_builtin_strategy(&builtin_goal)?;
        if result.is_true() {
            return Ok(result);
        }

        result =
            self.verify_equality_after_one_checked_definition_reduction(equal_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verified_by_arg_to_arg = self
                .verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(
                    equal_fact,
                    verify_state,
                )?;
            if verified_by_arg_to_arg {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        equal_fact.clone().into(),
                        same_shape_and_equal_args_reason(equal_fact),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if verify_state.is_round_0() && verify_state.equality_can_use_known_forall {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();
            result =
                self.verify_equal_fact_with_known_forall(equal_fact, &verify_state_add_one_round)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_equality_after_one_checked_definition_reduction(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // The goal's well-definedness check already discharged the selected
        // function application's carrier and domain obligations. Definition
        // reduction therefore performs substitution only and never opens a
        // second proof-search root.
        if !verify_state.is_round_0() || !verify_state.well_defined_already_verified {
            return Ok((StmtUnknown::new()).into());
        }

        if let Some(result) =
            self.try_reduce_one_checked_definition_side(equal_fact, true, verify_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_reduce_one_checked_definition_side(equal_fact, false, verify_state)?
        {
            return Ok(result);
        }
        Ok((StmtUnknown::new()).into())
    }

    fn try_reduce_one_checked_definition_side(
        &mut self,
        equal_fact: &EqualFact,
        application_is_left: bool,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (application_side, other_side) = if application_is_left {
            (&equal_fact.left, &equal_fact.right)
        } else {
            (&equal_fact.right, &equal_fact.left)
        };
        let line_file = equal_fact.line_file.clone();
        // Reduce exactly one checked definition already present in the goal.
        // Comparison remains limited to known facts, terminating computation,
        // and constructor descent.
        let checked_function_source = if self.captures_well_definedness() {
            self.checked_function_definition_reduction_source(application_side)?
        } else {
            None
        };
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
            if let Some((definition_object, defining_equality, defining_equality_fact_id)) =
                checked_function_source.clone()
            {
                let fact: Fact = equal_fact.clone().into();
                let evidence = CheckedFunctionDefinitionReductionEvidence {
                    definition_object,
                    defining_equality,
                    defining_equality_fact_id,
                    application_side: application_side.clone(),
                    reduced: comparison_candidate.clone(),
                    other_side: other_side.clone(),
                    application_is_left,
                    reduced_matches_other_by_alpha: alpha_equal,
                };
                let verified_by = VerifiedByResult::fact_with_checked_function_definition_reduction(
                    fact.clone(),
                    evidence,
                    Some(reason),
                );
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_known_fact(
                        fact,
                        verified_by,
                        Vec::new(),
                    )
                    .into(),
                ));
            }
            return Ok(Some(checked_definition_reduction_success(
                equal_fact,
                application_side,
                &comparison_candidate,
                &reason,
            )));
        }
        Ok(None)
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
        verify_state: &UseContextVerifyState,
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
        verify_state: &UseContextVerifyState,
    ) -> Result<bool, RuntimeError> {
        let result =
            self.verify_equal_fact_by_builtin_rules_and_known_equalities(equal_fact, verify_state)?;
        if result.is_true() {
            return Ok(true);
        }
        Ok(false)
    }

    fn verify_equal_fact_for_iterated_operator_functions(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<bool, RuntimeError> {
        // Iterated operators such as sum/product compare their summand
        // functions extensionally. Example:
        // `sum(1, n, fn(x Z) Z {f(x)}) = sum(1, n, fn(y Z) Z {f(y)})`.
        self.verify_equal_fact_for_corresponding_unary_args(equal_fact, verify_state)
    }

    pub(crate) fn verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
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
                    .is_true()
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
                    .is_true()
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
                    .map(|result| result.is_true())
                },
            ),
        }
    }

    fn verify_equal_fact_by_builtin_rules_and_known_equalities(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let result = self.verify_equal_fact_with_direct_routes(equal_fact)?;
        if result.is_true() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    "builtin rules".to_string(),
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
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    equal_fact.clone().into(),
                    same_shape_and_equal_args_reason(equal_fact),
                    Vec::new(),
                ))
                .into(),
            );
        }

        Ok((StmtUnknown::new()).into())
    }
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

fn checked_definition_reduction_success(
    equal_fact: &EqualFact,
    application_side: &Obj,
    reduced_side: &Obj,
    reason: &str,
) -> StmtResult {
    let fact: Fact = equal_fact.clone().into();
    let msg = format!(
        "{}; reduced goal side `{}` is compared with `{}` using stored equalities, terminating computation, anonymous-function beta reduction, or constructor descent",
        reason, application_side, reduced_side
    );
    let verified_by = VerifiedByResult::fact_with_note(fact.clone(), Some(msg));
    FactualStmtSuccess::new_with_verified_by_known_fact(fact, verified_by, Vec::new()).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_premise_structural_equality_still_requires_known_equal_leaves() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("zero_premise_structural_boundary.lit");

        let x: Obj = Identifier::new("x".to_string()).into();
        let y: Obj = Identifier::new("y".to_string()).into();
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();
        let left: Obj = Mul::new(
            Add::new(x.clone(), one.clone()).into(),
            Add::new(x, two.clone()).into(),
        )
        .into();
        let right: Obj = Mul::new(Add::new(y.clone(), one).into(), Add::new(y, two).into()).into();
        let equal_fact = EqualFact::new(left, right, default_line_file());

        assert!(runtime
            .verify_equal_fact_with_zero_premise_verification(&equal_fact)
            .expect("zero-premise equality boundary must not error")
            .is_unknown());
    }

    #[test]
    fn structural_equality_runs_only_from_the_outer_round() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("structural_equality_outer_round");

        let a: Obj = Identifier::new("A".to_string()).into();
        let b: Obj = Identifier::new("B".to_string()).into();
        let union_ab: Obj = Union::new(a.clone(), b.clone()).into();
        let union_ba: Obj = Union::new(b, a).into();
        let left: Obj =
            StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ab]).into();
        let right: Obj =
            StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ba]).into();
        let equal_fact = EqualFact::new(left, right, default_line_file());
        assert!(runtime
            .verify_equal_fact_by_known_equality(&equal_fact)
            .is_unknown());
        assert!(runtime
            .verify_equal_fact(&equal_fact, &UseContextVerifyState::new(1, true))
            .expect("later-round equality verification")
            .is_unknown());
        assert!(runtime
            .verify_equal_fact(&equal_fact, &UseContextVerifyState::new(0, true))
            .expect("outer-round equality verification")
            .is_true());
    }

    #[test]
    fn checked_definition_reduction_has_no_candidate_graph_or_ambient_mode() {
        let source = include_str!("verify_equality.rs");
        let reduction_impl = source
            .split("fn try_reduce_one_checked_definition_side(")
            .nth(1)
            .expect("direct checked-definition reduction must exist")
            .split("fn checked_function_definition_reduction_source(")
            .next()
            .expect("definition source lookup must follow direct reduction");

        assert!(reduction_impl
            .contains("equal_fact_sides_are_equal_by_terminating_reduction_and_congruence"));
        assert!(source.contains("!verify_state.well_defined_already_verified"));
        let obsolete_depth = ["known_equality_candidate_", "replay_depth"].concat();
        let obsolete_collector = ["collect_known_equality_", "pairs_from_envs"].concat();
        let obsolete_pair_attempt = ["try_verify_one_equality_", "representative_pair"].concat();
        assert!(!source.contains(&obsolete_depth));
        assert!(!source.contains(&obsolete_collector));
        assert!(!source.contains(&obsolete_pair_attempt));
        assert!(!reduction_impl.contains("verify_atomic_fact_with_known_forall"));
        assert!(!reduction_impl.contains("verify_equal_fact_with_direct_routes"));
        assert!(!reduction_impl.contains("verify_equal_fact("));

        let structural_source = include_str!("verify_builtin_rules/equality_structural.rs");
        let terminating_comparator = structural_source
            .split("fn equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(")
            .nth(1)
            .expect("terminating structural comparator must exist")
            .split("pub(crate) fn same_shape_and_corresponding_args_match")
            .next()
            .expect("central structural matcher must follow the terminating comparator");
        assert!(terminating_comparator.contains("verify_equal_fact_with_known_fact"));
        assert!(terminating_comparator.contains("verify_equal_fact_by_direct_evaluation"));
        assert!(
            !terminating_comparator.contains("verify_equal_fact_with_zero_premise_verification")
        );
        assert!(terminating_comparator.contains("beta_reduce_complete_anonymous_application_once"));
        let obsolete_one_rule = ["verify_atomic_fact_with_one_", "builtin_rule"].concat();
        assert!(!terminating_comparator.contains(&obsolete_one_rule));
        let obsolete_inner = ["verify_atomic_fact_with_builtin_rules_", "inner"].concat();
        assert!(!terminating_comparator.contains(&obsolete_inner));
        assert!(!terminating_comparator.contains("resolve_obj"));
        assert!(!terminating_comparator.contains("verify_atomic_fact_with_known_forall"));
        assert!(!terminating_comparator.contains("verify_equal_fact("));

        let atomic_source = include_str!("verify_atomic_fact.rs");
        assert!(!atomic_source.contains(&obsolete_depth));
        let forall_source = include_str!("verify_atomic_fact_with_known_forall.rs");
        assert!(!forall_source.contains(&obsolete_depth));

        let equality_builtin_source = include_str!("verify_builtin_rules/equality_dispatch.rs");
        assert!(!equality_builtin_source.contains(&obsolete_depth));

        let set_membership_source =
            include_str!("verify_builtin_rules/in_fact_builtin/set_membership.rs");
        assert!(!set_membership_source.contains(&obsolete_depth));
    }

    #[test]
    fn terminating_comparator_allows_computation_and_bounded_symbolic_normalization() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("terminating_structural_computation");
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();
        let one_plus_one: Obj = Add::new(one.clone(), one).into();

        assert!(runtime.equal_fact_sides_are_congruent_by_known_equalities(
            &EqualFact::new_from_refs(&one_plus_one, &two, default_line_file()),
        ));
        assert!(runtime
            .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
                &EqualFact::new_from_refs(&one_plus_one, &two, default_line_file()),
            )
            .expect("terminating structural comparison"));

        let x: Obj = Identifier::new("x".to_string()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let x_plus_zero: Obj = Add::new(x.clone(), zero).into();
        assert!(runtime
            .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
                &EqualFact::new_from_refs(&x_plus_zero, &x, default_line_file()),
            )
            .expect("bounded symbolic normalization"));

        let y: Obj = Identifier::new("y".to_string()).into();
        let x_minus_y: Obj = Sub::new(x.clone(), y.clone()).into();
        let y_minus_x: Obj = Sub::new(y.clone(), x.clone()).into();
        let abs_x_minus_y: Obj = Abs::new(x_minus_y).into();
        let abs_y_minus_x: Obj = Abs::new(y_minus_x).into();
        assert!(runtime
            .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
                &EqualFact::new_from_refs(&abs_x_minus_y, &abs_y_minus_x, default_line_file(),),
            )
            .expect("absolute-value sign normalization"));

        let abs_x: Obj = Abs::new(x).into();
        let abs_y: Obj = Abs::new(y).into();
        assert!(!runtime
            .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
                &EqualFact::new_from_refs(&abs_x, &abs_y, default_line_file()),
            )
            .expect("unrelated absolute values must not compare equal"));
    }
}
