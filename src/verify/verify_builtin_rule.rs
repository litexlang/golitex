use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    builtin_in_fact_result_for_evaluated_number_in_standard_set,
    builtin_not_in_fact_result_for_evaluated_number_in_standard_set,
};

impl Runtime {
    pub(crate) fn verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let leaf_result =
            self.verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation(goal)?;
        if leaf_result.is_true() {
            return Ok(leaf_result);
        }

        let builtin_state = UseBuiltinRuleVerifyState::new();
        self.verify_atomic_fact_with_one_builtin_rule(goal, &builtin_state)
    }

    pub(crate) fn verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let known_result = self.verify_known_non_forall_atomic_fact(goal)?;
        if known_result.is_true() {
            return Ok(known_result);
        }

        let result = self.verify_atomic_fact_by_builtin_computation(goal);
        Ok(self.remember_successful_atomic_fact_for_statement(goal, result))
    }

    pub(crate) fn verify_known_non_forall_atomic_fact(
        &mut self,
        goal: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let result = match goal {
            AtomicFact::EqualFact(fact) => Ok(self.verify_objs_are_equal_by_known_equality(
                &fact.left,
                &fact.right,
                fact.line_file.clone(),
            )),
            _ => self.verify_non_equational_atomic_fact_with_known_atomic_facts(goal),
        }?;
        Ok(self.remember_successful_atomic_fact_for_statement(goal, result))
    }

    pub(crate) fn verify_builtin_rule_premise(
        &mut self,
        child: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let leaf_result =
            self.verify_atomic_fact_with_non_forall_facts_then_with_builtin_computation(child)?;
        if leaf_result.is_true() {
            return Ok(leaf_result);
        }
        if !builtin_state.can_apply_builtin_rule() {
            return Ok(StmtUnknown::new().into());
        }
        self.verify_atomic_fact_with_one_builtin_rule(child, builtin_state)
    }

    pub(crate) fn verify_atomic_fact_by_builtin_computation(
        &self,
        fact: &AtomicFact,
    ) -> StmtResult {
        match fact {
            AtomicFact::InFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return StmtUnknown::new().into();
                };
                let Some(number) = fact
                    .element
                    .evaluate_to_normalized_decimal_number()
                    .or_else(|| match self.resolve_obj(&fact.element) {
                        Obj::Number(number) => Some(number),
                        _ => None,
                    })
                else {
                    return StmtUnknown::new().into();
                };
                builtin_in_fact_result_for_evaluated_number_in_standard_set(fact, &number, set)
            }
            AtomicFact::NotInFact(fact) => {
                let Obj::StandardSet(set) = &fact.set else {
                    return StmtUnknown::new().into();
                };
                let Some(number) = fact
                    .element
                    .evaluate_to_normalized_decimal_number()
                    .or_else(|| match self.resolve_obj(&fact.element) {
                        Obj::Number(number) => Some(number),
                        _ => None,
                    })
                else {
                    return StmtUnknown::new().into();
                };
                builtin_not_in_fact_result_for_evaluated_number_in_standard_set(fact, &number, set)
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                if self.verify_number_comparison_builtin_rule(fact) != Some(true) {
                    return StmtUnknown::new().into();
                }
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    fact.clone().into(),
                    "number comparison".to_string(),
                    Vec::new(),
                )
                .into()
            }
            AtomicFact::EqualFact(fact) => {
                let left_resolved = self.resolve_obj(&fact.left);
                let right_resolved = self.resolve_obj(&fact.right);
                let reason = if fact
                    .left
                    .two_objs_can_be_calculated_and_equal_by_calculation(&fact.right)
                    || left_resolved
                        .two_objs_can_be_calculated_and_equal_by_calculation(&right_resolved)
                {
                    "direct numeric computation"
                } else if objs_equal_by_bounded_symbolic_normalization(&fact.left, &fact.right)
                    || objs_equal_by_bounded_symbolic_normalization(&left_resolved, &right_resolved)
                {
                    // Bounded, obligation-free symbolic normalization. Example:
                    // `a * t + 0 = a * t` and `abs(x - y) = abs(y - x)`.
                    "bounded symbolic normalization"
                } else {
                    return StmtUnknown::new().into();
                };
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    fact.clone().into(),
                    reason.to_string(),
                    Vec::new(),
                )
                .into()
            }
            AtomicFact::NotEqualFact(fact) => self
                .verify_resolved_numeric_not_equal_without_builtin_recursion(fact)
                .unwrap_or_else(|| StmtUnknown::new().into()),
            AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_) => {
                self.verify_prime_fact_by_computation(fact)
            }
            _ => StmtUnknown::new().into(),
        }
    }

    pub(crate) fn verify_builtin_rule_premises(
        &mut self,
        children: &[AtomicFact],
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let mut results = Vec::with_capacity(children.len());
        for child in children {
            let result = self.verify_builtin_rule_premise(child, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        Ok(Some(results))
    }

    fn verify_atomic_fact_with_builtin_rules_inner(
        &mut self,
        goal: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(result) = self.try_verify_atomic_fact_from_known_set_builder_membership(goal)? {
            return Ok(result);
        }
        match goal {
            AtomicFact::EqualFact(fact) => self.verify_equality_by_builtin_rules(
                &fact.left,
                &fact.right,
                fact.line_file.clone(),
                builtin_state,
            ),
            _ => {
                self.verify_non_equational_atomic_fact_with_builtin_rules_inner(goal, builtin_state)
            }
        }
    }

    fn verify_atomic_fact_with_one_builtin_rule(
        &mut self,
        goal: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if !builtin_state.can_apply_builtin_rule() {
            return Ok(StmtUnknown::new().into());
        }
        let child_state = builtin_state.after_applying_builtin_rule();
        let result = self.verify_atomic_fact_with_builtin_rules_inner(goal, &child_state)?;
        Ok(self.remember_successful_atomic_fact_for_statement(goal, result))
    }
}

fn objs_equal_by_bounded_symbolic_normalization(left: &Obj, right: &Obj) -> bool {
    if objs_equal_by_rational_expression_evaluation(left, right) {
        return true;
    }

    // Absolute value is invariant under sign change. This remains a bounded
    // computation leaf: it creates no proof obligations and applies no rules.
    // Example: `abs(x - y) = abs(y - x)`.
    let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (left, right) else {
        return false;
    };
    let negative_one: Obj = Number::new("-1".to_string()).into();
    let negated_right: Obj = Mul::new(negative_one, right_abs.arg.as_ref().clone()).into();
    objs_equal_by_rational_expression_evaluation(left_abs.arg.as_ref(), &negated_right)
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    #[test]
    fn raw_builtin_dispatch_has_only_the_single_rule_entry_point() {
        let source = include_str!("verify_builtin_rule.rs");
        let full_verify_state_constructor = ["UseContextVerifyState", "::new("].concat();
        let raw_dispatch = ["verify_atomic_fact_with_builtin_rules_", "inner("].concat();
        let creates_full_verify_state =
            source
                .match_indices(&full_verify_state_constructor)
                .any(|(index, _)| {
                    source[..index]
                        .chars()
                        .next_back()
                        .is_none_or(|ch| !(ch.is_ascii_alphanumeric() || ch == '_'))
                });
        assert!(!creates_full_verify_state);
        assert_eq!(
            source.matches(&raw_dispatch).count(),
            2,
            "the raw dispatcher must only be defined once and called by the one-rule entry point"
        );
    }

    #[test]
    fn automatic_builtin_rule_files_do_not_create_fresh_roots_or_bypass_the_limited_entry() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/verify/verify_builtin_rules");
        visit_rust_files(&dir, &mut |path, source| {
            assert!(
                !source.contains("BuiltinRuleVerifyState::new"),
                "{} creates a fresh recursive builtin root",
                path.display()
            );
            assert!(
                !source.contains("verify_atomic_fact_with_builtin_rules("),
                "{} bypasses the depth-limited builtin premise entry point",
                path.display()
            );
        });
    }

    #[test]
    fn computation_matchers_are_not_repeated_in_the_direct_dispatchers() {
        let non_equational = include_str!("verify_builtin_rules/non_equational_dispatch.rs");
        assert!(!non_equational.contains("verify_prime_fact_by_computation"));

        let numeric_order = include_str!("verify_builtin_rules/number_compare.rs");
        assert_eq!(
            numeric_order
                .matches("verify_number_comparison_builtin_rule(")
                .count(),
            1,
            "number comparison computation must only be defined here, not called again by the direct rule dispatcher"
        );

        let extrema = include_str!("verify_builtin_rules/order_semantics_builtin.rs");
        assert!(!extrema.contains("verify_finite_set_members_are_at_most"));
        assert!(!extrema.contains("verify_finite_set_members_are_at_least"));
    }

    #[test]
    fn structural_equality_uses_one_shape_matcher_only_in_structural_routes() {
        let common_leaf = include_str!("verify_builtin_rule.rs");
        let common_leaf_impl = common_leaf
            .split("#[cfg(test)]")
            .next()
            .expect("builtin rule implementation must precede its tests");
        let known_fact_index = common_leaf_impl
            .find("verify_known_non_forall_atomic_fact(goal)?")
            .expect("common equality leaf must first check known non-forall facts");
        let computation_index = common_leaf_impl
            .find("verify_atomic_fact_by_builtin_computation(goal)")
            .expect("common equality leaf must finish with builtin computation");
        assert!(known_fact_index < computation_index);
        assert!(!common_leaf_impl.contains("try_verify_equality_by_corresponding_known_equalities"));

        let equality_structural = include_str!("verify_builtin_rules/equality_structural.rs");
        let known_only_impl = equality_structural
            .split("pub fn verify_objs_are_equal_by_known_equality(")
            .nth(1)
            .expect("known-only equality implementation must exist")
            .split("fn verify_objs_are_equal_directly_known_only(")
            .next()
            .expect("direct known-only implementation must follow the public entry");
        assert!(known_only_impl.contains("verify_objs_are_equal_directly_known_only("));
        assert!(!known_only_impl.contains("same_shape_and_corresponding_args_match("));
        assert!(
            !equality_structural.contains("try_verify_equality_by_corresponding_known_equalities")
        );
        assert_eq!(
            equality_structural
                .matches("fn same_shape_and_corresponding_args_match")
                .count(),
            1,
            "constructor decomposition must have one implementation",
        );
        let replay_safe_impl = equality_structural
            .split("pub(crate) fn objs_are_congruent_by_replay_safe_equality_routes(")
            .nth(1)
            .expect("replay-safe structural equality implementation must exist")
            .split("pub(crate) fn same_shape_and_corresponding_args_match")
            .next()
            .expect("central matcher must follow replay-safe comparison");
        assert!(replay_safe_impl.contains("same_shape_and_corresponding_args_match("));

        let equality_dispatch = include_str!("verify_builtin_rules/equality_dispatch.rs");
        assert!(
            !equality_dispatch.contains("try_verify_equality_by_corresponding_known_equalities")
        );

        let equality = include_str!("verify_equality.rs");
        let full_equality_impl = equality
            .split("pub fn verify_equal_fact(")
            .nth(1)
            .expect("full equality implementation must exist")
            .split("pub(crate) fn verify_equality_with_known_equalities(")
            .next()
            .expect("known-equality replay must follow full equality");
        assert!(!full_equality_impl.contains("FnEqualFact"));
        assert!(!full_equality_impl.contains("EqualFact::new("));
        let round_zero_index = full_equality_impl
            .find("if verify_state.is_round_0()")
            .expect("structural equality must be restricted to round zero");
        let structural_index = full_equality_impl
            .find(
                "verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively",
            )
            .expect("full equality must contain the structural equality route");
        assert!(round_zero_index < structural_index);
        let recursive_structural_impl = equality
            .split(
                "pub(crate) fn verify_objs_are_equal_when_they_have_same_builtin_shape_and_equal_args_recursively(",
            )
            .nth(1)
            .expect("recursive structural equality implementation must exist")
            .split("fn verify_two_objs_equal_by_builtin_rules_and_known_equalities(")
            .next()
            .expect("recursive child verifier must follow structural equality");
        assert!(recursive_structural_impl.contains("same_shape_and_corresponding_args_match("));
    }

    fn visit_rust_files(dir: &Path, f: &mut impl FnMut(&Path, &str)) {
        for entry in fs::read_dir(dir).expect("read builtin rule source directory") {
            let path = entry.expect("read builtin rule directory entry").path();
            if path.is_dir() {
                visit_rust_files(&path, f);
            } else if path.extension().and_then(|value| value.to_str()) == Some("rs") {
                let source = fs::read_to_string(&path).expect("read builtin rule source file");
                f(&path, &source);
            }
        }
    }
}
