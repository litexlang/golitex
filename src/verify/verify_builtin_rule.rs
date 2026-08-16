use crate::prelude::*;
impl Runtime {
    pub(crate) fn verify_builtin_rule_premise(
        &mut self,
        child: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match child {
            AtomicFact::EqualFact(equal_fact) => {
                let leaf_result = self.verify_equal_fact_with_leaf_routes(equal_fact)?;
                if leaf_result.is_true() || !builtin_state.can_apply_builtin_rule() {
                    return Ok(leaf_result);
                }
                self.verify_equal_fact_with_one_builtin_rule(equal_fact, builtin_state)
            }
            _ => {
                let zero_premise_result =
                    self.verify_non_equational_atomic_fact_with_zero_premise_verification(child)?;
                if zero_premise_result.is_true() || !builtin_state.can_apply_builtin_rule() {
                    return Ok(zero_premise_result);
                }
                self.verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule(
                    child,
                    builtin_state,
                )
            }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::Path;

    #[test]
    fn raw_builtin_dispatch_has_only_the_single_rule_entry_point() {
        let source = include_str!("verify_builtin_rule.rs");
        let implementation = source
            .split("#[cfg(test)]")
            .next()
            .expect("builtin premise implementation must precede its tests");
        let full_verify_state_constructor = ["UseContextVerifyState", "::new("].concat();
        let creates_full_verify_state = implementation
            .match_indices(&full_verify_state_constructor)
            .any(|(index, _)| {
                source[..index]
                    .chars()
                    .next_back()
                    .is_none_or(|ch| !(ch.is_ascii_alphanumeric() || ch == '_'))
            });
        assert!(!creates_full_verify_state);
        assert_eq!(
            implementation.matches("match child").count(),
            1,
            "a builtin premise must dispatch to its fact-family owner exactly once"
        );
        assert!(implementation.contains("verify_equal_fact_with_one_builtin_rule"));
        assert!(implementation
            .contains("verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule"));
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
    fn integer_leaf_reuses_known_finiteness_without_opening_a_direct_rule() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("integer_leaf_finite_set_size_test.lit");

        let start: Obj = Identifier::new("a".to_string()).into();
        let end: Obj = Identifier::new("b".to_string()).into();
        let set: Obj = ClosedRange::new(start, end).into();
        let size: Obj = FiniteSetSize::new(set.clone()).into();
        let line_file = default_line_file();

        let cold = runtime
            .verify_objects_are_known_integers_in_builtin_leaf(&[&size], &line_file)
            .expect("integer leaf verification should not error");
        assert!(
            cold.is_none(),
            "the integer leaf must not open the direct closed-range finiteness rule"
        );

        let finite_fact: AtomicFact = IsFiniteSetFact::new(set, line_file.clone()).into();
        let finite_result = runtime
            .verify_non_equational_atomic_fact_with_direct_routes(&finite_fact)
            .expect("direct finiteness verification should not error");
        assert!(finite_result.is_true());

        let mut warm = runtime
            .verify_objects_are_known_integers_in_builtin_leaf(&[&size], &line_file)
            .expect("integer leaf verification should not error")
            .expect("known finiteness should type finite_set_size as an integer");
        let size_result = warm
            .pop()
            .expect("finite_set_size integer evidence should be retained")
            .into_factual_success()
            .expect("finite_set_size integer evidence should be factual");
        let VerifiedByResult::BuiltinRule(rule) = size_result.underlying_verified_by() else {
            panic!("finite_set_size membership should keep its builtin rule evidence");
        };
        assert_eq!(
            rule.subgoals.len(),
            1,
            "the known finite-set premise must remain in the proof tree"
        );
    }

    #[test]
    fn direct_evaluation_matchers_are_not_repeated_in_builtin_rule_dispatchers() {
        let non_equational = include_str!("verify_builtin_rules/non_equational_dispatch.rs");
        assert!(!non_equational.contains("verify_prime_fact_by_computation"));

        let numeric_order = include_str!("verify_builtin_rules/number_compare.rs");
        assert_eq!(
            numeric_order
                .matches("verify_number_comparison_builtin_rule(")
                .count(),
            1,
            "number-comparison direct evaluation must be defined once and stay out of the premise-producing rule dispatcher"
        );

        let extrema = include_str!("verify_builtin_rules/order_semantics_builtin.rs");
        assert!(!extrema.contains("verify_finite_set_members_are_at_most"));
        assert!(!extrema.contains("verify_finite_set_members_are_at_least"));
    }

    #[test]
    fn obsolete_mixed_direct_routes_cannot_reappear_in_source() {
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let obsolete = [
            [
                "verify_atomic_fact_with_known_non_forall_facts_then_",
                "with_builtin_rules",
            ]
            .concat(),
            [
                "verify_atomic_fact_with_non_forall_facts_then_",
                "with_builtin_computation",
            ]
            .concat(),
            ["verify_known_non_forall_", "atomic_fact"].concat(),
            ["verify_atomic_fact_by_builtin_", "computation"].concat(),
            ["verify_atomic_fact_with_one_", "builtin_rule"].concat(),
            ["verify_atomic_fact_with_builtin_rules_", "inner"].concat(),
            [
                "verify_non_equational_atomic_fact_with_known_fact_then_",
                "with_builtin_computation",
            ]
            .concat(),
            [
                "verify_non_equational_atomic_fact_by_builtin_",
                "computation",
            ]
            .concat(),
            [
                "verify_non_equational_atomic_fact_with_one_",
                "builtin_rule",
            ]
            .concat(),
        ];
        visit_rust_files(&src, &mut |path, source| {
            for name in &obsolete {
                assert!(
                    !source.contains(name),
                    "{} reintroduces obsolete cross-family route `{}`",
                    path.display(),
                    name
                );
            }
        });
    }

    #[test]
    fn family_owned_direct_routes_preserve_policy_order_and_boundaries() {
        let equality = include_str!("verify_equality.rs");
        let equality_direct = equality
            .split("pub(crate) fn verify_equal_fact_with_direct_routes(")
            .nth(1)
            .expect("equality owner must expose a direct route")
            .split("pub(crate) fn verify_equal_fact_with_known_fact(")
            .next()
            .expect("known-equality leaf must follow the equality direct route");
        let equality_builtin = equality_direct
            .find("verify_equal_fact_with_one_builtin_rule")
            .expect("equality direct route must try a named builtin rule");
        let equality_leaf = equality_direct
            .find("verify_equal_fact_with_leaf_routes")
            .expect("equality direct route must retain its structural leaf fallback");
        assert!(equality_builtin < equality_leaf);

        let non_equational = include_str!("verify_non_equational_atomic_fact.rs");
        let non_equational_direct = non_equational
            .split("pub(crate) fn verify_non_equational_atomic_fact_with_direct_routes(")
            .nth(1)
            .expect("non-equational owner must expose a direct route")
            .split("pub(crate) fn verify_non_equational_atomic_fact_with_known_fact(")
            .next()
            .expect("known-fact leaf must follow the non-equational direct route");
        let non_equational_zero_premise = non_equational_direct
            .find("verify_non_equational_atomic_fact_with_zero_premise_verification")
            .expect("non-equational direct route must begin with zero-premise verification");
        let non_equational_builtin = non_equational_direct
            .find("verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule")
            .expect("non-equational direct route must finish with one premise-producing rule");
        assert!(non_equational_zero_premise < non_equational_builtin);

        let zero_premise_impl = non_equational
            .split(
                "pub(crate) fn verify_non_equational_atomic_fact_with_zero_premise_verification(",
            )
            .nth(1)
            .expect("non-equational owner must define zero-premise verification")
            .split("pub(crate) fn verify_non_equational_atomic_fact_by_direct_evaluation(")
            .next()
            .expect("direct evaluation must follow zero-premise verification");
        let known_index = zero_premise_impl
            .find("verify_non_equational_atomic_fact_with_known_fact(atomic_fact)")
            .expect("zero-premise verification must try known facts first");
        let evaluation_index = zero_premise_impl
            .find("verify_non_equational_atomic_fact_by_direct_evaluation(atomic_fact)")
            .expect("zero-premise verification must finish with direct evaluation");
        assert!(known_index < evaluation_index);

        let direct_evaluation_impl = non_equational
            .split("pub(crate) fn verify_non_equational_atomic_fact_by_direct_evaluation(")
            .nth(1)
            .expect("non-equational owner must define direct evaluation")
            .split(
                "pub(crate) fn verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule(",
            )
            .next()
            .expect("premise-producing rules must follow direct evaluation");
        assert!(!direct_evaluation_impl.contains("UseBuiltinRuleVerifyState"));
        assert!(!direct_evaluation_impl.contains("verify_builtin_rule_premise"));

        let strategy = include_str!("verify_builtin_strategy.rs");
        let child_dispatch = strategy
            .split("pub(crate) fn verify_builtin_strategy_child(")
            .nth(1)
            .expect("strategy child dispatcher must exist")
            .split("pub(crate) fn verify_atomic_fact_with_builtin_strategy(")
            .next()
            .expect("top-level strategy dispatcher must follow its child dispatcher");
        assert_eq!(child_dispatch.matches("match atomic_fact").count(), 1);
        assert!(child_dispatch.contains("verify_equal_fact_with_direct_routes"));
        assert!(child_dispatch.contains("verify_non_equational_atomic_fact_with_direct_routes"));

        let known_forall = include_str!("verify_atomic_fact_with_known_forall.rs");
        let forward = known_forall
            .split("fn verify_atomic_fact_with_known_forall_forward(")
            .nth(1)
            .expect("known-forall forward matcher must be shared")
            .split("fn get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(")
            .next()
            .expect("known-forall lookup must follow the shared matcher");
        assert!(!forward.contains("fact_with_reversed_args"));
        let equality_wrapper = known_forall
            .split("pub(crate) fn verify_equal_fact_with_known_forall(")
            .nth(1)
            .expect("equality must own reverse known-forall retry")
            .split("fn verify_atomic_fact_with_known_forall_forward(")
            .next()
            .expect("shared forward matcher must follow the equality wrapper");
        assert!(equality_wrapper.contains("fact_with_reversed_args"));
    }

    #[test]
    fn structural_equality_uses_one_shape_matcher_only_in_structural_routes() {
        let equality_owner = include_str!("verify_equality.rs");
        let equality_leaf_impl = equality_owner
            .split("pub(crate) fn verify_equal_fact_with_known_fact_then_computation(")
            .nth(1)
            .expect("equality owner must define its known/computation leaf")
            .split("pub(crate) fn verify_equal_fact_with_leaf_routes(")
            .next()
            .expect("equality structural leaf must follow known/computation");
        let known_fact_index = equality_leaf_impl
            .find("verify_equal_fact_with_known_fact(equal_fact)")
            .expect("equality leaf must first check known equality");
        let computation_index = equality_leaf_impl
            .find("verify_equal_fact_by_builtin_computation(equal_fact)")
            .expect("equality leaf must finish with builtin computation");
        assert!(known_fact_index < computation_index);
        assert!(
            !equality_leaf_impl.contains("try_verify_equality_by_corresponding_known_equalities")
        );

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
        let terminating_impl = equality_structural
            .split("pub(crate) fn objs_are_equal_by_terminating_reduction_and_congruence(")
            .nth(1)
            .expect("terminating structural equality implementation must exist")
            .split("pub(crate) fn same_shape_and_corresponding_args_match")
            .next()
            .expect("central matcher must follow terminating comparison");
        assert!(terminating_impl.contains("same_shape_and_corresponding_args_match("));

        let equality_dispatch = include_str!("verify_builtin_rules/equality_dispatch.rs");
        assert!(
            !equality_dispatch.contains("try_verify_equality_by_corresponding_known_equalities")
        );

        let equality = include_str!("verify_equality.rs");
        let full_equality_impl = equality
            .split("pub fn verify_equal_fact(")
            .nth(1)
            .expect("full equality implementation must exist")
            .split("fn verify_equality_after_one_checked_definition_reduction(")
            .next()
            .expect("direct checked-definition reduction must follow full equality");
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
