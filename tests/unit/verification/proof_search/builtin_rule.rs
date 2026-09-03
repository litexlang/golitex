//! Tests for builtin-rule proof search.

use super::*;
use std::fs;
use std::path::Path;

#[test]
fn builtin_premise_dispatch_has_one_quantifier_free_entry_and_one_atomic_leaf() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/proof_search/builtin_rule.rs"
    ));
    let implementation = source
        .split("#[cfg(test)]")
        .next()
        .expect("builtin premise implementation must precede its tests");
    let fresh_proof_search_state_constructor = ["VerifyState", "::initial("].concat();
    let creates_full_verify_state = implementation
        .match_indices(&fresh_proof_search_state_constructor)
        .any(|(index, _)| {
            source[..index]
                .chars()
                .next_back()
                .is_none_or(|ch| !(ch.is_ascii_alphanumeric() || ch == '_'))
        });
    assert!(!creates_full_verify_state);
    assert_eq!(implementation.matches("match premise").count(), 2);
    assert!(implementation.contains("QuantifierFreeFact::AndFact"));
    assert!(implementation.contains("QuantifierFreeFact::ChainFact"));
    assert!(implementation.contains("QuantifierFreeFact::OrFact"));
    assert!(implementation.contains("verify_or_fact_with_known_or_facts"));
    assert!(implementation.contains("DisjunctionIntroductionBuiltinRuleEvidence"));
    assert!(!implementation.contains("verify_fact_full("));
    assert!(!implementation.contains("verify_quantifier_free_fact("));
    assert!(!implementation.contains("verify_quantifier_free_fact_restricted_known_builtin("));
    assert!(implementation.contains("verify_equal_fact_with_one_premise_producing_builtin_rule"));
    assert!(implementation
        .contains("verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule"));
}

#[test]
fn automatic_builtin_rule_files_do_not_create_fresh_roots_or_bypass_the_limited_entry() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/verification/builtin_rules");
    visit_rust_files(&dir, &mut |path, source| {
        assert!(
            !source.contains("BuiltinRuleSearchState::initial"),
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
fn quantifier_free_premise_structure_does_not_reset_the_builtin_depth_budget() {
    let line_file = default_line_file();
    let leaf: AtomicFact =
        IsSetFact::new(Number::new("1".to_string()).into(), line_file.clone()).into();
    let premise = QuantifierFreeFact::OrFact(OrFact::new(
        vec![AndChainAtomicFact::AtomicFact(leaf)],
        line_file,
    ));

    let root_state = BuiltinRuleSearchState::initial();
    let child_state = root_state.after_applying_rule();
    let mut child_runtime = Runtime::default();
    child_runtime.start_isolated_source("qff_premise_child_depth.lit");
    let child_result = child_runtime
        .try_verify_builtin_rule_premise(&premise, &child_state)
        .expect("bounded compound-premise verification should not error");
    assert!(
        child_result.is_none(),
        "logical compound structure must not reopen a consumed builtin-rule step"
    );

    let mut root_runtime = Runtime::default();
    root_runtime.start_isolated_source("qff_premise_root_depth.lit");
    let root_result = root_runtime
        .try_verify_builtin_rule_premise(&premise, &root_state)
        .expect("root compound-premise verification should not error");
    assert!(
        root_result.is_some(),
        "the same atomic leaf should remain available when the root budget is unused"
    );
}

#[test]
fn quantifier_free_and_and_chain_premises_verify_every_atomic_leaf() {
    let line_file = default_line_file();
    let one: Obj = Number::new("1".to_string()).into();
    let two: Obj = Number::new("2".to_string()).into();
    let three: Obj = Number::new("3".to_string()).into();
    let less_one_two: AtomicFact =
        LessFact::new(one.clone(), two.clone(), line_file.clone()).into();
    let less_two_three: AtomicFact =
        LessFact::new(two.clone(), three.clone(), line_file.clone()).into();
    let and_premise = QuantifierFreeFact::AndFact(AndFact::new(
        vec![less_one_two, less_two_three],
        line_file.clone(),
    ));
    let chain_premise = QuantifierFreeFact::ChainFact(ChainFact::new(
        vec![one, two, three],
        vec![
            AtomicName::WithoutMod(LESS.to_string()),
            AtomicName::WithoutMod(LESS.to_string()),
        ],
        line_file,
    ));

    let child_state = BuiltinRuleSearchState::initial().after_applying_rule();
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("qff_and_chain_premises.lit");
    let and_result = runtime
        .try_verify_builtin_rule_premise(&and_premise, &child_state)
        .expect("conjunction premise verification should not error");
    assert!(and_result.is_some());
    let chain_result = runtime
        .try_verify_builtin_rule_premise(&chain_premise, &child_state)
        .expect("chain premise verification should not error");
    assert!(chain_result.is_some());
}

#[test]
fn integer_leaf_reuses_known_finiteness_without_opening_a_direct_rule() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("integer_leaf_finite_set_size_test.lit");
    let (_, setup_error) = crate::test_support::execute_source("have a, b Z\n", &mut runtime);
    assert!(setup_error.is_none(), "fixture endpoints: {setup_error:?}");

    let start: Obj = Identifier::new_bound(
        "a".to_string(),
        runtime
            .resolved_identifier_symbol("a")
            .expect("fixture a binding"),
    )
    .into();
    let end: Obj = Identifier::new_bound(
        "b".to_string(),
        runtime
            .resolved_identifier_symbol("b")
            .expect("fixture b binding"),
    )
    .into();
    let set: Obj = ClosedRange::new(start, end).into();
    let size: Obj = FiniteSetSize::new(set.clone()).into();
    let line_file = default_line_file();

    let cold = runtime
        .verify_objects_are_known_integers_in_builtin_leaf(
            &[&size],
            &line_file,
            &VerifyState::initial(),
        )
        .expect("integer leaf verification should not error");
    assert!(
        cold.is_none(),
        "the integer leaf must not open the direct closed-range finiteness rule"
    );

    let finite_fact: AtomicFact = IsFiniteSetFact::new(set, line_file.clone()).into();
    // This unit isolates proof-search reuse. The symbolic endpoints have real
    // integer declarations, so the generated finiteness fact can cross the
    // ordinary full-WD completion boundary.
    let verify_state = VerifyState::initial();
    let finite_result = runtime
        .verify_atomic_fact(&finite_fact, &verify_state)
        .expect("direct finiteness verification should not error");
    assert!(finite_result.is_success());

    let mut warm = runtime
        .verify_objects_are_known_integers_in_builtin_leaf(&[&size], &line_file, &verify_state)
        .expect("integer leaf verification should not error")
        .expect("known finiteness should type finite_set_size as an integer");
    let size_result = warm
        .pop()
        .expect("finite_set_size integer evidence should be retained")
        .into_verified()
        .expect("finite_set_size integer evidence should be factual");
    let SuccessFactProofResult::BuiltinRule(rule) = size_result.underlying_verified_by() else {
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
    let non_equational = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/builtin_rules/non_equational_dispatch.rs"
    ));
    assert!(!non_equational.contains("verify_prime_fact_by_computation"));

    let equality = crate::verification::equality_dispatch_source::SOURCE;
    assert!(!equality.contains("objs_match_for_pattern_and_calculation"));
    assert!(!equality.contains("objs_equal_by_rational_expression_evaluation"));

    let numeric_order = crate::verification::number_compare_source::SOURCE;
    assert_eq!(
            numeric_order
                .matches("verify_number_comparison_builtin_rule(")
                .count(),
            1,
            "number-comparison direct evaluation must be defined once and stay out of the premise-producing rule dispatcher"
        );

    let extrema = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/builtin_rules/order_semantics_builtin.rs"
    ));
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
        ["verify_non_equational_atomic_fact_with_", "known_fact("].concat(),
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
        ["verify_equal_fact_with_known_fact_then_", "computation"].concat(),
        ["verify_equal_fact_with_", "leaf_routes"].concat(),
        ["verify_equal_fact_by_builtin_", "computation"].concat(),
        ["verify_equal_fact_with_one_", "builtin_rule"].concat(),
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
fn family_owned_bounded_builtin_routes_preserve_policy_order_and_boundaries() {
    let equality = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/equality/core.rs"
    ));
    let equality_direct = equality
        .split("pub fn verify_equal_fact_with_bounded_builtin_routes(")
        .nth(1)
        .expect("equality owner must expose a direct route")
        .split("pub fn verify_equal_fact_with_known_fact(")
        .next()
        .expect("known-equality leaf must follow the equality direct route");
    let equality_zero_premise = equality_direct
        .find("verify_equal_fact_with_zero_premise_verification")
        .expect("equality direct route must begin with zero-premise verification");
    let equality_builtin = equality_direct
        .find("verify_equal_fact_with_one_premise_producing_builtin_rule")
        .expect("equality direct route must finish with one premise-producing rule");
    assert!(equality_zero_premise < equality_builtin);

    let equality_zero_premise_impl = equality
        .split("pub fn verify_equal_fact_with_zero_premise_verification(")
        .nth(1)
        .expect("equality owner must define zero-premise verification")
        .split("pub fn verify_equal_fact_by_direct_evaluation(")
        .next()
        .expect("direct evaluation must follow zero-premise equality verification");
    let equality_known = equality_zero_premise_impl
        .find("verify_equal_fact_with_known_fact(equal_fact)")
        .expect("zero-premise equality must try known equality first");
    let equality_evaluation = equality_zero_premise_impl
        .find("verify_equal_fact_by_direct_evaluation(equal_fact)")
        .expect("zero-premise equality must try direct evaluation second");
    let equality_known_evaluation = equality_zero_premise_impl
        .find("verify_equal_fact_by_known_equality_then_direct_evaluation(")
        .expect("zero-premise equality must retain known-equality-assisted evaluation");
    let equality_structural = equality_zero_premise_impl
        .find("equal_fact_sides_are_equal_by_terminating_reduction_and_congruence")
        .expect("zero-premise equality must finish with terminating congruence");
    assert!(equality_known < equality_evaluation);
    assert!(equality_evaluation < equality_known_evaluation);
    assert!(equality_known_evaluation < equality_structural);

    let equality_direct_evaluation_impl = equality
        .split("pub fn verify_equal_fact_by_direct_evaluation(")
        .nth(1)
        .expect("equality owner must define direct evaluation")
        .split("pub fn verify_equal_fact_with_one_premise_producing_builtin_rule(")
        .next()
        .expect("premise-producing equality rules must follow direct evaluation");
    assert!(!equality_direct_evaluation_impl.contains("BuiltinRuleSearchState"));
    assert!(!equality_direct_evaluation_impl.contains("verify_builtin_rule_premise"));

    let non_equational = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/atomic/non_equational.rs"
    ));
    let non_equational_direct = non_equational
        .split("pub fn verify_non_equational_atomic_fact_with_bounded_builtin_routes(")
        .nth(1)
        .expect("non-equational owner must expose a direct route")
        .split("pub fn verify_non_equational_atomic_fact_with_zero_premise_verification(")
        .next()
        .expect("zero-premise verification must follow the non-equational direct route");
    let non_equational_zero_premise = non_equational_direct
        .find("verify_non_equational_atomic_fact_with_zero_premise_verification")
        .expect("non-equational direct route must begin with zero-premise verification");
    let non_equational_builtin = non_equational_direct
        .find("verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule")
        .expect("non-equational direct route must finish with one premise-producing rule");
    assert!(non_equational_zero_premise < non_equational_builtin);

    let zero_premise_impl = non_equational
        .split("pub fn verify_non_equational_atomic_fact_with_zero_premise_verification(")
        .nth(1)
        .expect("non-equational owner must define zero-premise verification")
        .split("pub fn verify_non_equational_atomic_fact_by_direct_evaluation(")
        .next()
        .expect("direct evaluation must follow zero-premise verification");
    let known_index = zero_premise_impl
        .find("verify_non_equational_atomic_fact_with_known_atomic_facts(atomic_fact)")
        .expect("zero-premise verification must try known facts first");
    let evaluation_index = zero_premise_impl
        .find("verify_non_equational_atomic_fact_by_direct_evaluation(atomic_fact)")
        .expect("zero-premise verification must finish with direct evaluation");
    assert!(known_index < evaluation_index);

    let direct_evaluation_impl = non_equational
        .split("pub fn verify_non_equational_atomic_fact_by_direct_evaluation(")
        .nth(1)
        .expect("non-equational owner must define direct evaluation")
        .split("pub fn verify_non_equational_atomic_fact_with_one_premise_producing_builtin_rule(")
        .next()
        .expect("premise-producing rules must follow direct evaluation");
    assert!(!direct_evaluation_impl.contains("BuiltinRuleSearchState"));
    assert!(!direct_evaluation_impl.contains("verify_builtin_rule_premise"));

    let strategy = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/proof_search/builtin_strategy.rs"
    ));
    let child_dispatch = strategy
        .split("pub fn verify_builtin_strategy_child(")
        .nth(1)
        .expect("strategy child dispatcher must exist")
        .split("pub fn verify_atomic_fact_with_builtin_strategy(")
        .next()
        .expect("top-level strategy dispatcher must follow its child dispatcher");
    assert_eq!(child_dispatch.matches("match atomic_fact").count(), 1);
    assert!(child_dispatch.contains("verify_equal_fact_with_bounded_builtin_routes"));
    assert!(
        child_dispatch.contains("verify_non_equational_atomic_fact_with_bounded_builtin_routes")
    );

    let known_forall = crate::verification::universal_search_source::SOURCE;
    let forward = known_forall
        .split("fn verify_atomic_fact_with_known_forall_forward(")
        .nth(1)
        .expect("known-forall forward matcher must be shared")
        .split("fn get_matched_atomic_fact_in_fallback_known_forall_fact_in_envs(")
        .next()
        .expect("known-forall lookup must follow the shared matcher");
    assert!(!forward.contains("fact_with_reversed_args"));
    let equality_wrapper = known_forall
        .split("pub fn verify_equal_fact_with_known_forall(")
        .nth(1)
        .expect("equality must own reverse known-forall retry")
        .split("fn verify_atomic_fact_with_known_forall_forward(")
        .next()
        .expect("shared forward matcher must follow the equality wrapper");
    assert!(equality_wrapper.contains("fact_with_reversed_args"));
}

#[test]
fn structural_equality_uses_one_shape_matcher_only_in_structural_routes() {
    let equality_structural = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/builtin_rules/equality_structural.rs"
    ));
    let known_without_evaluation_impl = equality_structural
        .split("pub fn verify_equal_fact_by_known_equality_without_direct_evaluation(")
        .nth(1)
        .expect("equality must expose a known-only leaf without direct evaluation")
        .split("fn verify_equal_fact_directly_known_only(")
        .next()
        .expect("the direct known-only implementation must follow its memoized entry");
    assert!(!known_without_evaluation_impl
        .contains("two_objs_can_be_calculated_and_equal_by_calculation"));
    let known_only_impl = equality_structural
        .split("pub fn verify_equal_fact_by_known_equality(")
        .nth(1)
        .expect("known-only equality implementation must exist")
        .split("fn verify_equal_fact_directly_known_only(")
        .next()
        .expect("direct known-only implementation must follow the public entry");
    assert!(known_only_impl.contains("verify_equal_fact_directly_known_only("));
    assert!(!known_only_impl.contains("same_shape_and_corresponding_args_match("));
    assert!(!equality_structural.contains("try_verify_equality_by_corresponding_known_equalities"));
    let direct_known_only_impl = equality_structural
        .split("fn verify_equal_fact_directly_known_only(")
        .nth(1)
        .expect("direct known-only equality implementation must exist")
        .split("pub fn equal_fact_sides_are_congruent_by_known_equalities(")
        .next()
        .expect("known congruence must follow direct known-only equality");
    assert!(!direct_known_only_impl.contains("resolve_obj"));
    assert!(!direct_known_only_impl.contains("two_objs_can_be_calculated_and_equal_by_calculation"));
    assert_eq!(
        equality_structural
            .matches("fn same_shape_and_corresponding_args_match")
            .count(),
        1,
        "constructor decomposition must have one implementation",
    );
    let terminating_impl = equality_structural
        .split("pub fn equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(")
        .nth(1)
        .expect("terminating structural equality implementation must exist")
        .split("pub fn same_shape_and_corresponding_args_match")
        .next()
        .expect("central matcher must follow terminating comparison");
    let known_index = terminating_impl
        .find("verify_equal_fact_with_known_fact(equal_fact)")
        .expect("terminating comparison must try known equality first");
    let evaluation_index = terminating_impl
        .find("verify_equal_fact_by_direct_evaluation(equal_fact)")
        .expect("terminating comparison must try direct evaluation second");
    let shape_index = terminating_impl
        .find("same_shape_and_corresponding_args_match(")
        .expect("terminating comparison must finish with constructor descent");
    assert!(known_index < evaluation_index);
    assert!(evaluation_index < shape_index);
    assert!(terminating_impl.contains("same_shape_and_corresponding_args_match("));
    assert!(!terminating_impl.contains("verify_equal_fact_with_zero_premise_verification"));

    let equality_dispatch = crate::verification::equality_dispatch_source::SOURCE;
    assert!(!equality_dispatch.contains("try_verify_equality_by_corresponding_known_equalities"));
    assert!(!equality_dispatch.contains("verify_equal_fact_by_direct_evaluation"));
    assert!(!equality_dispatch.contains("objs_match_for_pattern_and_calculation"));

    let equality = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/equality/core.rs"
    ));
    let full_equality_impl = equality
        .split("pub fn verify_equal_fact(")
        .nth(1)
        .expect("full equality implementation must exist")
        .split("fn try_verify_equal_fact_by_transforming_known_equal_representatives(")
        .next()
        .expect("transform composition helper must follow full equality");
    assert!(!full_equality_impl.contains("FnEqualFact"));
    assert!(!full_equality_impl.contains("EqualFact::new("));
    let round_zero_index = full_equality_impl
        .find("if verify_state.is_initial_round()")
        .expect("structural equality must be restricted to round zero");
    let structural_index = full_equality_impl
        .find(
            "verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively",
        )
        .expect("full equality must contain the structural equality route");
    assert!(round_zero_index < structural_index);
    let recursive_structural_impl = equality
            .split(
                "pub fn verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(",
            )
            .nth(1)
            .expect("recursive structural equality implementation must exist")
            .split("fn verify_equal_fact_by_builtin_rules_and_known_equalities(")
            .next()
            .expect("recursive child verifier must follow structural equality");
    assert!(recursive_structural_impl.contains("same_shape_and_corresponding_args_match("));
}

#[test]
fn equality_proof_apis_receive_the_owned_equal_fact() {
    // These helpers own, forward, or decide one equality proof obligation even when their
    // historical names do not contain `equal`. Keeping the complete fact preserves source
    // identity and prevents left/right orientation plus LineFile from drifting independently.
    let owned_equality_target_apis = [
        "try_verify_matrix_power_definition",
        "try_verify_finite_set_size_fn_range_from_known_injection",
        "try_verify_finite_set_size_from_known_bijection",
        "try_trig_quotient_definition",
        "verify_reduce_functions_pointwise_on_set",
        "verify_zero_product_factor_matches_target",
        "try_verify_sum_merge_ordered_pair",
        "verify_finite_set_sum_functions_pointwise_premise",
        "try_verify_intersection_from_subset",
        "try_verify_literal_set_intersection_filter",
        "try_verify_one_subtraction_from_known_addition",
        "try_verify_product_from_known_division_candidate",
        "equality_builtin_match_subgoals",
        "collect_nested_equality_transport_steps",
    ];
    let mut explicitly_checked = vec![false; owned_equality_target_apis.len()];
    visit_rust_files(Path::new("src/verification"), &mut |path, source| {
        for function_tail in source.split("fn ").skip(1) {
            let Some((header, _)) = function_tail.split_once('{') else {
                continue;
            };
            let Some((name, _)) = header.split_once('(') else {
                continue;
            };
            let name = name.trim();
            let explicitly_owned = owned_equality_target_apis
                .iter()
                .position(|candidate| *candidate == name);
            if let Some(index) = explicitly_owned {
                explicitly_checked[index] = true;
            }
            let returns_equality_proof_result = (header.contains("-> StmtResult")
                || header.contains("Option<StmtResult>"))
                && !header.contains("Vec<StmtResult>");
            let equality_named_proof_api = (name.contains("equal") || name.contains("equality"))
                && !name.contains("not_equal")
                && !name.contains("less_equal")
                && !name.contains("greater_equal")
                && !name.contains("non_equational")
                && returns_equality_proof_result;
            if !equality_named_proof_api && explicitly_owned.is_none() {
                continue;
            }
            assert!(
                header.contains("&EqualFact"),
                "equality proof API `{name}` in {} must receive the complete EqualFact",
                path.display(),
            );
        }
    });
    for (name, found) in owned_equality_target_apis
        .iter()
        .zip(explicitly_checked.iter())
    {
        assert!(
            *found,
            "owned equality target API `{name}` must remain audited"
        );
    }

    let equality = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/equality/core.rs"
    ));
    let known_fact_impl = equality
        .split("pub fn verify_equal_fact_with_known_fact(")
        .nth(1)
        .expect("known-equality implementation must exist")
        .split("pub fn verify_equal_fact_with_zero_premise_verification(")
        .next()
        .expect("zero-premise verification must follow known equality");
    assert!(known_fact_impl
        .contains("verify_equal_fact_by_known_equality_without_direct_evaluation(equal_fact)"));
    assert!(!known_fact_impl.contains("EqualFact::new"));
    assert!(equality.contains(
            "fn verify_equal_fact_when_both_sides_have_same_builtin_shape_and_equal_args_recursively(\n        &mut self,\n        equal_fact: &EqualFact,"
        ));
    let structural = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/builtin_rules/equality_structural.rs"
    ));
    assert!(structural.contains(
            "pub fn try_verify_equal_fact_as_builtin_premise(\n        &mut self,\n        equal_fact: &EqualFact,"
        ));
    assert!(!structural.contains("pub fn verify_equal_fact_as_builtin_premise("));
    let dispatcher = crate::verification::equality_dispatch_source::SOURCE;
    assert!(dispatcher.contains(
            "pub fn verify_equal_fact_by_builtin_rules(\n        &mut self,\n        equal_fact: &EqualFact,"
        ));
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
