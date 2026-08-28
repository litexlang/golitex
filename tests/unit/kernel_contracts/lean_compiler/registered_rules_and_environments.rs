use super::super::*;
use super::existentials_claims_and_theorems::named_theorem_result_mut;
use super::run_registered_rule_test;

fn execute_typed_power_set_membership() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "have A set = R\nhave B set = C\ntrust A $subset B\nA $in power_set(B)\n",
        "direct_registered_power_set_membership.lit",
    )
    .expect("execute typed power-set membership")
}

fn typed_set_builtin_below_transparent_definitions(
    proof: &SuccessFactProofResult,
) -> &SuccessBuiltinFactProofResult {
    match proof {
        SuccessFactProofResult::BuiltinRule(builtin) => builtin,
        SuccessFactProofResult::Reuse(reuse) => {
            typed_set_builtin_below_transparent_definitions(reuse.source.proof())
        }
        SuccessFactProofResult::Transform(transformation) => {
            assert!(matches!(
                transformation.rule,
                FactTransformationRule::TransparentDefinitionReduction(_)
            ));
            typed_set_builtin_below_transparent_definitions(transformation.source.proof())
        }
        other => panic!("expected typed set proof below transparent definitions: {other:?}"),
    }
}

fn stored_citation_below_set_child_transforms(
    proof: &SuccessFactProofResult,
) -> &SuccessStoredFactCitationProofResult {
    match proof {
        SuccessFactProofResult::StoredFactCitation(citation) => citation,
        SuccessFactProofResult::Reuse(reuse) => {
            stored_citation_below_set_child_transforms(reuse.source.proof())
        }
        SuccessFactProofResult::Transform(transformation) => {
            stored_citation_below_set_child_transforms(transformation.source.proof())
        }
        other => panic!("typed set child must cite an exact source fact: {other:?}"),
    }
}

#[test]
fn typed_set_rule_compiles_directly_from_its_recursive_certificate() {
    run_registered_rule_test(|| {
        let results = execute_typed_power_set_membership();
        let [set_a, set_b, _, result] = results.as_slice() else {
            panic!("expected two set definitions, one trust boundary, and one result")
        };
        let result = result
            .factual_success()
            .expect("typed set rule result is factual");
        let builtin = typed_set_builtin_below_transparent_definitions(result.proof());
        let Some(BuiltinRuleEvidence::Set(rule)) = builtin.evidence.typed() else {
            panic!("expected typed set-rule evidence")
        };
        assert_eq!(*rule, SetBuiltinRule::PowerSetMembershipOfSubset);
        assert_eq!(rule.rule_id(), "set.power_set_membership_of_subset");
        let mut compiler =
            StmtResultToLeanCompiler::new("direct_registered_power_set_membership.lit");
        compiler
            .compile_stmt_result(set_a)
            .expect("compile first set definition");
        compiler
            .compile_stmt_result(set_b)
            .expect("compile second set definition");
        for (index, child) in builtin.subgoals.iter().enumerate() {
            let child = child.factual_success().expect("typed set child is factual");
            let citation = stored_citation_below_set_child_transforms(child.proof());
            let source_fact_id = citation.source_fact_id;
            compiler
                .environment_stack
                .fact_names
                .insert(source_fact_id, format!("__source{index}"));
            compiler
                .environment_stack
                .fact_propositions
                .insert(source_fact_id, citation.source_fact.clone());
        }
        let generated = compiler
            .construct_lean_proof_from_direct_fact_result(result)
            .expect("compile typed set rule directly")
            .expect("typed set rule must have a direct consumer");
        assert!(
            generated.contains("Litex.SetRules.inPowerSetOfSubset"),
            "{generated}"
        );
    });
}

#[test]
fn typed_nonzero_product_and_quotient_rules_fail_closed_at_same_observation_boundary() {
    run_registered_rule_test(|| {
        for (name, operator, rule_id) in [
            ("product", "*", "nonzero.mul"),
            ("quotient", "/", "nonzero.div"),
        ] {
            let file_name = format!("registered_nonzero_{name}.lit");
            let source = format!(
                "forall a, b R:\n    a != 0\n    b != 0\n    =>:\n        a {operator} b != 0\n"
            );
            let results = crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                &source,
                &file_name,
            )
            .unwrap_or_else(|error| panic!("execute typed nonzero {name} rule: {error}"));
            let error = StmtResultToLeanCompiler::new(&file_name)
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("typed nonzero arithmetic must fail closed without Same elimination");
            assert!(error.contains(rule_id), "{error}");
            assert!(
                error.contains("numeric-observation elimination theorem"),
                "{error}"
            );
        }
    });
}

#[test]
fn common_arithmetic_sign_rule_combines_its_child_results_directly() {
    run_registered_rule_test(|| {
        let results =
            crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "have a, b R\ntrust a >= 0\ntrust b >= 0\na + b >= 0\n",
                "direct_arithmetic_sign_rule.lit",
            )
            .expect("execute arithmetic sign rule");
        let [objects, _, _, result] = results.as_slice() else {
            panic!("expected object choice, two premises, and sign result")
        };
        let result = result.factual_success().expect("sign result is factual");
        let (SuccessFactProofResult::BuiltinRule(builtin)
        | SuccessFactProofResult::BuiltinStrategy(builtin)) = result.proof()
        else {
            panic!("expected builtin sign proof")
        };
        assert!(matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::Arithmetic(
                ArithmeticBuiltinRule::AddNonnegative
            ))
        ));
        let mut compiler = StmtResultToLeanCompiler::new("direct_arithmetic_sign_rule.lit");
        compiler
            .compile_stmt_result(objects)
            .expect("compile real object choice");
        for (index, child) in builtin.subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .expect("arithmetic premise is factual");
            let SuccessFactProofResult::StoredFactCitation(citation) = child.proof() else {
                panic!("arithmetic premise must cite an exact source fact")
            };
            let fact_id = citation.source_fact_id;
            compiler
                .environment_stack
                .fact_names
                .insert(fact_id, format!("__sign_source{index}"));
            compiler
                .environment_stack
                .fact_propositions
                .insert(fact_id, citation.source_fact.clone());
        }
        let proof = compiler
            .construct_lean_proof_from_direct_fact_result(result)
            .expect("compile arithmetic sign proof")
            .expect("arithmetic sign proof must not use compatibility IR");
        assert!(
            proof.contains("Litex.Rules.complexAddNonnegative"),
            "{proof}"
        );
    });
}

fn execute_registered_componentwise_order_addition() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "forall a, b, c, d R:\n    a <= b\n    c <= d\n    =>:\n        a + c <= b + d\n",
        "direct_registered_componentwise_order_addition.lit",
    )
    .expect("execute registered componentwise order addition")
}

fn registered_componentwise_order_addition_builtin_mut(
    results: &mut [StmtResult],
) -> &mut SuccessBuiltinFactProofResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results else {
        panic!("expected one forall statement Result")
    };
    let forall_verification = std::rc::Rc::get_mut(&mut forall_result.verification)
        .expect("test owns the forall verification Result");
    let SuccessFactProofResult::ForallProof(forall_proof) = forall_verification.proof_mut() else {
        panic!("expected forall proof Result")
    };
    let [conclusion] = forall_proof.proves.as_mut_slice() else {
        panic!("expected one forall conclusion Result")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(conclusion_result)) =
        conclusion.result.as_mut()
    else {
        panic!("expected factual forall conclusion Result")
    };
    let conclusion_verification = std::rc::Rc::get_mut(&mut conclusion_result.verification)
        .expect("test owns the conclusion verification Result");
    let SuccessFactProofResult::BuiltinRule(builtin) = conclusion_verification.proof_mut() else {
        panic!("expected registered builtin conclusion proof")
    };
    builtin
}

fn registered_single_forall_conclusion_builtin_mut(
    result: &mut StmtResult,
) -> &mut SuccessBuiltinFactProofResult {
    let StmtResult::Success(SuccessStmtResult::Fact(forall_result)) = result else {
        panic!("expected one forall statement Result")
    };
    let forall_verification = std::rc::Rc::get_mut(&mut forall_result.verification)
        .expect("test owns the forall verification Result");
    let SuccessFactProofResult::ForallProof(forall_proof) = forall_verification.proof_mut() else {
        panic!("expected forall proof Result")
    };
    let [conclusion] = forall_proof.proves.as_mut_slice() else {
        panic!("expected one forall conclusion Result")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(conclusion_result)) =
        conclusion.result.as_mut()
    else {
        panic!("expected factual forall conclusion Result")
    };
    let conclusion_verification = std::rc::Rc::get_mut(&mut conclusion_result.verification)
        .expect("test owns the conclusion verification Result");
    let SuccessFactProofResult::BuiltinRule(builtin) = conclusion_verification.proof_mut() else {
        panic!("expected registered builtin conclusion proof")
    };
    builtin
}

#[test]
fn registered_componentwise_order_addition_compiles_directly_from_result_children() {
    run_registered_rule_test(|| {
        let results = execute_registered_componentwise_order_addition();
        let generated =
            StmtResultToLeanCompiler::new("direct_registered_componentwise_order_addition.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile registered componentwise order addition directly");
        assert!(
            generated.contains("Litex.Rules.complexAddPreservesLessEqualComponentwise")
                && generated.contains("convert __domain1 using 1")
                && generated.contains("convert __domain2 using 1"),
            "{generated}"
        );
    });
}

#[test]
fn registered_componentwise_order_addition_rejects_swapped_semantic_children() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_componentwise_order_addition();
        let builtin = registered_componentwise_order_addition_builtin_mut(&mut results);
        assert_eq!(builtin.subgoals.len(), 2);
        builtin.subgoals.swap(0, 1);

        let error =
            StmtResultToLeanCompiler::new("direct_registered_componentwise_order_addition.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("swapped registered semantic premises must fail closed");
        assert!(
            error.contains("componentwise additive order premise 0 changed"),
            "{error}"
        );
    });
}

fn execute_registered_subtraction_sign_and_greater_to_greater_equal_rules() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "forall u, v R:\n    v <= u\n    =>:\n        0 <= u - v\n\nforall u, v R:\n    v < u\n    =>:\n        0 < u - v\n\nforall a, b R:\n    a > b\n    =>:\n        a >= b\n",
            "direct_registered_subtraction_sign_and_order.lit",
        )
        .expect("execute registered subtraction-sign and strict-to-weak order rules")
}

#[test]
fn registered_subtraction_sign_and_greater_to_greater_equal_compile_directly() {
    run_registered_rule_test(|| {
        let results = execute_registered_subtraction_sign_and_greater_to_greater_equal_rules();
        let generated =
            StmtResultToLeanCompiler::new("direct_registered_subtraction_sign_and_order.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile registered subtraction-sign and strict-to-weak order directly");
        assert!(
            generated.contains("Litex.Rules.complexSubNonnegativeOfLessEqual"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Rules.complexSubPositiveOfLess"),
            "{generated}"
        );
        assert!(generated.contains("Litex.Lt.toLe"), "{generated}");
        assert!(
            generated.contains("convert __domain1 using 1"),
            "{generated}"
        );
    });
}

#[test]
fn typed_subtraction_sign_evidence_replays_the_exact_real_adapter() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_subtraction_sign_and_greater_to_greater_equal_rules();
        for (result, rule) in results[..2].iter_mut().zip([
            ArithmeticBuiltinRule::SubNonnegativeFromLessEqual,
            ArithmeticBuiltinRule::SubPositiveFromLess,
        ]) {
            let builtin = registered_single_forall_conclusion_builtin_mut(result);
            assert_eq!(builtin.subgoals.len(), 1);
            assert!(matches!(
                builtin.evidence.typed(),
                Some(BuiltinRuleEvidence::Arithmetic(actual)) if *actual == rule
            ));
        }
        let generated = StmtResultToLeanCompiler::new("typed_subtraction_sign.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile typed subtraction-sign evidence");
        assert!(
            generated.contains("Litex.Rules.complexSubNonnegativeOfLessEqual"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Rules.complexSubPositiveOfLess"),
            "{generated}"
        );
    });
}

#[test]
fn typed_right_nonnegative_order_evidence_replays_exact_real_adapters() {
    run_registered_rule_test(|| {
        let mut results =
            crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "forall a, b R:\n    0 <= b\n    =>:\n        a <= a + b\n\nforall a, b, c R:\n    a <= b\n    0 <= c\n    =>:\n        a - c <= b\n",
                "legacy_typed_right_nonnegative_order.lit",
            )
            .expect("execute registered right-nonnegative order rules");
        for (result, rule) in results.iter_mut().zip([
            ArithmeticBuiltinRule::AddRightNonnegativeLessEqual,
            ArithmeticBuiltinRule::SubRightNonnegativeLessEqual,
        ]) {
            let builtin = registered_single_forall_conclusion_builtin_mut(result);
            assert!(!builtin.subgoals.is_empty());
            assert!(matches!(
                builtin.evidence.typed(),
                Some(BuiltinRuleEvidence::Arithmetic(actual)) if *actual == rule
            ));
        }
        let generated = StmtResultToLeanCompiler::new("typed_right_nonnegative_order.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile typed right-nonnegative order evidence");
        assert!(
            generated.contains("Litex.Rules.realCastLeAddOfNonnegativeRight"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Rules.realCastSubLeOfLeOfNonnegative"),
            "{generated}"
        );
        assert!(
            !generated.contains("Litex.OrderBridge.leOfReal (by positivity)"),
            "the right-nonnegative rule must replay its retained semantic premise: {generated}"
        );
    });
}

#[test]
fn typed_subtraction_sign_rejects_a_missing_semantic_child() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_subtraction_sign_and_greater_to_greater_equal_rules();
        let builtin = registered_single_forall_conclusion_builtin_mut(&mut results[0]);
        assert_eq!(builtin.subgoals.len(), 1);
        builtin.subgoals.clear();

        let error =
            StmtResultToLeanCompiler::new("direct_registered_subtraction_sign_and_order.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("missing typed subtraction-sign premise must fail closed");
        assert!(error.contains("changed its ordered child arity"), "{error}");
    });
}

fn execute_order_transitivity() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "forall a, b, c R:\n    a <= b\n    b < c\n    =>:\n        a < c\n",
        "direct_order_transitivity.lit",
    )
    .expect("execute mixed order transitivity")
}

fn order_transitivity_builtin_mut(
    results: &mut [StmtResult],
) -> &mut SuccessBuiltinFactProofResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results else {
        panic!("expected one forall Result")
    };
    let verification = std::rc::Rc::get_mut(&mut forall_result.verification)
        .expect("test owns forall verification");
    let SuccessFactProofResult::ForallProof(forall) = verification.proof_mut() else {
        panic!("expected forall proof")
    };
    let [conclusion] = forall.proves.as_mut_slice() else {
        panic!("expected one conclusion")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(conclusion)) = conclusion.result.as_mut()
    else {
        panic!("expected factual conclusion")
    };
    let verification = std::rc::Rc::get_mut(&mut conclusion.verification)
        .expect("test owns conclusion verification");
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
        panic!("expected builtin transitivity proof")
    };
    assert!(matches!(
        builtin.evidence.typed(),
        Some(BuiltinRuleEvidence::Arithmetic(
            ArithmeticBuiltinRule::OrderTransitivity
        ))
    ));
    builtin
}

#[test]
fn order_transitivity_fails_closed_without_a_reviewed_mapping() {
    run_registered_rule_test(|| {
        let mut results = execute_order_transitivity();
        order_transitivity_builtin_mut(&mut results);
        let error = StmtResultToLeanCompiler::new("direct_order_transitivity.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("non-catalog order transitivity must fail closed");
        assert!(error.contains("order.transitivity"), "{error}");
    });
}

#[test]
fn order_transitivity_retains_two_ordered_semantic_children() {
    run_registered_rule_test(|| {
        let mut results = execute_order_transitivity();
        let builtin = order_transitivity_builtin_mut(&mut results);
        let child_count = builtin.subgoals.len();
        assert!(child_count >= 2);
        let semantic = &builtin.subgoals[child_count - 2..];
        assert_eq!(
            semantic[0].factual_success().unwrap().fact().to_string(),
            "#0#a <= #1#b"
        );
        assert_eq!(
            semantic[1].factual_success().unwrap().fact().to_string(),
            "#1#b < #2#c"
        );
    });
}

fn execute_strategy_definition_with_local_proof_environment() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "prop reflexive(x R):\n    x = x\n\nstrategy prove_reflexive:\n    ? forall x R:\n        $reflexive(x)\n    x = x\n    by def $reflexive(x)\n",
            "direct_strategy_definition_compiler_environment.lit",
        )
        .expect("execute a verified strategy with one local parameter scope")
}

#[test]
fn strategy_definition_compiles_from_recursive_well_definedness_and_local_proof_scope() {
    run_registered_rule_test(|| {
        let results = execute_strategy_definition_with_local_proof_environment();
        let [_, StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::DefStrategyStmt(strategy),
        ))] = results.as_slice()
        else {
            panic!("expected predicate and strategy Results")
        };
        let verification = strategy
            .verification
            .as_ref()
            .expect("verified strategy must retain its verification Result");
        assert!(matches!(
            verification.well_definedness.recursive.as_deref(),
            Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(_))
        ));
        assert_eq!(
            verification
                .proof_scope
                .assumption_infers
                .store_fact_outputs
                .len(),
            1
        );
        assert_eq!(verification.proof_steps.len(), 2);
        assert_eq!(verification.conclusion_checks.len(), 1);

        let generated =
            StmtResultToLeanCompiler::new("direct_strategy_definition_compiler_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile strategy Result through a child compiler environment");
        assert!(generated.contains("theorem prove_reflexive"), "{generated}");
        assert!(
            generated.contains("intro __carrier0_1 x __h"),
            "{generated}"
        );
        assert!(
            generated.contains("have __step2 : reflexive (Litex.In.rep x __h"),
            "{generated}"
        );
        assert!(generated.contains("Litex.In.own Litex.R"), "{generated}");
    });
}

#[test]
fn strategy_definition_rejects_a_result_missing_its_local_parameter_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_strategy_definition_with_local_proof_environment();
        let [_, StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::DefStrategyStmt(strategy),
        ))] = results.as_mut_slice()
        else {
            panic!("expected predicate and strategy Results")
        };
        strategy
            .verification
            .as_mut()
            .expect("verified strategy")
            .proof_scope
            .assumption_infers
            .store_fact_outputs
            .clear();

        let error =
            StmtResultToLeanCompiler::new("direct_strategy_definition_compiler_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("a missing local parameter FactId must fail closed");
        assert!(
            error.contains("named forall proof-scope assumptions stored 0 facts"),
            "{error}"
        );
    });
}

fn execute_order_reflexivity_theorem() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "thm local_weak_order_reflexivity:\n    ? forall x R:\n        x <= x\n",
        "direct_order_reflexivity_compiler_environment.lit",
    )
    .expect("execute symbolic weak-order reflexivity")
}

fn order_reflexivity_evidence_mut(
    results: &mut [StmtResult],
) -> &mut OrderReflexivityBuiltinRuleEvidence {
    let theorem = named_theorem_result_mut(results);
    let conclusion = theorem
        .verification
        .as_mut()
        .expect("named theorem retains verification")
        .conclusion_checks
        .first_mut()
        .expect("named theorem retains one conclusion")
        .factual_success_mut()
        .expect("named theorem conclusion is factual");
    let verification = std::rc::Rc::get_mut(&mut conclusion.verification)
        .expect("test owns the conclusion verification Result");
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
        panic!("expected builtin order-reflexivity proof")
    };
    let Some(BuiltinRuleEvidence::OrderReflexivity(evidence)) = builtin.evidence.typed_mut() else {
        panic!("expected typed order-reflexivity evidence")
    };
    evidence
}

#[test]
fn symbolic_order_reflexivity_compiles_inside_the_result_owned_binder_environment() {
    run_registered_rule_test(|| {
        let mut results = execute_order_reflexivity_theorem();
        order_reflexivity_evidence_mut(&mut results);

        let generated =
            StmtResultToLeanCompiler::new("direct_order_reflexivity_compiler_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile symbolic reflexivity from its typed Result evidence");
        assert!(
            generated.contains("intro __carrier0_1 x __h"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Le.refl (((Litex.In.rep x __h"),
            "{generated}"
        );
    });
}

#[test]
fn symbolic_order_reflexivity_rejects_a_retargeted_repeated_object() {
    run_registered_rule_test(|| {
        let mut results = execute_order_reflexivity_theorem();
        order_reflexivity_evidence_mut(&mut results).repeated_object =
            Number::new("1".to_string()).into();

        let error =
            StmtResultToLeanCompiler::new("direct_order_reflexivity_compiler_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("retargeted order-reflexivity evidence must fail closed");
        assert!(
            error.contains("order-reflexivity evidence changed its repeated object"),
            "{error}"
        );
    });
}

fn closed_numeric_comparison_evidence_mut(
    results: &mut [StmtResult],
) -> &mut ClosedNumericComparisonBuiltinRuleEvidence {
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results else {
        panic!("expected one successful factual Result")
    };
    let verification = std::rc::Rc::get_mut(&mut result.verification)
        .expect("test owns the factual verification Result");
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
        panic!("expected builtin closed-comparison proof")
    };
    let Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) = builtin.evidence.typed_mut()
    else {
        panic!("expected typed closed numeric comparison evidence")
    };
    evidence
}

#[test]
fn closed_numeric_comparison_retains_both_recursive_evaluations() {
    run_registered_rule_test(|| {
        let mut results =
            crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "2 + 3 < 6\n",
                "direct_closed_numeric_comparison_result.lit",
            )
            .expect("execute a closed numeric comparison");
        let evidence = closed_numeric_comparison_evidence_mut(&mut results);
        assert_eq!(evidence.left_evaluation.expression.to_string(), "2 + 3");
        assert_eq!(evidence.left_evaluation.value.normalized_value, "5");
        assert_eq!(evidence.right_evaluation.value.normalized_value, "6");

        let generated =
            StmtResultToLeanCompiler::new("direct_closed_numeric_comparison_result.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile a closed comparison from retained evaluations");
        assert!(generated.contains("Litex.OrderBridge.ltOfComplexReals"));
    });
}

#[test]
fn closed_numeric_comparison_rejects_a_corrupted_normal_form() {
    run_registered_rule_test(|| {
        let mut results =
            crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "2 + 3 < 6\n",
                "direct_closed_numeric_comparison_result.lit",
            )
            .expect("execute a closed numeric comparison");
        closed_numeric_comparison_evidence_mut(&mut results)
            .left_evaluation
            .value = Number::new("4".to_string());

        let error = StmtResultToLeanCompiler::new("direct_closed_numeric_comparison_result.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("corrupted numeric comparison evidence must fail closed");
        assert!(
            error.contains("closed numeric evaluation changed its expression or value"),
            "{error}"
        );
    });
}

fn execute_registered_reflexive_predicate_and_use() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "prop rel(x set, y set):\n    x = y\n\nby reflexive_prop:\n    ? forall x set:\n        $rel(x, x)\n    x = x\n    by def $rel(x, x)\n\n$rel(R, R)\n",
            "direct_registered_reflexive_predicate_environment.lit",
        )
        .expect("execute a registered user-predicate reflexivity theorem and one use")
}

fn registered_reflexive_predicate_evidence_mut(
    results: &mut [StmtResult],
) -> &mut RegisteredReflexivePredicateBuiltinRuleEvidence {
    let Some(StmtResult::Success(SuccessStmtResult::Fact(result))) = results.last_mut() else {
        panic!("expected a final factual Result")
    };
    let target = result.fact();
    result.store.infers.rule_applications.clear();
    for output in &mut result.store.infers.store_fact_outputs {
        output.inferred_facts.clear();
        output.inferred_fact_ids.clear();
    }
    let verification = std::rc::Rc::get_mut(&mut result.verification)
        .expect("test owns the final verification Result");
    *verification.proof_mut() =
        SuccessFactProofResult::BuiltinRule(SuccessBuiltinFactProofResult {
            msg: "registered reflexive predicate".to_string(),
            evidence: SuccessBuiltinFactProofEvidenceResult::Typed(
                BuiltinRuleEvidence::RegisteredReflexivePredicate(
                    RegisteredReflexivePredicateBuiltinRuleEvidence::new(target, "rel".to_string()),
                ),
            ),
            subgoals: Vec::new(),
        });
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
        unreachable!("test just installed a builtin proof")
    };
    let Some(BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence)) =
        builtin.evidence.typed_mut()
    else {
        panic!("expected typed registered-reflexivity evidence")
    };
    evidence
}

fn execute_all_registered_predicate_property_results() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/lean/examples/46_RegisteredPredicateCompilerEnvironment.lit"
        )),
        "46_RegisteredPredicateCompilerEnvironment.lit",
    )
    .expect("execute all four registered predicate-property Results")
}

#[test]
fn all_predicate_property_registrations_compile_in_result_owned_forall_environments() {
    run_registered_rule_test(|| {
        let results = execute_all_registered_predicate_property_results();
        let generated =
            StmtResultToLeanCompiler::new("46_RegisteredPredicateCompilerEnvironment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile all predicate-property registration environments");
        assert!(
            generated.contains("theorem __litex_registered_reflexive_same_set_"),
            "{generated}"
        );
        assert!(
            generated.contains("theorem __litex_registered_symmetric_same_set_"),
            "{generated}"
        );
        assert!(
            generated.contains("theorem __litex_registered_transitive_same_set_"),
            "{generated}"
        );
        assert!(
            generated.contains("theorem __litex_registered_antisymmetric_same_set_"),
            "{generated}"
        );
        assert!(
            generated.contains("(__domain1 : same_set x y)"),
            "{generated}"
        );
        assert!(
            generated.contains("(__domain2 : same_set y z)"),
            "{generated}"
        );
        assert!(
            generated.contains("have __definition := __domain1"),
            "{generated}"
        );
    });
}

fn execute_registered_transitive_predicate_chain_and_use() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "prop same_set(x set, y set):\n    x = y\n\nby transitive_prop:\n    ? forall x, y, z set:\n        $same_set(x, y)\n        $same_set(y, z)\n        =>:\n            $same_set(x, z)\n    x = y\n    y = z\n    x = z\n    by def $same_set(x, z)\n\ntrust R $same_set C\ntrust C $same_set N\nR $same_set C $same_set N\nR $same_set N\n",
            "direct_registered_transitive_predicate_environment.lit",
        )
        .expect("execute a registered transitive predicate chain and later citation")
}

fn registered_transitive_chain_rule_mut(
    results: &mut [StmtResult],
) -> &mut RegisteredTransitivePredicateChainClosureInferRule {
    let Some(StmtResult::Success(SuccessStmtResult::Fact(chain_result))) =
        results.get_mut(results.len().saturating_sub(2))
    else {
        panic!("expected the penultimate Result to be the source chain")
    };
    chain_result
        .store
        .infers
        .rule_applications
        .iter_mut()
        .find_map(|application| {
            let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &mut application.rule
            else {
                return None;
            };
            Some(rule)
        })
        .expect("three-object chain should retain typed registered transitivity")
}

fn first_trusted_defined_predicate_clause_rule_mut(
    results: &mut [StmtResult],
) -> &mut DefinedPredicateDefinitionClauseProjectionInferRule {
    results
        .iter_mut()
        .find_map(|result| {
            let StmtResult::Success(SuccessStmtResult::UnsafeStmt(
                SuccessUnsafeStmtResult::TrustStmt(trust),
            )) = result
            else {
                return None;
            };
            trust
                .common
                .infers
                .rule_applications
                .iter_mut()
                .find_map(|application| {
                    let InferRule::DefinedPredicateDefinitionClauseProjection(rule) =
                        &mut application.rule
                    else {
                        return None;
                    };
                    Some(rule)
                })
        })
        .expect("trusted predicate application must retain a definition-clause projection")
}

#[test]
fn registered_transitive_predicate_chain_compiles_through_the_current_environment_stack() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_transitive_predicate_chain_and_use();
        registered_transitive_chain_rule_mut(&mut results);

        let generated =
            StmtResultToLeanCompiler::new("direct_registered_transitive_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile registered transitive closure from its recursive Result");
        assert!(
            generated.contains("theorem __litex_registered_transitive_same_set_"),
            "{generated}"
        );
        assert!(
            generated
                .matches("__litex_registered_transitive_same_set_")
                .count()
                >= 2,
            "{generated}"
        );
        assert!(
            generated.contains("(__fact") && generated.contains(".1)"),
            "the chain premise FactIds should be backed by source-theorem projections: {generated}"
        );
    });
}

#[test]
fn registered_transitive_predicate_chain_rejects_a_changed_object_interval() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_transitive_predicate_chain_and_use();
        registered_transitive_chain_rule_mut(&mut results).end_object_index = 1;

        let error =
            StmtResultToLeanCompiler::new("direct_registered_transitive_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("corrupted transitive-chain interval must fail closed");
        assert!(
            error.contains("changed its predicate or object interval"),
            "{error}"
        );
    });
}

#[test]
fn defined_predicate_inference_rejects_a_changed_definition_clause_index() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_transitive_predicate_chain_and_use();
        first_trusted_defined_predicate_clause_rule_mut(&mut results).clause_index = 1;

        let error =
            StmtResultToLeanCompiler::new("direct_registered_transitive_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("retargeted predicate definition clause must fail closed");
        assert!(
            error.contains("defined-predicate inference selected component")
                || error.contains("clause projection left the definition clause range"),
            "{error}"
        );
    });
}

#[test]
fn predicate_property_registration_rejects_a_missing_local_domain_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_all_registered_predicate_property_results();
        let Some(StmtResult::Success(SuccessStmtResult::By(
            SuccessByStmtResult::BySymmetricPropStmt(result),
        ))) = results.get_mut(2)
        else {
            panic!("expected the symmetric registration Result")
        };
        let verification = result
            .verification
            .as_mut()
            .expect("symmetric registration retains verification");
        verification.assumption_infers.store_fact_outputs[2].fact_id = None;
        let forall_check = verification
            .forall_check
            .factual_success_mut()
            .expect("registration forall check is factual");
        let forall_verification = std::rc::Rc::get_mut(&mut forall_check.verification)
            .expect("test owns the nested forall verification Result");
        let SuccessFactProofResult::ForallProof(forall_proof) = forall_verification.proof_mut()
        else {
            panic!("registration retains its verify_forall_fact layer")
        };
        forall_proof.assumption_infers.store_fact_outputs[2].fact_id = None;

        let error = StmtResultToLeanCompiler::new("46_RegisteredPredicateCompilerEnvironment.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("a missing binder-local domain FactId must fail closed");
        assert!(
            error.contains("named forall proof-scope assumptions store 2")
                && error.contains("has no FactId"),
            "{error}"
        );
    });
}

#[test]
fn predicate_property_registration_pushes_its_forall_environment_and_publishes_a_compiler_binding()
{
    run_registered_rule_test(|| {
        let mut results = execute_registered_reflexive_predicate_and_use();
        registered_reflexive_predicate_evidence_mut(&mut results);

        let generated =
            StmtResultToLeanCompiler::new("direct_registered_reflexive_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile a registered predicate theorem and its exact later use");
        assert!(
            generated.contains("theorem __litex_registered_reflexive_rel_"),
            "{generated}"
        );
        assert!(
            generated
                .matches("__litex_registered_reflexive_rel_")
                .count()
                >= 2
                && generated.contains(" Litex.R"),
            "{generated}"
        );
    });
}

#[test]
fn registered_reflexive_predicate_use_rejects_a_changed_predicate_name() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_reflexive_predicate_and_use();
        registered_reflexive_predicate_evidence_mut(&mut results).predicate_name =
            "another_relation".to_string();

        let error =
            StmtResultToLeanCompiler::new("direct_registered_reflexive_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("changed registered predicate evidence must fail closed");
        assert!(
            error
                .contains("registered reflexive-predicate evidence changed its predicate or arity"),
            "{error}"
        );
    });
}

fn clear_embedded_property_rule_child_effects(result: &mut StmtResult) {
    let result = result
        .factual_success_mut()
        .expect("embedded property-rule child is factual");
    result.store.fact_id = None;
    result.store.infers = SuccessInferResult::new();
}

fn replace_embedded_property_rule_child_with_exact_fact_citation(
    result: &mut StmtResult,
    source_fact_id: FactId,
) {
    let result = result
        .factual_success_mut()
        .expect("embedded property-rule child is factual");
    let fact = result.fact();
    let verification = std::rc::Rc::get_mut(&mut result.verification)
        .expect("test owns the embedded child verification Result");
    *verification.proof_mut() =
        SuccessFactProofResult::stored_fact_citation(fact, source_fact_id, None);
}

fn exact_visible_stored_fact_id(results: &[StmtResult], fact: &Fact) -> Option<FactId> {
    for result in results.iter().rev() {
        if let Some(factual) = result.factual_success() {
            if factual.fact().to_string() == fact.to_string() {
                if let Some(fact_id) = factual.store.fact_id {
                    return Some(fact_id);
                }
            }
        }
        if let Some(non_factual) = result.non_factual_success() {
            if let Some(common) = non_factual.common() {
                for output in common.infers.store_fact_outputs.iter().rev() {
                    if output.itself_and_why_itself_is_stored.0.to_string() == fact.to_string() {
                        if let Some(fact_id) = output.fact_id {
                            return Some(fact_id);
                        }
                    }
                }
            }
        }
    }
    None
}

fn clear_visible_property_source_inferred_children(results: &mut [StmtResult], fact: &Fact) {
    for result in results {
        let Some(non_factual) = result.non_factual_success_mut() else {
            continue;
        };
        let Some(common) = non_factual.common_mut() else {
            continue;
        };
        common.infers.rule_applications.clear();
        for output in &mut common.infers.store_fact_outputs {
            if output.itself_and_why_itself_is_stored.0.to_string() == fact.to_string() {
                output.inferred_facts.clear();
                output.inferred_fact_ids.clear();
            }
        }
    }
}

fn install_registered_symmetric_predicate_proof(
    results: &mut Vec<StmtResult>,
) -> &mut RegisteredSymmetricPredicateBuiltinRuleEvidence {
    let child_index = results
        .len()
        .checked_sub(2)
        .expect("symmetric fixture retains a child and target");
    let mut alternate_result = results.remove(child_index);
    clear_embedded_property_rule_child_effects(&mut alternate_result);
    let alternate = alternate_result
        .factual_success()
        .expect("symmetric fixture alternate is factual")
        .fact();
    clear_visible_property_source_inferred_children(results, &alternate);
    let source_fact_id = exact_visible_stored_fact_id(results, &alternate)
        .expect("symmetric fixture retains the exact visible alternate FactId");
    replace_embedded_property_rule_child_with_exact_fact_citation(
        &mut alternate_result,
        source_fact_id,
    );
    let Some(StmtResult::Success(SuccessStmtResult::Fact(target_result))) = results.last_mut()
    else {
        panic!("symmetric fixture target is factual")
    };
    let target = target_result.fact();
    target_result.store.infers.rule_applications.clear();
    for output in &mut target_result.store.infers.store_fact_outputs {
        output.inferred_facts.clear();
        output.inferred_fact_ids.clear();
    }
    let verification = std::rc::Rc::get_mut(&mut target_result.verification)
        .expect("test owns the symmetric target verification Result");
    *verification.proof_mut() =
        SuccessFactProofResult::BuiltinRule(SuccessBuiltinFactProofResult {
            msg: "registered symmetric predicate".to_string(),
            evidence: SuccessBuiltinFactProofEvidenceResult::Typed(
                BuiltinRuleEvidence::RegisteredSymmetricPredicate(
                    RegisteredSymmetricPredicateBuiltinRuleEvidence::new(
                        target,
                        "any_set".to_string(),
                        vec![1, 0],
                        alternate,
                    ),
                ),
            ),
            subgoals: vec![alternate_result],
        });
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
        unreachable!("test just installed a builtin proof")
    };
    let Some(BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence)) =
        builtin.evidence.typed_mut()
    else {
        unreachable!("test just installed symmetric evidence")
    };
    evidence
}

fn execute_registered_symmetric_predicate_and_use() -> Vec<StmtResult> {
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "prop any_set(x set, y set):\n    x = x\n\nby symmetric_prop:\n    ? forall x, y set:\n        $any_set(x, y)\n        =>:\n            $any_set(y, x)\n    x = x\n    by def $any_set(y, x)\n\ntrust $any_set(R, C)\n$any_set(R, C)\n$any_set(C, R)\n",
            "direct_registered_symmetric_predicate_environment.lit",
        )
        .expect("execute a registered user-predicate symmetry theorem and reordered facts")
}

#[test]
fn registered_symmetric_predicate_use_compiles_its_exact_child_in_the_visible_environment() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_symmetric_predicate_and_use();
        install_registered_symmetric_predicate_proof(&mut results);

        let mut focused_compiler =
            StmtResultToLeanCompiler::new("direct_registered_symmetric_predicate_environment.lit");
        for prefix in &results[..results.len() - 1] {
            focused_compiler
                .compile_stmt_result(prefix)
                .expect("compile the environment preceding the symmetry use");
        }
        let target = results
            .last()
            .and_then(StmtResult::factual_success)
            .expect("symmetric fixture target is factual");
        assert!(
            focused_compiler
                .construct_lean_proof_from_direct_fact_result(target)
                .expect("construct the focused registered-symmetry proof")
                .is_some(),
            "registered symmetry should be a direct proof route"
        );

        let generated =
            StmtResultToLeanCompiler::new("direct_registered_symmetric_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile registered symmetry from its exact child Result");
        assert!(
            generated.contains("theorem __litex_registered_symmetric_any_set_"),
            "{generated}"
        );
        assert!(
            generated
                .matches("__litex_registered_symmetric_any_set_")
                .count()
                >= 2,
            "{generated}"
        );
    });
}

#[test]
fn registered_symmetric_predicate_use_rejects_a_corrupted_permutation() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_symmetric_predicate_and_use();
        install_registered_symmetric_predicate_proof(&mut results).gather = vec![0, 1];

        let error =
            StmtResultToLeanCompiler::new("direct_registered_symmetric_predicate_environment.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("a changed symmetry permutation must fail closed");
        assert!(
            error.contains("changed its reordered premise")
                || error.contains("invalid permutation"),
            "{error}"
        );
    });
}

fn install_registered_antisymmetric_predicate_proof(
    results: &mut Vec<StmtResult>,
) -> &mut RegisteredAntisymmetricPredicateBuiltinRuleEvidence {
    let child_index = results
        .len()
        .checked_sub(2)
        .expect("antisymmetric fixture retains children and target");
    let mut second_premise = results.remove(child_index);
    let child_index = results
        .len()
        .checked_sub(2)
        .expect("antisymmetric fixture retains its first child and target");
    let mut first_premise = results.remove(child_index);
    let premise_fact = first_premise
        .factual_success()
        .expect("antisymmetric fixture premise is factual")
        .fact();
    clear_visible_property_source_inferred_children(results, &premise_fact);
    let source_fact_id = exact_visible_stored_fact_id(results, &premise_fact)
        .expect("antisymmetric fixture retains the exact visible premise FactId");
    replace_embedded_property_rule_child_with_exact_fact_citation(
        &mut first_premise,
        source_fact_id,
    );
    replace_embedded_property_rule_child_with_exact_fact_citation(
        &mut second_premise,
        source_fact_id,
    );
    clear_embedded_property_rule_child_effects(&mut first_premise);
    clear_embedded_property_rule_child_effects(&mut second_premise);
    let Some(StmtResult::Success(SuccessStmtResult::Fact(target_result))) = results.last_mut()
    else {
        panic!("antisymmetric fixture target is factual")
    };
    let target = target_result.fact();
    target_result.store.infers.rule_applications.clear();
    for output in &mut target_result.store.infers.store_fact_outputs {
        output.inferred_facts.clear();
        output.inferred_fact_ids.clear();
    }
    let verification = std::rc::Rc::get_mut(&mut target_result.verification)
        .expect("test owns the antisymmetric target verification Result");
    *verification.proof_mut() =
        SuccessFactProofResult::BuiltinRule(SuccessBuiltinFactProofResult {
            msg: "registered antisymmetric predicate".to_string(),
            evidence: SuccessBuiltinFactProofEvidenceResult::Typed(
                BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(
                    RegisteredAntisymmetricPredicateBuiltinRuleEvidence::new(
                        target,
                        "same_set".to_string(),
                    ),
                ),
            ),
            subgoals: vec![first_premise, second_premise],
        });
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
        unreachable!("test just installed a builtin proof")
    };
    let Some(BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence)) =
        builtin.evidence.typed_mut()
    else {
        unreachable!("test just installed antisymmetric evidence")
    };
    evidence
}

fn execute_registered_antisymmetric_predicate_and_use() -> Vec<StmtResult> {
    let source = format!(
        "{}\nR = R\ntrust $same_set(R, R)\n$same_set(R, R)\n$same_set(R, R)\nR = R\n",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/lean/examples/46_RegisteredPredicateCompilerEnvironment.lit"
        ))
    );
    crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        &source,
        "direct_registered_antisymmetric_predicate_environment.lit",
    )
    .expect("execute a registered user-predicate antisymmetry theorem and its premises")
}

#[test]
fn registered_antisymmetric_predicate_use_combines_its_two_exact_children() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_antisymmetric_predicate_and_use();
        install_registered_antisymmetric_predicate_proof(&mut results);

        let generated = StmtResultToLeanCompiler::new(
            "direct_registered_antisymmetric_predicate_environment.lit",
        )
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile registered antisymmetry from its two exact child Results");
        assert!(
            generated.contains("theorem __litex_registered_antisymmetric_same_set_"),
            "{generated}"
        );
        assert!(
            generated
                .matches("__litex_registered_antisymmetric_same_set_")
                .count()
                >= 2,
            "{generated}"
        );
    });
}

#[test]
fn setting_definition_is_a_pass_through_before_its_elaborated_forall_result() {
    run_registered_rule_test(|| {
        let results =
            crate::lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "setting RealElement(x R)\n\nforall [RealElement]:\n    x = x\n",
                "direct_setting_elaboration_result.lit",
            )
            .expect("execute one setting and one elaborated forall");
        let [StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::DefSettingStmt(setting),
        )), StmtResult::Success(SuccessStmtResult::Fact(_))] = results.as_slice()
        else {
            panic!("expected setting Result followed by its elaborated forall Result")
        };
        assert!(setting.common.infers.is_empty());

        let generated = StmtResultToLeanCompiler::new("direct_setting_elaboration_result.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile the setting as pass-through and the forall directly");
        assert!(!generated.contains("def RealElement"), "{generated}");
        assert!(generated.contains("Litex.Same.refl x"), "{generated}");
    });
}
