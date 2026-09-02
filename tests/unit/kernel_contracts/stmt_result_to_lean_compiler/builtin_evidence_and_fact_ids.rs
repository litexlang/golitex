use super::super::*;
use super::run_registered_rule_test;

#[test]
fn direct_compiler_rejects_a_conjunction_component_result_with_changed_position() {
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "1 = 1 and 2 = 2",
            "corrupted_conjunction_component_result.lit",
        )
        .expect("execute conjunction before corrupting its Result");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_mut_slice() else {
        panic!("expected one successful conjunction Result")
    };
    let InferRule::ConjunctionImpliesComponent(rule) =
        &mut result.store.infers.rule_applications[0].rule
    else {
        panic!("expected typed conjunction-component inference")
    };
    rule.component_index = 1;

    let error = StmtResultToLeanCompiler::new("corrupted_conjunction_component_result.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed component position must fail closed");
    assert!(error.contains("structural position"), "{error}");
}

#[test]
fn finite_enumeration_rejects_a_corrupted_assignment_fact_id() {
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "by enumerate finite_set:\n    ? forall x {1, 2}:\n        x = 1 or x = 2\n",
            "corrupted_finite_enumeration_assignment.lit",
        )
        .expect("execute finite enumeration before corrupting its Result");
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByEnumerateFiniteSetStmt(
        result,
    )))] = results.as_mut_slice()
    else {
        panic!("expected one successful finite enumeration Result")
    };
    let verification = result
        .verification
        .as_mut()
        .expect("verified enumeration has assignment children");
    verification.assignments[0].assumptions[0].fact_id = FactId::new(u64::MAX - 7);

    let error = StmtResultToLeanCompiler::new("corrupted_finite_enumeration_assignment.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed assignment FactId must fail closed");
    assert!(error.contains("assumption FactId"), "{error}");
}

#[test]
fn finite_enumeration_introduces_the_implicit_host_carrier_before_the_value() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "by enumerate finite_set:\n    ? forall x {1, 2}:\n        x = 1 or x = 2\n",
            "finite_enumeration_implicit_carrier.lit",
        )
        .expect("execute finite enumeration");
    let generated = StmtResultToLeanCompiler::new("finite_enumeration_implicit_carrier.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile finite enumeration");

    assert!(
        generated.contains("intro __carrier1 x __type1"),
        "{generated}"
    );
}

#[test]
fn integer_range_iteration_rejects_a_corrupted_evaluated_value() {
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "by for:\n    ? forall n range(0, 3):\n        n < 3\n",
            "corrupted_integer_range_iteration.lit",
        )
        .expect("execute range iteration before corrupting its Result");
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByForStmt(result)))] =
        results.as_mut_slice()
    else {
        panic!("expected one successful by-for Result")
    };
    let Some(SuccessVerifyByForResult::Ranges(verification)) = result.verification.as_mut() else {
        panic!("expected the exact range verification Result")
    };
    verification.parameters[0].enumerated_values[1] = "7".into();

    let error = StmtResultToLeanCompiler::new("corrupted_integer_range_iteration.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed evaluated value must fail closed");
    assert!(error.contains("ordered evaluated values"), "{error}");
}

#[test]
fn integer_range_iteration_introduces_the_implicit_host_carrier_before_the_value() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "by for:\n    ? forall n range(0, 3):\n        n < 3\n",
            "integer_range_implicit_carrier.lit",
        )
        .expect("execute range iteration");
    let generated = StmtResultToLeanCompiler::new("integer_range_implicit_carrier.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile range iteration");

    assert!(
        generated.contains("intro __carrier1 n __type1"),
        "{generated}"
    );
}

#[test]
fn algebraic_nonzero_child_proof_is_anchored_to_its_semantic_proposition() {
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "forall z C:\n    z + i != 0\n    =>:\n        (z + i) ^ 2 / (z + i) = z + i\n",
            "algebraic_nonzero_semantic_type.lit",
        )
        .expect("execute algebraic normalization with a nonzero premise");
    let generated = StmtResultToLeanCompiler::new("algebraic_nonzero_semantic_type.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile algebraic normalization");

    assert!(
        generated.contains("exact (show ¬ Litex.Same")
            && generated.contains("from (by")
            && generated.contains("Litex.Same.ofEq __native_eq"),
        "{generated}"
    );
}

pub(super) fn execute_closed_natural_membership() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "2 + 3 $in N\n",
        "direct_closed_membership.lit",
    )
    .expect("execute closed natural membership")
}

pub(super) fn closed_natural_membership_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessFactStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results else {
        panic!("expected one successful factual result")
    };
    result
}

#[test]
fn numeric_eval_wraps_recursive_computation_and_publishes_its_exact_fact_id() {
    run_registered_rule_test(|| {
        let results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "eval 2 + 3\n2 + 3 = 5\n",
                "direct_numeric_eval.lit",
            )
            .expect("execute numeric eval and its later citation");
        let [StmtResult::Success(SuccessStmtResult::Command(SuccessCommandStmtResult::EvalStmt(
            eval,
        ))), _] = results.as_slice()
        else {
            panic!("expected eval followed by one fact Result")
        };
        let SuccessEvalStmtExecutionResult::Evaluated(execution) = &eval.execution else {
            panic!("ordinary eval must retain its execution Result")
        };
        let evaluation = execution
            .recursive_numeric_evaluation
            .as_ref()
            .expect("closed numeric eval must retain its recursive computation");
        assert_eq!(evaluation.expression.to_string(), "2 + 3");
        assert_eq!(evaluation.value.to_string(), "5");
        let [store] = eval.common.infers.store_fact_outputs.as_slice() else {
            panic!("numeric eval must retain one equality store")
        };
        assert!(store.fact_id.is_some());

        let generated = StmtResultToLeanCompiler::new("direct_numeric_eval.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile eval directly from its recursive Result");
        assert!(
            generated.contains("Litex.Same ((2 : ℂ) + (3 : ℂ)) (5 : ℂ)")
                && generated.contains("exact __fact0"),
            "{generated}"
        );

        let json = crate::output::render_statement_result_json(&results[0]);
        assert!(
            json.contains("\"recursive_numeric_evaluation\": {"),
            "{json}"
        );
        assert!(
            json.contains(&format!(
                "\"fact_id\": \"{}\"",
                store.fact_id.expect("checked above")
            )),
            "reported eval store must use the final attached FactId: {json}"
        );
    });
}

#[test]
fn numeric_eval_rejects_a_corrupted_recursive_normal_form() {
    run_registered_rule_test(|| {
        let mut results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "eval 2 + 3\n",
                "corrupted_numeric_eval.lit",
            )
            .expect("execute numeric eval");
        let [StmtResult::Success(SuccessStmtResult::Command(SuccessCommandStmtResult::EvalStmt(
            eval,
        )))] = results.as_mut_slice()
        else {
            panic!("expected one eval Result")
        };
        let SuccessEvalStmtExecutionResult::Evaluated(execution) = &mut eval.execution else {
            panic!("ordinary eval must retain its execution Result")
        };
        execution
            .recursive_numeric_evaluation
            .as_mut()
            .expect("closed numeric eval must retain recursive evidence")
            .value = Number::new("6".to_string());

        let error = StmtResultToLeanCompiler::new("corrupted_numeric_eval.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("retargeted eval computation must fail closed");
        assert!(
            error.contains("evaluation changed its expression or value")
                || error.contains("changed its input or output"),
            "{error}"
        );
    });
}

fn execute_integer_remainder_membership() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "forall a, b Z:\n    b != 0\n    =>:\n        a % b $in Z\n",
        "direct_integer_remainder_membership.lit",
    )
    .expect("execute integer remainder membership")
}

fn integer_remainder_builtin_mut(results: &mut [StmtResult]) -> &mut SuccessBuiltinFactProofResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results else {
        panic!("expected one forall Result")
    };
    let verification = forall_result
        .verification_mut()
        .expect("test owns the forall verification Result");
    let SuccessFactProofResult::ForallProof(forall) = verification.proof_mut() else {
        panic!("expected forall proof Result")
    };
    let [conclusion] = forall.proves.as_mut_slice() else {
        panic!("expected one forall conclusion")
    };
    let Some(conclusion) = conclusion.result.verified_mut() else {
        panic!("expected factual remainder conclusion")
    };
    let SuccessFactProofResult::BuiltinRule(builtin) = conclusion.proof_mut() else {
        panic!("expected builtin remainder proof")
    };
    builtin
}

#[test]
fn integer_remainder_uses_exact_integer_representatives_from_the_compiler_environment() {
    run_registered_rule_test(|| {
        let mut results = execute_integer_remainder_membership();
        let builtin = integer_remainder_builtin_mut(&mut results);
        assert!(matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::IntegerMembershipClosure(
                IntegerMembershipClosureBuiltinRule::Mod
            ))
        ));
        let generated = StmtResultToLeanCompiler::new("direct_integer_remainder_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile integer remainder directly from recursive Results");
        assert!(
            generated.contains("Litex.Rules.complexIntInZ")
                && generated.contains("Litex.Rules.complexIntInZ (a % b)")
                && !generated.contains("Litex.In.rep a")
                && !generated.contains("Litex.In.rep b")
                && generated.contains(" % "),
            "{generated}"
        );
    });
}

#[test]
fn integer_remainder_rejects_a_certificate_retargeted_to_addition() {
    run_registered_rule_test(|| {
        let mut results = execute_integer_remainder_membership();
        let builtin = integer_remainder_builtin_mut(&mut results);
        builtin.evidence = SuccessBuiltinFactProofEvidenceResult::Typed(
            BuiltinRuleEvidence::IntegerMembershipClosure(IntegerMembershipClosureBuiltinRule::Add),
        );
        let error = StmtResultToLeanCompiler::new("corrupted_integer_remainder_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("retargeted integer closure certificate must fail closed");
        assert!(
            error.contains("integer arithmetic closure changed its target operator"),
            "{error}"
        );
    });
}

fn execute_rational_power_membership() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "forall a Q, z Z:\n    a != 0\n    =>:\n        a^z $in Q\n",
        "direct_rational_power_membership.lit",
    )
    .expect("execute rational integer-power membership")
}

fn rational_power_builtin_mut(results: &mut [StmtResult]) -> &mut SuccessBuiltinFactProofResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results else {
        panic!("expected one forall Result")
    };
    let verification = forall_result
        .verification_mut()
        .expect("test owns the forall verification Result");
    let SuccessFactProofResult::ForallProof(forall) = verification.proof_mut() else {
        panic!("expected forall proof Result")
    };
    let [conclusion] = forall.proves.as_mut_slice() else {
        panic!("expected one forall conclusion")
    };
    let Some(conclusion) = conclusion.result.verified_mut() else {
        panic!("expected factual rational-power conclusion")
    };
    let SuccessFactProofResult::BuiltinRule(builtin) = conclusion.proof_mut() else {
        panic!("expected builtin rational-power proof")
    };
    builtin
}

#[test]
fn rational_power_uses_exact_rational_and_integer_compiler_representatives() {
    run_registered_rule_test(|| {
        let mut results = execute_rational_power_membership();
        let builtin = rational_power_builtin_mut(&mut results);
        assert!(matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::RationalMembershipClosure(
                RationalMembershipClosureBuiltinRule::Pow
            ))
        ));
        let generated = StmtResultToLeanCompiler::new("direct_rational_power_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile rational integer power directly from recursive Results");
        assert!(
            generated.contains("Litex.Rules.complexRatInQ")
                && generated.contains("Litex.In.rep a __h")
                && generated.contains(" ^ z")
                && !generated.contains("Litex.In.rep z")
                && generated.contains(" ^ "),
            "{generated}"
        );
    });
}

#[test]
fn rational_power_rejects_a_certificate_retargeted_to_division() {
    run_registered_rule_test(|| {
        let mut results = execute_rational_power_membership();
        let builtin = rational_power_builtin_mut(&mut results);
        builtin.evidence = SuccessBuiltinFactProofEvidenceResult::Typed(
            BuiltinRuleEvidence::RationalMembershipClosure(
                RationalMembershipClosureBuiltinRule::Div,
            ),
        );
        let error = StmtResultToLeanCompiler::new("corrupted_rational_power_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("retargeted rational closure certificate must fail closed");
        assert!(
            error.contains("rational arithmetic closure changed its target operator"),
            "{error}"
        );
    });
}

#[test]
fn direct_closed_membership_compiler_rejects_corrupted_evaluation_tree() {
    let mut results = execute_closed_natural_membership();
    let result = closed_natural_membership_result_mut(&mut results);
    let verification = result
        .verification_mut()
        .expect("test result has one proof owner");
    let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
        panic!("expected builtin proof")
    };
    let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = proof.evidence.typed_mut()
    else {
        panic!("expected closed membership evidence")
    };
    evidence.evaluation.value = Number::new("6".to_string());

    let error = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("corrupted evaluation must fail closed");
    assert!(error.contains("evaluation changed its expression or value"));
}

#[test]
fn direct_closed_membership_compiler_rejects_corrupted_infer_fact_id() {
    let mut results = execute_closed_natural_membership();
    let result = closed_natural_membership_result_mut(&mut results);
    result.store.infers.rule_applications[0].premises[0].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("corrupted infer citation must fail closed");
    assert!(
        error.contains("FactId"),
        "unexpected corruption error: {error}"
    );
}
