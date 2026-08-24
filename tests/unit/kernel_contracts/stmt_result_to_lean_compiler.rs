use super::*;
use crate::output::display_stmt_result_json_v2;
use crate::verify::rule_schema::{RuleFingerprint, RuleId};

#[test]
fn combined_builtin_items_retain_and_compile_their_typed_component_evidence() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "1 = 1 and 2 = 2\n",
            "combined_builtin_items.lit",
        )
        .expect("execute conjunction fixture");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
        panic!("expected one successful conjunction Result")
    };
    let target = result.fact();
    let SuccessFactProofResult::CombinedProofs(combined) = result.proof() else {
        panic!("expected recursive combined proof Result")
    };

    let proof = StmtResultToLeanCompiler::new("combined_builtin_items.lit")
        .construct_lean_combined_fact_proof_from_result(&target, combined)
        .expect("compile typed combined builtin items")
        .expect("typed combined builtin items are direct");
    assert_eq!(proof, "⟨Litex.Same.refl (1 : ℂ), Litex.Same.refl (2 : ℂ)⟩");
}

fn execute_structured_integer_induction_from(start: &str) -> Vec<StmtResult> {
    let source = format!(
            "by induc n from {start}:\n    ? n + 1 = n + 1\n    ? from n = {start}:\n        do_nothing\n    ? induc:\n        do_nothing\n"
        );
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            &source,
            "structured_integer_induction_result.lit",
        )
        .expect("execute structured integer induction")
}

fn structured_integer_induction_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessByInducStmtResult {
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByInducStmt(result)))] =
        results
    else {
        panic!("expected one successful structured induction Result")
    };
    result
}

#[test]
fn structured_integer_induction_retains_named_recursive_results_and_exact_fact_ids() {
    let mut results = execute_structured_integer_induction_from("-1");
    let result = structured_integer_induction_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("structured induction retains its verification Result");
    let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &verification.proof else {
        panic!("expected typed structured integer-induction proof")
    };

    assert_eq!(
        proof.start.to_string(),
        result.statement.induc_from.to_string()
    );
    assert_eq!(proof.base.proof_steps.len(), 1);
    assert_eq!(proof.step.proof_steps.len(), 1);
    assert_eq!(proof.base.conclusions.len(), 1);
    assert_eq!(proof.step.conclusions.len(), 1);

    let [base_parameter, base_equality] = proof.base.assumptions.as_slice() else {
        panic!("base case must retain its two named assumptions")
    };
    assert_eq!(
        base_parameter.role,
        SuccessVerifyByInducAssumptionRole::ParameterType
    );
    assert_eq!(
        base_equality.role,
        SuccessVerifyByInducAssumptionRole::BaseCaseEquality
    );
    assert_ne!(base_parameter.fact_id, base_equality.fact_id);

    let [step_parameter, step_domain, step_hypothesis] = proof.step.assumptions.as_slice() else {
        panic!("step case must retain parameter, domain, and hypothesis assumptions")
    };
    assert_eq!(
        step_parameter.role,
        SuccessVerifyByInducAssumptionRole::ParameterType
    );
    assert_eq!(
        step_domain.role,
        SuccessVerifyByInducAssumptionRole::DomainLowerBound
    );
    assert_eq!(
        step_hypothesis.role,
        SuccessVerifyByInducAssumptionRole::InductionHypothesis
    );
    assert_eq!(step_hypothesis.goal_index, Some(0));
    assert_ne!(step_parameter.fact_id, step_domain.fact_id);
    assert_ne!(step_domain.fact_id, step_hypothesis.fact_id);
    for assumption in proof
        .base
        .assumptions
        .iter()
        .chain(proof.step.assumptions.iter())
    {
        let case_infers = if proof
            .base
            .assumptions
            .iter()
            .any(|candidate| candidate.fact_id == assumption.fact_id)
        {
            &proof.base.assumption_infers
        } else {
            &proof.step.assumption_infers
        };
        assert!(infer_result_retains_fact_id(
            case_infers,
            &assumption.fact,
            assumption.fact_id
        ));
    }
    assert_eq!(
        proof.base.conclusions[0].goal.to_string(),
        proof.base.conclusions[0]
            .check
            .factual_success()
            .expect("base conclusion check is factual")
            .fact()
            .to_string()
    );
    assert_eq!(
        proof.step.conclusions[0].goal.to_string(),
        proof.step.conclusions[0]
            .check
            .factual_success()
            .expect("step conclusion check is factual")
            .fact()
            .to_string()
    );
}

#[test]
fn structured_integer_induction_compiler_follows_result_scopes_and_balances_its_stack() {
    let results = execute_structured_integer_induction_from("-1");
    let mut compiler = StmtResultToLeanCompiler::new("structured_integer_induction_result.lit");
    for result in &results {
        compiler
            .compile_stmt_result_to_lean_source(result)
            .expect("compile recursive structured induction Result");
    }
    assert!(compiler.environment_stack.is_top_level());
    let generated = compiler.finish_lean_source().expect("finish Lean source");
    assert!(
        generated.contains("Litex.Rules.integerInductionFrom"),
        "{generated}"
    );
}

#[test]
fn structured_integer_induction_rejects_a_retargeted_hypothesis_fact_id() {
    let mut results = execute_structured_integer_induction_from("-1");
    let result = structured_integer_induction_result_mut(&mut results);
    let verification = result
        .verification
        .as_mut()
        .expect("structured induction retains verification");
    let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &mut verification.proof else {
        panic!("expected structured integer induction")
    };
    proof.step.assumptions[2].fact_id = proof.step.assumptions[1].fact_id;

    let error = StmtResultToLeanCompiler::new("corrupted_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("retargeted local FactId must fail closed");
    assert!(error.contains("lost FactId"), "{error}");
}

#[test]
fn structured_integer_induction_rejects_a_changed_conclusion_result() {
    let mut results = execute_structured_integer_induction_from("-1");
    let result = structured_integer_induction_result_mut(&mut results);
    let verification = result
        .verification
        .as_mut()
        .expect("structured induction retains verification");
    let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &mut verification.proof else {
        panic!("expected structured integer induction")
    };
    proof.step.conclusions[0].goal = proof.step.assumptions[1].fact.clone();

    let error = StmtResultToLeanCompiler::new("corrupted_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("changed conclusion must fail closed");
    assert!(error.contains("changed its checked goal"), "{error}");
}

#[test]
fn structured_integer_induction_zero_and_strong_boundaries_fail_closed() {
    let zero_results = execute_structured_integer_induction_from("0");
    let zero_error = StmtResultToLeanCompiler::new("zero_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&zero_results)
        .expect_err("zero-ended order lowering must fail closed");
    assert!(zero_error.contains("nonnegative-value"), "{zero_error}");

    let strong_source = "by strong_induc n from -1:\n    ? n + 1 = n + 1\n    ? from n = -1:\n        do_nothing\n    ? strong_induc:\n        do_nothing\n";
    let strong_results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            strong_source,
            "strong_structured_induction.lit",
        )
        .expect("execute structured strong induction");
    let strong_error = StmtResultToLeanCompiler::new("strong_structured_induction.lit")
        .compile_stmt_results_to_lean_source(&strong_results)
        .expect_err("strong induction must fail closed until its Result compiler lands");
    assert!(strong_error.contains("strong induction"), "{strong_error}");
}

#[test]
fn forall_result_retains_exact_parameter_and_domain_fact_ids_for_compiler_scope() {
    let source = "forall a set, b set:\n    $is_set(a)\n    $is_set(b)\n    a != b\n    =>:\n        b != a\n";
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            source,
            "direct_forall_scope_fact_ids.lit",
        )
        .expect("execute forall before dropping Runtime");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
        panic!("expected one successful forall Result")
    };
    let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
        panic!("expected recursive ForallProof Result")
    };
    assert_eq!(proof.parameter_assumptions.len(), 2);
    assert_eq!(proof.domain_assumptions.len(), 3);
    assert_eq!(
        proof.parameter_assumptions[0].fact_id,
        proof.domain_assumptions[0].fact_id
    );
    assert_eq!(
        proof.parameter_assumptions[1].fact_id,
        proof.domain_assumptions[1].fact_id
    );
    assert_ne!(
        proof.domain_assumptions[2].fact_id,
        proof.parameter_assumptions[0].fact_id
    );

    let json = display_stmt_result_json_v2(&results[0]);
    assert!(json.contains("\"parameter_assumptions\""), "{json}");
    assert!(json.contains("\"domain_assumptions\""), "{json}");

    let generated = StmtResultToLeanCompiler::new("direct_forall_scope_fact_ids.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile only from the frozen recursive Result");
    assert!(generated.contains("Litex.Rules.notSameSymm"), "{generated}");
}

#[test]
fn nested_compiler_environment_inherits_outer_bindings_without_leaking_back() {
    let outer_fact_id = FactId::new(1);
    let inner_fact_id = FactId::new(2);
    let inner_integer_symbol_id = SymbolId::new(3);
    let mut outer = StmtResultToLeanCompilerEnvironmentStack::default();
    outer
        .fact_names
        .insert(outer_fact_id, "__outer".to_string());

    let mut inner = outer.clone();
    inner.push_inherited_environment();
    assert_eq!(inner.environments.len(), 2);
    assert_eq!(
        inner.fact_names.get(&outer_fact_id),
        Some(&"__outer".to_string())
    );
    inner
        .fact_names
        .insert(inner_fact_id, "__inner".to_string());
    inner
        .numeric_integer_values
        .insert(inner_integer_symbol_id, "(__inner_integer : ℤ)".to_string());
    inner.numeric_rational_values.insert(
        inner_integer_symbol_id,
        "(__inner_rational : ℚ)".to_string(),
    );

    assert!(!outer.fact_names.contains_key(&inner_fact_id));
    assert!(!outer
        .numeric_integer_values
        .contains_key(&inner_integer_symbol_id));
    assert!(!outer
        .numeric_rational_values
        .contains_key(&inner_integer_symbol_id));
    assert_eq!(
        inner.fact_names.get(&inner_fact_id),
        Some(&"__inner".to_string())
    );
    inner.pop_local_environment();
    assert_eq!(inner.environments.len(), 1);
    assert!(!inner.fact_names.contains_key(&inner_fact_id));
    assert!(!inner
        .numeric_integer_values
        .contains_key(&inner_integer_symbol_id));
    assert!(!inner
        .numeric_rational_values
        .contains_key(&inner_integer_symbol_id));
    assert_eq!(
        inner.fact_names.get(&outer_fact_id),
        Some(&"__outer".to_string())
    );
}

#[test]
fn failed_local_result_compilation_restores_the_outer_compiler_layer() {
    let outer_fact_id = FactId::new(1);
    let mut compiler = StmtResultToLeanCompiler::new("local_failure.lit");
    compiler.declarations.push("outer declaration".into());
    compiler.next_fact_name_index = 7;
    compiler.next_sketch_namespace_index = 3;
    compiler
        .environment_stack
        .fact_names
        .insert(outer_fact_id, "__outer".into());

    let unknown: StmtResult =
        UnknownGenericStmtResult::new_with_detail("deliberate local compiler failure".into())
            .into();
    let error = compiler
        .compile_stmt_results_in_new_local_environment(&[unknown])
        .expect_err("unknown local result must fail closed");

    assert!(error.contains("cannot compile unknown result"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations, ["outer declaration"]);
    assert_eq!(compiler.next_fact_name_index, 7);
    assert_eq!(compiler.next_sketch_namespace_index, 3);
    assert_eq!(
        compiler.environment_stack.fact_names.get(&outer_fact_id),
        Some(&"__outer".to_string())
    );
}

#[test]
fn direct_compiler_rejects_a_conjunction_component_result_with_changed_position() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
fn integer_range_iteration_rejects_a_corrupted_evaluated_value() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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

fn execute_closed_natural_membership() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "2 + 3 $in N\n",
            "direct_closed_membership.lit",
        )
        .expect("execute closed natural membership")
}

fn closed_natural_membership_result_mut(results: &mut [StmtResult]) -> &mut SuccessFactStmtResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results else {
        panic!("expected one successful factual result")
    };
    result
}

#[test]
fn numeric_eval_wraps_recursive_computation_and_publishes_its_exact_fact_id() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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

        let json = crate::output::display_stmt_result_json_v2(&results[0]);
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
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "forall a, b Z:\n    b != 0\n    =>:\n        a % b $in Z\n",
            "direct_integer_remainder_membership.lit",
        )
        .expect("execute integer remainder membership")
}

fn integer_remainder_builtin_mut(results: &mut [StmtResult]) -> &mut SuccessBuiltinFactProofResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results else {
        panic!("expected one forall Result")
    };
    let verification = std::rc::Rc::get_mut(&mut forall_result.verification)
        .expect("test owns the forall verification Result");
    let SuccessFactProofResult::ForallProof(forall) = verification.proof_mut() else {
        panic!("expected forall proof Result")
    };
    let [conclusion] = forall.proves.as_mut_slice() else {
        panic!("expected one forall conclusion")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(conclusion)) = conclusion.result.as_mut()
    else {
        panic!("expected factual remainder conclusion")
    };
    let verification = std::rc::Rc::get_mut(&mut conclusion.verification)
        .expect("test owns the remainder verification Result");
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
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
                && generated.contains("Litex.In.rep a __h0_1")
                && generated.contains("Litex.In.rep b __h0_2")
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "forall a Q, z Z:\n    a != 0\n    =>:\n        a^z $in Q\n",
            "direct_rational_power_membership.lit",
        )
        .expect("execute rational integer-power membership")
}

fn rational_power_builtin_mut(results: &mut [StmtResult]) -> &mut SuccessBuiltinFactProofResult {
    let [StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results else {
        panic!("expected one forall Result")
    };
    let verification = std::rc::Rc::get_mut(&mut forall_result.verification)
        .expect("test owns the forall verification Result");
    let SuccessFactProofResult::ForallProof(forall) = verification.proof_mut() else {
        panic!("expected forall proof Result")
    };
    let [conclusion] = forall.proves.as_mut_slice() else {
        panic!("expected one forall conclusion")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(conclusion)) = conclusion.result.as_mut()
    else {
        panic!("expected factual rational-power conclusion")
    };
    let verification = std::rc::Rc::get_mut(&mut conclusion.verification)
        .expect("test owns the rational-power verification Result");
    let SuccessFactProofResult::BuiltinRule(builtin) = verification.proof_mut() else {
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
                && generated.contains("Litex.In.rep a __h0_1")
                && generated.contains("Litex.In.rep z __h0_2")
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
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
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

fn execute_known_forall_instantiation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "abstract_prop p(x)\naxiom p_real:\n    ? forall x R:\n        $p(x)\n\n$p(2)\n",
            "direct_known_forall.lit",
        )
        .expect("execute known-forall instantiation")
}

fn known_forall_instantiation_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessInstantiateKnownForallResult {
    let [_, _, StmtResult::Success(SuccessStmtResult::Fact(result))] = results else {
        panic!("expected abstract predicate, source axiom, and instantiated fact")
    };
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
    let SuccessFactProofResult::KnownForallInstantiation(instantiation) = verification.proof_mut()
    else {
        panic!("expected known-forall proof Result")
    };
    instantiation
}

#[test]
fn known_forall_instantiation_combines_exact_fact_id_and_requirement_result_directly() {
    run_registered_rule_test(|| {
        let results = execute_known_forall_instantiation();
        let generated = StmtResultToLeanCompiler::new("direct_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile known-forall Result directly");

        assert!(generated.contains("axiom p_real"), "{generated}");
        assert!(
                generated.contains("exact (p_real (2 : ℂ) (Litex.Rules.complexRealInR")
                    && generated.contains("complexRealInR (2 : ℝ)"),
                "known-forall application did not combine its source theorem and parameter requirement: {generated}"
            );
    });
}

fn execute_multi_conclusion_known_forall_instantiation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
        "abstract_prop first(x)\nabstract_prop second(x)\naxiom paired_source:\n    ? forall x R:\n        $first(x)\n        $second(x)\n\n$second(2)\n",
        "direct_multi_conclusion_known_forall.lit",
    )
    .expect("execute multi-conclusion known-forall instantiation")
}

fn multi_conclusion_known_forall_instantiation_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessInstantiateKnownForallResult {
    let result = results
        .last_mut()
        .and_then(StmtResult::factual_success_mut)
        .expect("final result should be the instantiated second conclusion");
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
    let SuccessFactProofResult::KnownForallInstantiation(instantiation) = verification.proof_mut()
    else {
        panic!("expected known-forall proof Result")
    };
    instantiation
}

#[test]
fn known_forall_instantiation_projects_the_selected_multi_conclusion_source() {
    run_registered_rule_test(|| {
        let results = execute_multi_conclusion_known_forall_instantiation();
        let generated = StmtResultToLeanCompiler::new("direct_multi_conclusion_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile selected multi-conclusion known-forall source");

        assert!(generated.contains("axiom paired_source"), "{generated}");
        assert!(
            generated.contains("paired_source") && generated.contains(".2"),
            "the compiler did not project the retained second conclusion: {generated}"
        );
    });
}

#[test]
fn known_forall_instantiation_rejects_a_corrupted_multi_conclusion_location() {
    run_registered_rule_test(|| {
        let mut results = execute_multi_conclusion_known_forall_instantiation();
        multi_conclusion_known_forall_instantiation_result_mut(&mut results)
            .source_conclusion_location = ForallConclusionLocation::direct_then_fact(0);

        let error = StmtResultToLeanCompiler::new("direct_multi_conclusion_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("corrupted multi-conclusion location must fail closed");
        assert!(
            error.contains("does not match target"),
            "unexpected corruption error: {error}"
        );
    });
}

#[test]
fn known_forall_instantiation_rejects_a_reclassified_parameter_requirement() {
    run_registered_rule_test(|| {
        let mut results = execute_known_forall_instantiation();
        known_forall_instantiation_result_mut(&mut results).requirements[0].kind =
            KnownForallRequirementKind::Domain;

        let error = StmtResultToLeanCompiler::new("direct_known_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("reclassified known-forall requirement must fail closed");
        assert!(error.contains("parameter requirement 0 changed its kind"));
    });
}

#[test]
fn function_application_return_membership_resolves_its_exact_well_definedness_fact_id() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "trust have f fn(x R) R\ntrust have a R\nf(a) $in R\n",
                "direct_function_application_return_membership.lit",
            )
            .expect("execute exact function-return membership");
        let result = results
            .last()
            .and_then(StmtResult::factual_success)
            .expect("function-return membership is factual");
        assert!(result.well_definedness.recursive.is_some());

        let generated =
            StmtResultToLeanCompiler::new("direct_function_application_return_membership.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect("compile exact function-return membership directly");
        assert!(
            generated.contains("Litex.In.own Litex.R") && generated.contains("Litex.fnApply"),
            "function-return membership did not use its retained application layer: {generated}"
        );
    });
}

#[test]
fn trust_have_rejects_a_missing_parameter_store_fact_id() {
    run_registered_rule_test(|| {
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "trust have a R\n",
                "direct_trust_have.lit",
            )
            .expect("execute trusted object declaration");
        let [StmtResult::Success(SuccessStmtResult::UnsafeStmt(
            SuccessUnsafeStmtResult::TrustHaveStmt(result),
        ))] = results.as_mut_slice()
        else {
            panic!("expected one trust-have Result")
        };
        result.common.infers.store_fact_outputs[0].fact_id = None;

        let error = StmtResultToLeanCompiler::new("direct_trust_have.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("missing trusted binding FactId must fail closed");
        assert!(error.contains("parameter store 0 has no FactId"), "{error}");
    });
}

#[test]
fn known_fact_rational_transformation_replays_its_ordered_result_steps() {
    run_registered_rule_test(|| {
        const SOURCE: &str = "trust:\n    2 < 3\n1 + 1 < 3\n";
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                SOURCE,
                "direct_fact_transformation.lit",
            )
            .expect("execute a rationally normalized known-fact citation");
        let result = results
            .last()
            .and_then(StmtResult::factual_success)
            .expect("normalized citation is factual");
        let SuccessFactProofResult::Transform(transformation) = result.proof() else {
            panic!(
                "expected recursive fact transformation, got {:#?}",
                result.proof()
            )
        };
        assert!(matches!(
            transformation.rule,
            FactTransformationRule::RationalNormalization
        ));
        assert!(matches!(
            transformation.source.proof(),
            SuccessFactProofResult::StoredFactCitation(_)
        ));

        let generated = StmtResultToLeanCompiler::new("direct_fact_transformation.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile ordered fact transformation");
        assert!(generated.contains("convert __fact0 using 1 <;> norm_num"));
    });
}

#[test]
fn known_fact_transformation_rejects_a_removed_result_step() {
    run_registered_rule_test(|| {
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "trust:\n    2 < 3\n1 + 1 < 3\n",
                "direct_fact_transformation.lit",
            )
            .expect("execute a rationally normalized known-fact citation");
        let result = results
            .last_mut()
            .and_then(StmtResult::factual_success_mut)
            .expect("normalized citation is factual");
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("test citation has one verification owner");
        let SuccessFactProofResult::Transform(transformation) = verification.proof_mut() else {
            panic!("expected recursive fact transformation")
        };
        let source = std::rc::Rc::get_mut(&mut transformation.source)
            .expect("test owns the nested transformation source");
        *source.proof_mut() =
            SuccessFactProofResult::DiagnosticOnly(SuccessDiagnosticFactProofResult {
                detail: "corrupted nested source".to_string(),
            });

        let error = StmtResultToLeanCompiler::new("direct_fact_transformation.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("removed transformation step must fail closed");
        assert!(
            error.contains("does not support") || error.contains("no direct"),
            "{error}"
        );
    });
}

fn execute_direct_forall_proof() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "forall x R:\n    x = x\n",
            "direct_forall_proof.lit",
        )
        .expect("execute direct forall proof")
}

#[test]
fn forall_proof_compiles_its_binder_owned_results_in_one_child_environment() {
    let results = execute_direct_forall_proof();
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
        panic!("expected one forall fact Result")
    };
    let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
        panic!("expected ForallProof Result")
    };
    let parameter_fact_id = proof.assumption_infers.store_fact_outputs[0]
        .fact_id
        .expect("forall parameter retains its local FactId");
    let conclusion_fact_id = proof.proves[0]
        .result
        .factual_success()
        .expect("forall conclusion is factual")
        .store
        .fact_id
        .expect("forall conclusion retains its FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_forall_proof.lit");

    assert!(compiler
        .compile_direct_forall_fact_result(result)
        .expect("compile ForallProof directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&parameter_fact_id));
    assert!(compiler
        .environment_stack
        .forall_conclusion_bindings
        .contains_key(&conclusion_fact_id));
    assert!(compiler.declarations[0].contains("intro x __h0_1"));
    assert!(compiler.declarations[0].contains("have __c0_0"));
}

#[test]
fn forall_proof_rejects_a_parameter_assumption_with_the_wrong_fact_id() {
    let mut results = execute_direct_forall_proof();
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_mut_slice() else {
        panic!("expected one forall fact Result")
    };
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
    let SuccessFactProofResult::ForallProof(proof) = verification.proof_mut() else {
        panic!("expected ForallProof Result")
    };
    proof.parameter_assumptions[0].fact_id = FactId::new(999_991);

    let error = StmtResultToLeanCompiler::new("direct_forall_proof.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("forall parameter with a forged FactId must fail closed");
    assert!(error.contains("retain exact FactId"), "{error}");
}

#[test]
fn forall_proof_compiles_natural_parameter_inference_inside_its_binder_environment() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "forall a, b N:\n    a + b $in N\n",
            "direct_natural_forall.lit",
        )
        .expect("execute natural-parameter forall");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
        panic!("expected one natural forall Result")
    };
    let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
        panic!("expected ForallProof Result")
    };
    let inferred_fact_ids = proof
        .assumption_infers
        .rule_applications
        .iter()
        .map(|application| {
            application.conclusions[0]
                .fact_id
                .expect("typed natural inference retains a FactId")
        })
        .collect::<Vec<_>>();
    let mut compiler = StmtResultToLeanCompiler::new("direct_natural_forall.lit");

    assert!(compiler
        .compile_direct_forall_fact_result(result)
        .expect("compile natural inference directly inside the forall frame"));
    let declaration = compiler
        .declarations
        .last()
        .expect("natural forall emits one theorem");
    assert_eq!(declaration.matches("have __infer0_").count(), 4);
    assert!(declaration.contains("Litex.Rules.nonnegativeOfInN (__h0_1)"));
    assert!(declaration.contains("Litex.Rules.complexEqNatInN"));
    assert!(!declaration.contains("complexAddInN (__h0_1)"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    for fact_id in inferred_fact_ids {
        assert!(!compiler.environment_stack.fact_names.contains_key(&fact_id));
    }
}

#[test]
fn forall_proof_rejects_natural_inference_citing_the_wrong_parameter_fact_id() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "forall a, b N:\n    a + b $in N\n",
            "direct_natural_forall.lit",
        )
        .expect("execute natural-parameter forall");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_mut_slice() else {
        panic!("expected one natural forall Result")
    };
    let verification = std::rc::Rc::get_mut(&mut result.verification)
        .expect("corruption test uniquely owns its verification");
    let SuccessFactProofResult::ForallProof(proof) = verification.proof_mut() else {
        panic!("expected ForallProof Result")
    };
    let wrong_fact_id = proof.assumption_infers.store_fact_outputs[1]
        .fact_id
        .expect("second parameter retains a FactId");
    proof.assumption_infers.rule_applications[0].premises[0].fact_id = Some(wrong_fact_id);

    let error = StmtResultToLeanCompiler::new("direct_natural_forall.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("retargeted natural inference must fail closed");
    assert!(
        error.contains("cites a source outside its complete forall assumption Result"),
        "{error}"
    );
}

#[test]
fn forall_proof_compiles_positive_real_inference_only_inside_its_binder_environment() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "forall r R+:\n    r > 0\n",
                "direct_positive_real_forall.lit",
            )
            .expect("execute positive-real forall");
        let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_slice() else {
            panic!("expected one positive-real forall Result")
        };
        let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
            panic!("expected ForallProof Result")
        };
        let inferred_fact_id = proof.assumption_infers.rule_applications[0].conclusions[0]
            .fact_id
            .expect("typed positive inference retains a FactId");
        let mut compiler = StmtResultToLeanCompiler::new("direct_positive_real_forall.lit");

        assert!(compiler
            .compile_direct_forall_fact_result(result)
            .expect("compile positive inference directly inside the forall frame"));
        let declaration = compiler
            .declarations
            .last()
            .expect("positive-real forall emits one theorem");
        assert!(declaration.contains(
            "have __infer0_0 : Litex.Positive r := Litex.Rules.positiveOfInRPos (__h0_1)"
        ));
        assert_eq!(compiler.environment_stack.environments.len(), 1);
        assert!(!compiler
            .environment_stack
            .fact_names
            .contains_key(&inferred_fact_id));
    });
}

#[test]
fn forall_proof_rejects_positive_inference_with_a_corrupted_source_set() {
    run_registered_rule_test(|| {
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "forall r R+:\n    r > 0\n",
                "direct_positive_real_forall.lit",
            )
            .expect("execute positive-real forall");
        let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_mut_slice() else {
            panic!("expected one positive-real forall Result")
        };
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("corruption test uniquely owns its verification");
        let SuccessFactProofResult::ForallProof(proof) = verification.proof_mut() else {
            panic!("expected ForallProof Result")
        };
        let InferRule::PositiveStandardSetMembershipImpliesPositive(rule) =
            &mut proof.assumption_infers.rule_applications[0].rule
        else {
            panic!("expected typed positive-carrier inference")
        };
        rule.source_set = StandardSet::NPos;

        let error = StmtResultToLeanCompiler::new("direct_positive_real_forall.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("retargeted positive-carrier inference must fail closed");
        assert!(
            error.contains("source does not match its typed source set"),
            "{error}"
        );
    });
}

#[test]
fn forall_proof_keeps_a_function_parameter_contract_inside_its_binder_environment() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "forall f fn(x R) R:\n    f = f\n",
                "direct_forall_function_parameter.lit",
            )
            .expect("execute forall with a function parameter");
        let generated = StmtResultToLeanCompiler::new("direct_forall_function_parameter.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile function-parameter forall directly");

        assert!(
            generated.contains("intro __carrier1 f __h0_1")
                && generated.contains("Litex.Same.refl f"),
            "function parameter lost its carrier or membership contract: {generated}"
        );
    });
}

#[test]
fn forall_registered_set_parameter_checks_are_validated_without_lean_proof_terms() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "forall A, B set:\n    union(A, B) = union(B, A)\n",
                "direct_forall_set_parameters.lit",
            )
            .expect("execute forall with set parameters");
        let generated = StmtResultToLeanCompiler::new("direct_forall_set_parameters.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile set-parameter forall directly");

        assert!(
            generated.contains("intro A B")
                && generated.contains("Litex.SetRules.unionCommutative A B"),
            "sethood child was not consumed as a compiler-only parameter check: {generated}"
        );
    });
}

fn execute_direct_forall_proof_with_domain() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "forall a R:\n    a = a\n    =>:\n        a = a\n",
            "direct_forall_domain.lit",
        )
        .expect("execute forall proof with a domain premise")
}

#[test]
fn forall_proof_installs_explicit_domain_fact_ids_in_the_same_binder_environment() {
    run_registered_rule_test(|| {
        let results = execute_direct_forall_proof_with_domain();
        let generated = StmtResultToLeanCompiler::new("direct_forall_domain.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile domain-bearing forall directly");

        assert!(
            generated.contains("intro a __h0_1 __domain1") && generated.contains("__domain1"),
            "domain premise was not installed in the forall child environment: {generated}"
        );
    });
}

#[test]
fn forall_proof_rejects_an_explicit_domain_with_the_wrong_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_direct_forall_proof_with_domain();
        let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_mut_slice() else {
            panic!("expected one forall fact Result")
        };
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("test result has one proof owner");
        let SuccessFactProofResult::ForallProof(proof) = verification.proof_mut() else {
            panic!("expected ForallProof Result")
        };
        proof.domain_assumptions[0].fact_id = FactId::new(999_992);

        let error = StmtResultToLeanCompiler::new("direct_forall_domain.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("forall domain with a forged FactId must fail closed");
        assert!(error.contains("retain exact FactId"), "{error}");
    });
}

#[test]
fn direct_closed_membership_compiler_ignores_diagnostic_label_text() {
    let original = execute_closed_natural_membership();
    let original_lean = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
        .compile_stmt_results_to_lean_source(&original)
        .expect("compile original result");

    let mut renamed = execute_closed_natural_membership();
    let result = closed_natural_membership_result_mut(&mut renamed);
    let verification =
        std::rc::Rc::get_mut(&mut result.verification).expect("test result has one proof owner");
    let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
        panic!("expected builtin proof")
    };
    proof.msg = "display text is not compiler evidence".to_string();
    let renamed_lean = StmtResultToLeanCompiler::new("direct_closed_membership.lit")
        .compile_stmt_results_to_lean_source(&renamed)
        .expect("compile result after diagnostic-only change");

    assert_eq!(renamed_lean, original_lean);
}

fn execute_nonempty_set_witness() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness $is_nonempty_set({1, 2}) from 1:\n    do_nothing\n",
            "direct_nonempty_set_witness.lit",
        )
        .expect("execute nonempty-set witness")
}

fn nonempty_set_witness_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessWitnessNonemptySetResult {
    let [StmtResult::Success(SuccessStmtResult::Witness(
        SuccessWitnessStmtResult::WitnessNonemptySet(result),
    ))] = results
    else {
        panic!("expected one successful nonempty-set witness Result")
    };
    result
}

#[test]
fn direct_nonempty_set_witness_rejects_an_out_of_range_list_selection() {
    let mut results = execute_nonempty_set_witness();
    let witness = nonempty_set_witness_result_mut(&mut results);
    let membership = witness
        .verification
        .as_mut()
        .expect("witness retains verification")
        .nonempty_check
        .factual_success_mut()
        .expect("final check is factual");
    let verification = std::rc::Rc::get_mut(&mut membership.verification)
        .expect("test membership has one proof owner");
    let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
        panic!("expected builtin membership proof")
    };
    let Some(BuiltinRuleEvidence::ListSetMembership(evidence)) = proof.evidence.typed_mut() else {
        panic!("expected list-set membership evidence")
    };
    evidence.selected_index = 10;

    let error = StmtResultToLeanCompiler::new("direct_nonempty_set_witness.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("out-of-range membership evidence must fail closed");
    assert!(error.contains("out-of-range index"), "{error}");
}

#[test]
fn direct_nonempty_set_witness_ignores_membership_diagnostic_text() {
    let original = execute_nonempty_set_witness();
    let original_lean = StmtResultToLeanCompiler::new("direct_nonempty_set_witness.lit")
        .compile_stmt_results_to_lean_source(&original)
        .expect("compile original witness Result");

    let mut renamed = execute_nonempty_set_witness();
    let witness = nonempty_set_witness_result_mut(&mut renamed);
    let membership = witness
        .verification
        .as_mut()
        .expect("witness retains verification")
        .nonempty_check
        .factual_success_mut()
        .expect("final check is factual");
    let verification = std::rc::Rc::get_mut(&mut membership.verification)
        .expect("test membership has one proof owner");
    let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
        panic!("expected builtin membership proof")
    };
    proof.msg = "display-only text must not select a compiler rule".into();

    let renamed_lean = StmtResultToLeanCompiler::new("direct_nonempty_set_witness.lit")
        .compile_stmt_results_to_lean_source(&renamed)
        .expect("compile witness after diagnostic-only mutation");
    assert_eq!(renamed_lean, original_lean);
}

#[test]
fn common_zero_premise_builtin_families_compile_directly_from_results() {
    for (source, label) in [
        ("$is_nonempty_set(R)\n", "standard nonempty"),
        ("i $in C\n", "native constant"),
        ("R $subset C\n", "standard subset"),
        ("$prime(97)\n", "prime reflection"),
        ("$coprime(14, 25)\n", "coprime reflection"),
        ("$is_finite_set({1, 2})\n", "finite literal"),
        ("$is_tuple((1, 2))\n", "tuple literal shape"),
        ("not 0 $in C*\n", "closed zero nonmembership"),
    ] {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                source,
                "direct_common_builtin.lit",
            )
            .unwrap_or_else(|error| panic!("execute {label}: {error}"));
        let [result] = results.as_slice() else {
            panic!("{label} must return one statement Result")
        };
        let factual = result
            .factual_success()
            .unwrap_or_else(|| panic!("{label} must return a fact Result"));
        let proof = StmtResultToLeanCompiler::new("direct_common_builtin.lit")
            .construct_lean_proof_from_direct_fact_result(factual)
            .unwrap_or_else(|error| panic!("construct {label}: {error}"));
        assert!(proof.is_some(), "{label} still requires compatibility IR");
    }
}

#[test]
fn not_equal_symmetry_wraps_the_exact_cited_child_result() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have a, b R\ntrust a != b\nb != a\n",
            "direct_not_equal_symmetry.lit",
        )
        .expect("execute a symbolic symmetry example");
    let [objects, trusted, symmetric] = results.as_slice() else {
        panic!("expected object choice, source trust, and symmetric fact")
    };
    let mut compiler = StmtResultToLeanCompiler::new("direct_not_equal_symmetry.lit");
    compiler
        .compile_stmt_result_to_lean_source(objects)
        .expect("compile object bindings");
    compiler
        .compile_stmt_result_to_lean_source(trusted)
        .expect("compile source trust boundary");
    let factual = symmetric
        .factual_success()
        .expect("symmetry statement is factual");
    let proof = compiler
        .construct_lean_proof_from_direct_fact_result(factual)
        .expect("construct symmetry directly")
        .expect("symmetry must not use compatibility IR");
    assert!(proof.contains("Litex.Rules.notSameSymm"), "{proof}");
    assert!(proof.contains("__fact"), "{proof}");
}

#[test]
fn set_builder_membership_combines_its_ordered_child_results_directly() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "1 $in {x R: x = 1}\n",
            "direct_set_builder_membership.lit",
        )
        .expect("execute set-builder membership");
    let [result] = results.as_slice() else {
        panic!("expected one set-builder membership Result")
    };
    let result = result
        .factual_success()
        .expect("set-builder membership must be factual");
    let proof = StmtResultToLeanCompiler::new("direct_set_builder_membership.lit")
        .construct_lean_proof_from_direct_fact_result(result)
        .expect("compile direct set-builder proof")
        .expect("set-builder membership must not use compatibility IR");
    assert!(proof.contains("Litex.Rules.inSetBuilder"), "{proof}");
    let generated = StmtResultToLeanCompiler::new("direct_set_builder_membership.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile set-builder statement and typed infer Results");
    assert!(
        generated.contains("Litex.Rules.inBaseOfInSetBuilder"),
        "{generated}"
    );
    assert!(generated.contains("inSetBuilder_iff.mp"), "{generated}");
    let json = crate::output::display_stmt_result_json_v2(&results[0]);
    assert!(
        json.contains("\"rule\": \"SetBuilderBaseMembershipProjection\""),
        "{json}"
    );
    assert!(
        json.contains("\"rule\": \"SetBuilderPredicateProjection\"")
            && json.contains("\"clause_index\": 0"),
        "{json}"
    );
}

#[test]
fn set_builder_membership_rejects_a_corrupted_projection_clause_index() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "1 $in {x R: x = 1}\n",
            "corrupted_set_builder_projection.lit",
        )
        .expect("execute set-builder membership");
    let [StmtResult::Success(SuccessStmtResult::Fact(result))] = results.as_mut_slice() else {
        panic!("expected one successful set-builder membership Result")
    };
    result.store.infers.rule_applications[1].rule =
        InferRule::SetBuilderPredicateProjection { clause_index: 9 };

    let error = StmtResultToLeanCompiler::new("corrupted_set_builder_projection.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("a corrupted projection index must fail closed");
    assert!(
        error.contains("typed rule or clause order"),
        "unexpected corruption error: {error}"
    );
}

fn execute_predicate_backed_witness() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "prop has_copy(a R):\n    exist x R st {x = a}\nwitness $has_copy(2) from 2:\n    2 = 2\n",
            "direct_predicate_backed_witness.lit",
        )
        .expect("execute predicate-backed witness")
}

#[test]
fn predicate_backed_witness_rejects_a_missing_inferred_existential_fact_id() {
    let mut results = execute_predicate_backed_witness();
    let StmtResult::Success(SuccessStmtResult::Witness(
        SuccessWitnessStmtResult::WitnessAtomicFact(witness),
    )) = &mut results[1]
    else {
        panic!("expected predicate-backed witness Result")
    };
    *witness.common.infers.store_fact_outputs[0]
        .inferred_fact_ids
        .last_mut()
        .expect("witness retains existential effect") = None;

    let error = StmtResultToLeanCompiler::new("direct_predicate_backed_witness.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing existential FactId must fail closed");
    assert!(
        error.contains("inferred existential has no FactId"),
        "{error}"
    );
}

#[test]
fn arithmetic_membership_closures_publish_directly_from_recursive_results() {
    for (source, expected_theorem) in [
        ("have a, b C\na + b $in C\n", "complexAddInC"),
        ("have a, b Z\na - b $in Z\n", "complexSubInZ"),
        ("have a, b Q\na * b $in Q\n", "complexMulInQ"),
        ("have a, b N\na + b $in N\n", "complexAddInN"),
    ] {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                source,
                "direct_arithmetic_closure.lit",
            )
            .unwrap_or_else(|error| panic!("execute {expected_theorem}: {error}"));
        let [objects, fact] = results.as_slice() else {
            panic!("{expected_theorem} source must return two Results")
        };
        let mut compiler = StmtResultToLeanCompiler::new("direct_arithmetic_closure.lit");
        compiler
            .compile_stmt_result_to_lean_source(objects)
            .unwrap_or_else(|error| panic!("compile binders for {expected_theorem}: {error}"));
        compiler
            .compile_stmt_result_to_lean_source(fact)
            .unwrap_or_else(|error| panic!("compile {expected_theorem}: {error}"));
        assert!(
            compiler
                .declarations
                .iter()
                .any(|declaration| declaration.contains(expected_theorem)),
            "{expected_theorem} did not use its direct Result adapter: {:?}",
            compiler.declarations
        );
    }
}

#[test]
fn set_relation_duality_passes_through_the_exact_child_result() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "let A = R\nlet B = N\ntrust A $superset B\nB $subset A\n",
            "direct_set_relation_duality.lit",
        )
        .expect("execute set-relation duality source");
    let [set_a, set_b, _, dual] = results.as_slice() else {
        panic!("expected two set aliases, trusted premise, and dual result")
    };
    let dual = dual.factual_success().expect("duality result is factual");
    let SuccessFactProofResult::BuiltinRule(proof) = dual.proof() else {
        panic!("duality must retain builtin proof")
    };
    assert!(matches!(
        proof.evidence.typed(),
        Some(BuiltinRuleEvidence::SetRelationDuality(
            SetRelationDualityBuiltinRule::SubsetFromSuperset
        ))
    ));
    let [source_result] = proof.subgoals.as_slice() else {
        panic!("duality must retain one source Result")
    };
    let source_result = source_result
        .factual_success()
        .expect("duality source must be factual");
    let SuccessFactProofResult::StoredFactCitation(source_citation) = source_result.proof() else {
        panic!("duality source must cite the preceding relation")
    };
    let trusted_fact_id = source_citation.source_fact_id;
    let mut compiler = StmtResultToLeanCompiler::new("direct_set_relation_duality.lit");
    compiler
        .compile_stmt_result_to_lean_source(set_a)
        .expect("compile first set alias");
    compiler
        .compile_stmt_result_to_lean_source(set_b)
        .expect("compile second set alias");
    compiler
        .environment_stack
        .fact_names
        .insert(trusted_fact_id, "__fact0".to_string());
    compiler
        .environment_stack
        .fact_propositions
        .insert(trusted_fact_id, source_result.fact());
    let proof = compiler
        .construct_lean_proof_from_direct_fact_result(dual)
        .expect("compile typed duality")
        .expect("duality must not use compatibility IR");
    assert!(proof.contains("__fact"), "{proof}");
}

#[test]
fn explicit_source_axiom_preserves_its_name_and_fact_id() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "axiom source_reflexivity:\n    ? forall x R:\n        x = x\n",
            "direct_source_axiom.lit",
        )
        .expect("execute explicit source axiom");
    let generated = StmtResultToLeanCompiler::new("direct_source_axiom.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile explicit source axiom");
    assert!(
        generated.contains("axiom source_reflexivity"),
        "{generated}"
    );
    assert!(!generated.contains("sorry"), "{generated}");
}

fn rename_object_choice_nonempty_diagnostic_label(results: &mut [StmtResult]) {
    let Some(StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveObjInNonemptySetStmt(choice),
    ))) = results.first_mut()
    else {
        panic!("expected object-choice statement result")
    };
    let verification = choice
        .verification
        .as_mut()
        .expect("object choice retains verification result");
    let nonempty = verification.groups[0]
        .nonempty_check
        .as_deref_mut()
        .expect("standard carrier retains nonempty check");
    let factual = nonempty
        .factual_success_mut()
        .expect("nonempty check is factual");
    let verification = std::rc::Rc::get_mut(&mut factual.verification)
        .expect("test nonempty result has one proof owner");
    let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
        panic!("expected standard-set builtin proof")
    };
    proof.msg = "diagnostic label is not semantic input".into();
}

#[test]
fn direct_object_choice_compiler_uses_typed_child_evidence_not_its_label() {
    const SOURCE: &str = "have chosen R\nchosen $in R\n";
    let original = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            SOURCE,
            "direct_object_choice.lit",
        )
        .expect("execute object choice");
    let original_lean = StmtResultToLeanCompiler::new("direct_object_choice.lit")
        .compile_stmt_results_to_lean_source(&original)
        .expect("compile object choice");

    let mut renamed = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            SOURCE,
            "direct_object_choice.lit",
        )
        .expect("execute object choice again");
    rename_object_choice_nonempty_diagnostic_label(&mut renamed);
    let renamed_lean = StmtResultToLeanCompiler::new("direct_object_choice.lit")
        .compile_stmt_results_to_lean_source(&renamed)
        .expect("compile object choice after diagnostic-only mutation");

    assert_eq!(renamed_lean, original_lean);
    assert!(original_lean.contains("Classical.choice (Litex.Rules.realNonempty)"));
    assert!(original_lean.contains("Litex.In.own Litex.R chosen"));
}

fn execute_single_existential_witness() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\n",
            "direct_existential_witness.lit",
        )
        .expect("execute one-witness existential introduction")
}

fn single_existential_witness_result_mut(
    results: &mut [StmtResult],
) -> &mut SuccessWitnessExistFactResult {
    let [StmtResult::Success(SuccessStmtResult::Witness(
        SuccessWitnessStmtResult::WitnessExistFact(result),
    ))] = results
    else {
        panic!("expected one successful existential-witness result")
    };
    result
}

#[test]
fn existential_witness_compiles_directly_from_named_recursive_children() {
    let mut results = execute_single_existential_witness();
    let result = single_existential_witness_result_mut(&mut results);
    let local_fact_id = result
        .verification
        .as_ref()
        .expect("witness retains verification")
        .proof_steps[0]
        .factual_success()
        .expect("witness proof step is factual")
        .store
        .fact_id
        .expect("witness proof step retains its local FactId");
    let outer_fact_id = result.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("witness outer store retains its FactId");

    let mut compiler = StmtResultToLeanCompiler::new("direct_existential_witness.lit");
    assert!(compiler
        .compile_witness_exist_fact_stmt_result_to_lean_source(result)
        .expect("direct existential-witness compilation succeeds"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&local_fact_id));
    assert_eq!(
        compiler.environment_stack.fact_names.get(&outer_fact_id),
        Some(&"__fact0".to_string())
    );
    assert!(
        compiler.declarations[0].contains("∃ (x : ℂ), Litex.In x Litex.R ∧ Litex.Same x (1 : ℂ)")
    );
    assert!(compiler.declarations[0].contains("have __step1"));
    assert!(compiler.declarations[0].contains("⟨(1 : ℂ)"));
}

#[test]
fn existential_witness_rejects_a_missing_parameter_check_child() {
    let mut results = execute_single_existential_witness();
    let result = single_existential_witness_result_mut(&mut results);
    result
        .verification
        .as_mut()
        .expect("witness retains verification")
        .parameter_checks[0] = None;

    let error = StmtResultToLeanCompiler::new("direct_existential_witness.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing parameter child must fail closed");
    assert!(error.contains("has no parameter-check child Result"));
}

#[test]
fn existential_witness_rejects_a_missing_outer_fact_id() {
    let mut results = execute_single_existential_witness();
    let result = single_existential_witness_result_mut(&mut results);
    result.common.infers.store_fact_outputs[0].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_existential_witness.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing outer FactId must fail closed");
    assert!(error.contains("existential witness outer effect store has no FactId"));
}

#[test]
fn existential_elimination_uses_source_and_projection_fact_ids_directly() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\n",
            "direct_existential_elimination.lit",
        )
        .expect("execute existential introduction and elimination");
    let [StmtResult::Success(SuccessStmtResult::Witness(
        SuccessWitnessStmtResult::WitnessExistFact(witness),
    )), StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::ObtainObjFromExistFact(elimination),
    ))] = results.as_slice()
    else {
        panic!("expected witness followed by existential elimination")
    };
    let source_fact_id = witness.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("witness retains source FactId");
    let source_citation = elimination
        .verification
        .as_ref()
        .expect("elimination retains verification")
        .source_result
        .factual_success()
        .expect("elimination source is factual");
    let SuccessFactProofResult::StoredFactCitation(source_citation) = source_citation.proof()
    else {
        panic!("elimination source cites the stored existential")
    };
    assert_eq!(source_citation.source_fact_id, source_fact_id);

    let mut compiler = StmtResultToLeanCompiler::new("direct_existential_elimination.lit");
    assert!(compiler
        .compile_witness_exist_fact_stmt_result_to_lean_source(witness)
        .expect("compile direct existential introduction"));
    assert!(compiler
        .compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(elimination)
        .expect("compile direct existential elimination"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(compiler.declarations[1].contains("noncomputable def y : ℂ := Classical.choose"));
    assert!(compiler.declarations[1].contains("from __fact0"));
    assert!(compiler.declarations[2].contains("Classical.choose_spec"));
    assert!(compiler.declarations[2].contains("from __fact0"));
    assert!(compiler.declarations[2].contains(").1"));
    assert!(compiler.declarations[3].contains("Classical.choose_spec"));
    assert!(compiler.declarations[3].contains("from __fact0"));
    assert!(compiler.declarations[3].contains(").2"));
}

#[test]
fn existential_elimination_rejects_a_projection_without_fact_id() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "witness exist x R st {x = 1} from 1:\n    1 = 1\nobtain y from exist x R st {x = 1}\n",
            "direct_existential_elimination.lit",
        )
        .expect("execute existential introduction and elimination");
    let StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::ObtainObjFromExistFact(elimination),
    )) = &mut results[1]
    else {
        panic!("expected existential elimination")
    };
    elimination.common.infers.store_fact_outputs[1].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_existential_elimination.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("projection without FactId must fail closed");
    assert!(error.contains("existential elimination projections store 1"));
}

fn execute_predicate_backed_existential_elimination() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "prop has_copy(a R):\n    exist x R st {x = a}\nwitness exist x R st {x = 2} from 2:\n    2 = 2\nby def $has_copy(2)\nobtain copy from $has_copy(2)\n",
            "direct_predicate_backed_existential_elimination.lit",
        )
        .expect("execute predicate-backed existential elimination")
}

#[test]
fn predicate_backed_existential_elimination_compiles_definition_projection_directly() {
    let results = execute_predicate_backed_existential_elimination();
    let [definition, witness, by_definition, StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::ObtainObjFromAtomicFact(elimination),
    ))] = results.as_slice()
    else {
        panic!("expected predicate definition, witness, by-definition, and obtain")
    };

    let mut compiler =
        StmtResultToLeanCompiler::new("direct_predicate_backed_existential_elimination.lit");
    for result in [definition, witness, by_definition] {
        compiler
            .compile_stmt_result_to_lean_source(result)
            .expect("compile prerequisite Result directly");
    }
    assert!(compiler
        .compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(elimination)
        .expect("compile predicate-backed elimination directly"));
    assert!(compiler
        .declarations
        .iter()
        .any(|declaration| declaration.contains("unfold has_copy at __definition")));
    assert!(compiler
        .declarations
        .iter()
        .any(|declaration| declaration.contains("noncomputable def copy")));
}

#[test]
fn predicate_backed_existential_elimination_rejects_a_retargeted_source_publication() {
    let mut results = execute_predicate_backed_existential_elimination();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(by_definition))) =
        &mut results[2]
    else {
        panic!("expected by-definition prerequisite")
    };
    let source_fact_id = by_definition.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("by-definition retains source FactId");
    by_definition.common.infers.store_fact_outputs[0].fact_id =
        Some(FactId::new(source_fact_id.value() + 10_000));

    let mut compiler =
        StmtResultToLeanCompiler::new("direct_predicate_backed_existential_elimination.lit");
    for result in &results[..2] {
        compiler
            .compile_stmt_result_to_lean_source(result)
            .expect("compile prerequisites before the corrupted publication");
    }
    let error = compiler
        .compile_stmt_result_to_lean_source(&results[2])
        .expect_err("retargeting the source publication must fail at its typed infer edge");
    assert!(
        error.contains(&format!("unavailable cited fact `{source_fact_id}`")),
        "{error}"
    );
}

fn execute_direct_cases_and_contradiction() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "by cases:\n    ? 2 = 2\n    case 1 = 1 and 2 = 2:\n        1 = 1\nby contra:\n    ? not 2 < 1\n    impossible 2 < 1\n",
            "direct_cases_and_contradiction.lit",
        )
        .expect("execute direct cases and contradiction")
}

#[test]
fn cases_and_contradiction_compile_directly_in_nested_environments() {
    let results = execute_direct_cases_and_contradiction();
    let [StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(cases))), StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(
        contradiction,
    )))] = results.as_slice()
    else {
        panic!("expected cases followed by contradiction")
    };
    let branch = &cases
        .verification
        .as_ref()
        .expect("cases retains verification")
        .branches[0];
    let branch_assumption_fact_id = branch.assumption_fact_id;
    let branch_component_fact_ids = branch
        .proof_scope
        .assumption_components
        .iter()
        .map(|(fact_id, _)| *fact_id)
        .collect::<Vec<_>>();
    let reverse_assumption_fact_id = contradiction
        .verification
        .as_ref()
        .expect("contra retains verification")
        .reverse_assumption_fact_id;

    let mut compiler = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit");
    let coverage = cases
        .verification
        .as_ref()
        .expect("cases retains verification")
        .coverage_check
        .factual_success()
        .expect("coverage is factual");
    assert!(
        compiler
            .construct_lean_proof_from_direct_fact_result(coverage)
            .expect("construct coverage proof")
            .is_some(),
        "coverage proof remained unsupported: {:?}",
        coverage.proof()
    );
    assert!(compiler
        .compile_by_cases_stmt_result_to_lean_source(cases)
        .expect("compile cases directly"));
    assert!(compiler
        .compile_by_contra_stmt_result_to_lean_source(contradiction)
        .expect("compile contradiction directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&branch_assumption_fact_id));
    assert!(branch_component_fact_ids
        .iter()
        .all(|fact_id| !compiler.environment_stack.fact_names.contains_key(fact_id)));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&reverse_assumption_fact_id));
    assert!(compiler.declarations[0].contains("have __case1_component1"));
    assert!(compiler.declarations[0].contains("have __case1_component2"));
    assert!(compiler.declarations[1].contains("Classical.byContradiction"));
}

#[test]
fn cases_and_contradiction_tracer_compiles_from_recursive_results() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/lean/examples/9_CasesAndContradiction.lit"
    ));
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            source,
            "9_CasesAndContradiction.lit",
        )
        .expect("execute cases-and-contradiction tracer");
    let lean_source = StmtResultToLeanCompiler::new("9_CasesAndContradiction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile recursive cases-and-contradiction Results");
    assert!(lean_source.contains("__case1_component1"));
    assert!(lean_source.contains("Classical.byContradiction"));
}

#[test]
fn cases_reject_a_branch_assumption_fact_id_mismatch() {
    let mut results = execute_direct_cases_and_contradiction();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(cases))) =
        &mut results[0]
    else {
        panic!("expected cases result")
    };
    let exported_fact_id = cases.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("cases exports a FactId");
    cases
        .verification
        .as_mut()
        .expect("cases retains verification")
        .branches[0]
        .assumption_fact_id = exported_fact_id;

    let error = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("mismatched branch FactId must fail closed");
    assert!(error.contains("branch assumption FactIds disagree"));
}

#[test]
fn contradiction_rejects_a_reverse_assumption_fact_id_mismatch() {
    let mut results = execute_direct_cases_and_contradiction();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByContraStmt(
        contradiction,
    ))) = &mut results[1]
    else {
        panic!("expected contradiction result")
    };
    let exported_fact_id = contradiction.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("contradiction exports a FactId");
    contradiction
        .verification
        .as_mut()
        .expect("contradiction retains verification")
        .reverse_assumption_fact_id = exported_fact_id;

    let error = StmtResultToLeanCompiler::new("direct_cases_and_contradiction.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("mismatched reverse FactId must fail closed");
    assert!(error.contains("reverse-assumption FactIds disagree"));
}

fn execute_ordinary_claim() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "claim:\n    ? 2 = 2\n    2 = 2\n",
            "direct_claim.lit",
        )
        .expect("execute ordinary claim")
}

fn ordinary_claim_result_mut(results: &mut [StmtResult]) -> &mut SuccessClaimStmtResult {
    let [StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(
        result,
    )))] = results
    else {
        panic!("expected one successful claim result")
    };
    result
}

#[test]
fn local_claim_proof_step_store_keeps_its_local_fact_id_after_outer_store() {
    let mut results = execute_ordinary_claim();
    let claim = ordinary_claim_result_mut(&mut results);
    let outer_fact_id = claim.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("claim outer store has a FactId");
    let Some(SuccessVerifyClaimResult::Fact(verification)) = &claim.verification else {
        panic!("ordinary claim retains ordinary-fact verification")
    };
    let local = verification.proof_steps[0]
        .factual_success()
        .expect("claim proof step is factual");
    let local_fact_id = local
        .store
        .fact_id
        .expect("local proof step has a frozen FactId");

    assert_ne!(local_fact_id, outer_fact_id);
    assert_eq!(
        local.store.infers.store_fact_outputs[0].fact_id,
        Some(local_fact_id)
    );
    let SuccessFactProofResult::StoredFactCitation(citation) = verification
        .conclusion_check
        .factual_success()
        .expect("claim conclusion is factual")
        .proof()
    else {
        panic!("claim conclusion cites its local proof step")
    };
    assert_eq!(citation.source_fact_id, local_fact_id);
}

#[test]
fn ordinary_claim_and_example_compile_directly_from_recursive_results() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "claim:\n    ? 2 = 2\n    2 = 2\n\nexample:\n    ? 3 = 3\n    3 = 3\n",
            "direct_claim_and_example.lit",
        )
        .expect("execute claim and example");
    let [StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(
        claim,
    ))), StmtResult::Success(SuccessStmtResult::ProofBlock(
        SuccessProofBlockStmtResult::ExampleStmt(example),
    ))] = results.as_slice()
    else {
        panic!("expected claim and example results")
    };

    let mut compiler = StmtResultToLeanCompiler::new("direct_claim_and_example.lit");
    assert!(compiler
        .compile_claim_stmt_result_to_lean_source(claim)
        .expect("direct claim compilation succeeds"));
    assert!(compiler
        .compile_example_stmt_result_to_lean_source(example)
        .expect("direct example compilation succeeds"));
    assert!(compiler.declarations[0].contains("theorem __fact0"));
    assert!(compiler.declarations[0].contains("have __step1"));
    assert!(compiler.declarations[0].contains("exact __step1"));
    assert!(compiler.declarations[1].starts_with("example :"));
    assert!(compiler.declarations[1].contains("have __step1"));
}

#[test]
fn direct_claim_compiler_rejects_a_local_store_retargeted_to_the_outer_fact_id() {
    let mut results = execute_ordinary_claim();
    let claim = ordinary_claim_result_mut(&mut results);
    let outer_fact_id = claim.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("claim outer store has a FactId");
    let Some(SuccessVerifyClaimResult::Fact(verification)) = &mut claim.verification else {
        panic!("ordinary claim retains ordinary-fact verification")
    };
    verification.proof_steps[0]
        .factual_success_mut()
        .expect("claim proof step is factual")
        .store
        .infers
        .store_fact_outputs[0]
        .fact_id = Some(outer_fact_id);

    let error = StmtResultToLeanCompiler::new("direct_claim.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("retargeted local store must fail closed");
    assert!(error.contains("local proof-step store does not retain its exact FactId"));
}

fn execute_zero_binder_named_theorem() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm one_eq_one:\n    ? forall:\n        1 = 1\n",
            "direct_zero_binder_theorem.lit",
        )
        .expect("execute zero-binder named theorem")
}

fn named_theorem_result_mut(results: &mut [StmtResult]) -> &mut SuccessDefThmStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefThmStmt(result))] = results else {
        panic!("expected one successful named-theorem result")
    };
    result
}

#[test]
fn zero_binder_named_theorem_compiles_directly_from_recursive_result() {
    let mut results = execute_zero_binder_named_theorem();
    let theorem = named_theorem_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit");

    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("direct zero-binder theorem compilation succeeds"));
    assert_eq!(compiler.declarations.len(), 1);
    assert!(compiler.declarations[0].starts_with("theorem one_eq_one :"));
    assert!(compiler.declarations[0].contains("have __c0_0"));
    assert!(compiler.declarations[0].contains("exact __c0_0"));
}

#[test]
fn zero_binder_named_theorem_compiler_ignores_conclusion_diagnostic_label() {
    let original = execute_zero_binder_named_theorem();
    let original_lean = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
        .compile_stmt_results_to_lean_source(&original)
        .expect("compile original zero-binder theorem");

    let mut renamed = execute_zero_binder_named_theorem();
    let theorem = named_theorem_result_mut(&mut renamed);
    let conclusion = theorem
        .verification
        .as_mut()
        .expect("named theorem retains verification")
        .conclusion_checks[0]
        .factual_success_mut()
        .expect("named theorem conclusion is factual");
    let verification = std::rc::Rc::get_mut(&mut conclusion.verification)
        .expect("test conclusion has one proof owner");
    let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
        panic!("expected builtin conclusion proof")
    };
    proof.msg = "diagnostic-only theorem conclusion label".into();

    let renamed_lean = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
        .compile_stmt_results_to_lean_source(&renamed)
        .expect("compile theorem after diagnostic-only mutation");
    assert_eq!(renamed_lean, original_lean);
}

#[test]
fn zero_binder_named_theorem_compiler_rejects_missing_outer_fact_id() {
    let mut results = execute_zero_binder_named_theorem();
    let theorem = named_theorem_result_mut(&mut results);
    theorem.common.infers.store_fact_outputs[0].fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_zero_binder_theorem.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("theorem without its frozen outer FactId must fail closed");
    assert!(
        error.contains("named forall outer store has no FactId"),
        "{error}"
    );
}

#[test]
fn standard_set_binder_named_theorem_compiles_in_a_child_environment() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm local_reflexivity:\n    ? forall x R:\n        x = x\n    x = x\n",
            "direct_binder_theorem.lit",
        )
        .expect("execute standard-set binder theorem");
    let theorem = named_theorem_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_binder_theorem.lit");

    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("direct binder theorem compilation succeeds"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(compiler.declarations[0].contains("∀ (x : ℂ)"));
    assert!(compiler.declarations[0].contains("(__h0_1 : Litex.In x Litex.R)"));
    assert!(compiler.declarations[0].contains("intro x __h0_1"));
    assert!(compiler.declarations[0].contains("have __step1"));
    assert!(compiler.declarations[0].contains("exact __c0_0"));
}

#[test]
fn existential_theorem_compiles_nested_witness_in_two_child_environments() {
    let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm member_has_witness:\n    ? forall S set, a S:\n        exist x S st {x = a}\n    witness exist x S st {x = a} from a:\n        a = a\n",
            "direct_existential_theorem.lit",
        )
        .expect("execute theorem with a nested existential witness");
    let theorem = named_theorem_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_existential_theorem.lit");

    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("direct existential theorem compilation succeeds"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 1);
    assert!(compiler.declarations[0].contains("∀ (S : Litex.Set)"));
    assert!(compiler.declarations[0].contains("{__carrier0_2 : Type}"));
    assert!(compiler.declarations[0].contains("(a : __carrier0_2)"));
    assert!(compiler.declarations[0].contains("have __step1 : ∃"));
    assert!(compiler.declarations[0].contains("have __step1 : Litex.Same a a"));
    assert!(compiler.declarations[0].contains("⟨_, a, (__h0_2), (__step1)⟩"));
    assert!(compiler.declarations[0].contains("exact __c0_0"));
}

fn execute_named_theorem_and_instantiation() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm local_reflexivity:\n    ? forall x R:\n        x = x\n    x = x\n\nby thm local_reflexivity(1)\n",
            "direct_theorem_instantiation.lit",
        )
        .expect("execute named theorem and its instantiation")
}

fn theorem_instantiation_result_mut(results: &mut [StmtResult]) -> &mut SuccessByThmStmtResult {
    let [_, StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(result)))] =
        results
    else {
        panic!("expected a named theorem followed by by-thm")
    };
    result
}

#[test]
fn by_thm_uses_the_exact_source_fact_id_and_argument_check_result() {
    let results = execute_named_theorem_and_instantiation();
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(by_theorem))) =
        &results[1]
    else {
        panic!("second Result is by-thm")
    };
    let source_fact_id = by_theorem
        .verification
        .as_ref()
        .expect("by-thm retains verification")
        .source_fact_id
        .expect("by-thm retains its source theorem FactId");
    let json = crate::output::display_stmt_result_json_v2(&results[1]);
    assert!(json.contains(&format!("\"source_fact_id\": \"{source_fact_id}\"")));

    let lean = StmtResultToLeanCompiler::new("direct_theorem_instantiation.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile theorem and exact-FactId instantiation");

    assert!(lean.contains("theorem local_reflexivity :"));
    assert!(lean.contains("theorem __fact1 : Litex.Same (1 : ℂ) (1 : ℂ)"));
    assert!(lean.contains("local_reflexivity (1 : ℂ)"));
    assert!(lean.contains("Litex.Rules.complexRealInR (1 : ℝ)"));
}

#[test]
fn by_thm_rejects_a_missing_source_theorem_fact_id() {
    let mut results = execute_named_theorem_and_instantiation();
    theorem_instantiation_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("by-thm retains verification")
        .source_fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_theorem_instantiation.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("by-thm without its source FactId must fail closed");
    assert!(error.contains("by-thm Result has no source theorem FactId"));
}

#[test]
fn theorem_backed_obtain_consumes_but_does_not_publish_its_local_conclusion() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "thm self_exists:\n    ? forall a R:\n        exist x R st {x = a}\n    witness exist x R st {x = a} from a:\n        a = a\nobtain selected from thm self_exists(3)\n",
            "direct_theorem_backed_obtain.lit",
        )
        .expect("execute theorem-backed obtain");
    let [StmtResult::Success(SuccessStmtResult::DefThmStmt(theorem)), StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::ObtainObjFromThm(obtain),
    ))] = results.as_slice()
    else {
        panic!("expected theorem followed by theorem-backed obtain")
    };
    let source = obtain
        .verification
        .as_ref()
        .expect("obtain retains elimination verification")
        .source_result
        .non_factual_success()
        .expect("obtain source is a statement Result");
    let SuccessStmtResult::By(SuccessByStmtResult::ByThmStmt(application)) = source else {
        panic!("obtain source is a by-thm Result")
    };
    assert_eq!(
        application.common.infers.store_fact_outputs[0].fact_id, None,
        "the temporary theorem conclusion is not publishable after its local environment pops"
    );
    let theorem_fact_id = theorem.common.infers.store_fact_outputs[0]
        .fact_id
        .expect("named theorem retains its published FactId");
    let projection_fact_ids = obtain
        .common
        .infers
        .store_fact_outputs
        .iter()
        .map(|output| output.fact_id.expect("projection retains FactId"))
        .collect::<Vec<_>>();

    let mut compiler = StmtResultToLeanCompiler::new("direct_theorem_backed_obtain.lit");
    assert!(compiler
        .compile_named_theorem_stmt_result_to_lean_source(theorem)
        .expect("compile source theorem"));
    assert!(compiler
        .compile_obtain_obj_from_theorem_stmt_result_to_lean_source(obtain)
        .expect("compile theorem-backed obtain"));
    assert_eq!(compiler.environment_stack.fact_names.len(), 3);
    assert!(compiler
        .environment_stack
        .fact_names
        .contains_key(&theorem_fact_id));
    for fact_id in projection_fact_ids {
        assert!(compiler.environment_stack.fact_names.contains_key(&fact_id));
    }
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[1].contains("noncomputable def selected"));
}

fn execute_concrete_predicate_and_by_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "prop is_unit_pair(x R, y R):\n    x = 1\n    y = 1\n\n1 = 1\nby def $is_unit_pair(1, 1)\n",
            "direct_by_definition.lit",
        )
        .expect("execute concrete predicate and by-definition")
}

fn by_definition_result_mut(results: &mut [StmtResult]) -> &mut SuccessByDefStmtResult {
    let [_, _, StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(result)))] =
        results
    else {
        panic!("expected concrete predicate, fact, and by-definition Results")
    };
    result
}

#[test]
fn by_definition_combines_parameter_and_clause_results_directly() {
    let results = execute_concrete_predicate_and_by_definition();
    let mut compiler = StmtResultToLeanCompiler::new("direct_by_definition.lit");
    let StmtResult::Success(SuccessStmtResult::DefPredicateStmt(
        SuccessDefPredicateStmtResult::DefPropStmt(definition),
    )) = &results[0]
    else {
        panic!("first Result is a concrete predicate definition")
    };
    let StmtResult::Success(SuccessStmtResult::Fact(fact)) = &results[1] else {
        panic!("second Result is the reusable clause fact")
    };
    let StmtResult::Success(SuccessStmtResult::By(SuccessByStmtResult::ByDefStmt(by_definition))) =
        &results[2]
    else {
        panic!("third Result is by-definition")
    };

    compiler
        .compile_def_prop_stmt_result_to_lean_source(definition)
        .expect("compile concrete predicate directly");
    compiler
        .compile_fact_stmt_result_to_lean_source(fact)
        .expect("compile reusable clause fact directly");
    assert!(compiler
        .compile_by_definition_stmt_result_to_lean_source(by_definition)
        .expect("compile by-definition directly"));
    assert!(compiler.declarations[2].contains("unfold is_unit_pair"));
    assert!(compiler.declarations[2].contains(
            "exact ⟨Litex.Rules.complexRealInR (1 : ℝ), Litex.Rules.complexRealInR (1 : ℝ), __fact0, __fact0⟩"
        ));
}

#[test]
fn by_definition_rejects_a_missing_clause_child_result() {
    let mut results = execute_concrete_predicate_and_by_definition();
    by_definition_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("by-definition retains verification")
        .clause_checks
        .pop();

    let error = StmtResultToLeanCompiler::new("direct_by_definition.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing clause child must fail closed");
    assert!(error.contains("changed its component arity"));
}

#[test]
fn by_definition_rejects_a_missing_target_fact_id() {
    let mut results = execute_concrete_predicate_and_by_definition();
    by_definition_result_mut(&mut results)
        .common
        .infers
        .store_fact_outputs[0]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_by_definition.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("by-definition target without FactId must fail closed");
    assert!(error.contains("by-definition target store has no FactId"));
}

fn execute_named_real_function(source: &str) -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            source,
            "direct_named_real_function.lit",
        )
        .expect("execute named real function")
}

fn named_real_function_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveFnEqualStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnEqualStmt(result),
    ))] = results
    else {
        panic!("expected one named-function Result")
    };
    result
}

#[test]
fn named_real_function_compiles_return_check_in_child_environment() {
    let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\n");
    let result = named_real_function_result_mut(&mut results);
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("defining equality retains FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");

    assert!(compiler
        .compile_have_fn_equal_stmt_result_to_lean_source(result)
        .expect("compile named real function directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 3);
    assert!(compiler.declarations[0].contains("noncomputable def inc : Litex.Fn"));
    assert!(compiler.declarations[0].contains("Litex.In.rep __arg __arg_in + (1 : ℝ)"));
    let binding = compiler
        .environment_stack
        .named_function_definitions
        .get(&defining_equality_fact_id)
        .expect("direct function publishes its reduction binding");
    assert!(binding.uses_native_real_body);
}

#[test]
fn checked_named_function_reduction_uses_its_exact_definition_fact_id() {
    let results = execute_named_real_function("have fn inc(x R) R = x + 1\ninc(2) = 2 + 1\n");
    let reduction_result = results[1]
        .factual_success()
        .expect("second statement is a factual reduction");
    let SuccessFactProofResult::CheckedFunctionDefinitionReduction(reduction) =
        reduction_result.proof()
    else {
        panic!("checked definition reduction must retain typed evidence")
    };
    let StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnEqualStmt(definition),
    )) = &results[0]
    else {
        panic!("first statement is the named-function definition")
    };
    assert_eq!(
        Some(reduction.verification.defining_equality_fact_id),
        definition.common.infers.store_fact_outputs[1].fact_id
    );

    let lean = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect("compile checked function reduction directly");
    assert!(lean.contains("unfold Litex.fnApplyOwn inc"));
}

#[test]
fn checked_named_function_reduction_rejects_a_wrong_definition_fact_id() {
    let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\ninc(2) = 2 + 1\n");
    let StmtResult::Success(SuccessStmtResult::Fact(reduction_result)) = &mut results[1] else {
        panic!("second statement is a factual reduction")
    };
    let wrong_fact_id = reduction_result
        .store
        .fact_id
        .expect("outer reduction result retains a FactId");
    let verification = std::rc::Rc::get_mut(&mut reduction_result.verification)
        .expect("executed Result uniquely owns its verification in this corruption test");
    let SuccessFactProofResult::CheckedFunctionDefinitionReduction(reduction) =
        verification.proof_mut()
    else {
        panic!("checked definition reduction must retain typed evidence")
    };
    reduction.verification.defining_equality_fact_id = wrong_fact_id;

    let error = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("wrong defining FactId must fail closed");
    assert!(error.contains("unavailable cited fact"), "{error}");
}

#[test]
fn checked_named_function_reduction_inside_forall_uses_wd_scope_fact_ids() {
    let results = execute_named_real_function(
            "have fn reciprocal(x R: x != 0) R = 1 / x\nforall a R:\n    a != 0\n    =>:\n        reciprocal(a) = 1 / a\n",
        );
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnEqualStmt(definition),
    )), StmtResult::Success(SuccessStmtResult::Fact(forall_result))] = results.as_slice()
    else {
        panic!("expected a function definition and one forall Result")
    };
    let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");
    assert!(compiler
        .compile_have_fn_equal_stmt_result_to_lean_source(definition)
        .expect("compile domain-constrained function definition directly"));
    assert!(compiler
        .compile_direct_forall_fact_result(forall_result)
        .expect("compile checked reduction under the forall Result environment"));
    assert!(compiler.declarations.last().is_some_and(|declaration| {
        declaration.contains("unfold Litex.fnApplyWhereOwn reciprocal")
            && declaration.contains("__domain1")
            && declaration.contains("Litex.Same.realComplex ((Litex.In.rep a ")
            && !declaration.contains("Litex.Same.symm (Litex.In.same_rep a (__h8_1))")
    }));
}

#[test]
fn named_real_function_domain_fact_stays_inside_function_binder() {
    let mut results = execute_named_real_function("have fn reciprocal(x R: x != 0) R = 1 / x\n");
    let result = named_real_function_result_mut(&mut results);
    let mut compiler = StmtResultToLeanCompiler::new("direct_named_real_function.lit");

    assert!(compiler
        .compile_have_fn_equal_stmt_result_to_lean_source(result)
        .expect("compile domain-constrained real function directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert!(compiler.declarations[0].contains("Litex.FnWhere"));
    assert!(compiler.declarations[0].contains("__arg_domain"));
    assert!(compiler
        .environment_stack
        .fact_propositions
        .values()
        .all(|fact| fact.to_string() != "x != 0"));
}

#[test]
fn named_real_function_rejects_missing_local_parameter_fact_id() {
    let mut results = execute_named_real_function("have fn inc(x R) R = x + 1\n");
    named_real_function_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("function retains verification")
        .assumption_infers
        .store_fact_outputs[0]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_named_real_function.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("missing local parameter FactId must fail closed");
    assert!(error.contains("named real function local assumptions store 0"));
    assert!(error.contains("has no FactId"));
}

fn execute_indexed_tuple_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have tuple coordinates for index <= 3, coordinates[index] = index + 1\n",
            "direct_indexed_tuple.lit",
        )
        .expect("execute indexed tuple definition")
}

fn indexed_tuple_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveTupleStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveTupleStmt(
        result,
    )))] = results
    else {
        panic!("expected one indexed tuple Result")
    };
    result
}

#[test]
fn indexed_tuple_compiles_value_well_definedness_in_child_environment() {
    let mut results = execute_indexed_tuple_definition();
    let result = indexed_tuple_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("indexed tuple retains combined verification");
    match verification.value_well_definedness.as_ref() {
        SuccessVerifyObjWellDefinedResult::Direct(value) => {
            assert_eq!(
                obj_equality_key(&value.object),
                obj_equality_key(&result.statement.value)
            );
        }
        other => panic!("expected direct tuple value WD Result, found {other:?}"),
    }
    let mut compiler = StmtResultToLeanCompiler::new("direct_indexed_tuple.lit");

    assert!(compiler
        .compile_have_tuple_stmt_result_to_lean_source(result)
        .expect("compile indexed tuple directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 6);
    assert!(
        compiler.declarations[2].contains("noncomputable def coordinates : Litex.IndexedTuple 3 ℂ")
    );
    assert!(compiler.declarations[2].contains("__index.val"));
    assert!(compiler.declarations[2].contains("+ (1 : ℂ)"));
    assert!(compiler.declarations[5].contains("∀ {__tuple_index_carrier : Type}"));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.index_binding.id()));
}

#[test]
fn indexed_tuple_rejects_a_coordinate_store_without_fact_id() {
    let mut results = execute_indexed_tuple_definition();
    indexed_tuple_result_mut(&mut results)
        .common
        .infers
        .store_fact_outputs[2]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_indexed_tuple.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("coordinate store without a FactId must fail closed");
    assert!(error.contains("lost its FactId"));
}

fn execute_indexed_sequence_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have seq identity_sequence seq(R) for index, identity_sequence(index) = index + 1\n",
            "direct_indexed_sequence.lit",
        )
        .expect("execute indexed sequence definition")
}

fn indexed_sequence_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveSeqStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveSeqStmt(
        result,
    )))] = results
    else {
        panic!("expected one indexed sequence Result")
    };
    result
}

#[test]
fn indexed_sequence_compiles_return_check_in_its_index_environment() {
    let mut results = execute_indexed_sequence_definition();
    let result = indexed_sequence_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("sequence retains combined verification");
    let parameter_fact_id = verification.assumption_infers.store_fact_outputs[0]
        .fact_id
        .expect("sequence index membership retains its local FactId");
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("sequence equality retains its outer FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_indexed_sequence.lit");

    assert!(compiler
        .compile_have_sequence_stmt_result_to_lean_source(result)
        .expect("compile indexed sequence directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[0]
        .contains("noncomputable def identity_sequence : Litex.Fn Litex.NPos Litex.R"));
    assert!(compiler.declarations[0].contains("(Litex.In.rep __arg __arg_in).val : ℕ"));
    assert!(compiler.declarations[0].contains("+ (1 : ℝ)"));
    assert!(compiler.declarations[1].contains("Litex.sequenceSet Litex.R"));
    assert!(compiler.declarations[2].contains("Litex.fnSet Litex.NPos Litex.R"));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.index_binding.id()));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&parameter_fact_id));
    assert!(compiler
        .environment_stack
        .named_function_definitions
        .contains_key(&defining_equality_fact_id));
}

#[test]
fn indexed_sequence_rejects_a_missing_local_parameter_fact_id() {
    let mut results = execute_indexed_sequence_definition();
    indexed_sequence_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("sequence retains verification")
        .assumption_infers
        .store_fact_outputs[0]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_indexed_sequence.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("sequence index without a local FactId must fail closed");
    assert!(error.contains("sequence index parameter store has no FactId"));
}

fn execute_finite_sequence_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have finite_seq bounded_sequence finite_seq(R, 3) for index <= 3, bounded_sequence(index) = index + 1\nbounded_sequence(2) = 2 + 1\n",
            "direct_finite_sequence.lit",
        )
        .expect("execute finite-sequence definition and application")
}

fn finite_sequence_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveFiniteSeqStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFiniteSeqStmt(result),
    )), _] = results
    else {
        panic!("expected a finite-sequence definition followed by an application fact")
    };
    result
}

#[test]
fn finite_sequence_compiles_bound_scope_and_application_from_recursive_results() {
    let mut results = execute_finite_sequence_definition();
    let result = finite_sequence_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("finite sequence retains combined verification");
    assert_eq!(verification.bound_checks.len(), 2);
    assert_eq!(verification.assumption_infers.store_fact_outputs.len(), 2);
    let parameter_fact_id = verification.assumption_infers.store_fact_outputs[0]
        .fact_id
        .expect("finite-sequence parameter membership retains its local FactId");
    let domain_fact_id = verification.assumption_infers.store_fact_outputs[1]
        .fact_id
        .expect("finite-sequence domain premise retains its local FactId");
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("finite-sequence equality retains its outer FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_finite_sequence.lit");

    assert!(compiler
        .compile_have_finite_sequence_stmt_result_to_lean_source(result)
        .expect("compile finite sequence directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[0]
        .contains("noncomputable def bounded_sequence : Litex.FnTelescope.Carrier"));
    assert!(compiler.declarations[0].contains("Litex.FnTelescope.requirement"));
    assert!(compiler.declarations[0].contains("fun __arg_domain => ULift.up"));
    assert!(compiler.declarations[1].contains("Litex.finiteSequenceSet.{0} Litex.R (3 : Nat)"));
    assert!(compiler.declarations[2].contains("Litex.fnTelescopeSet"));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.index_binding.id()));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&parameter_fact_id));
    assert!(!compiler
        .environment_stack
        .fact_names
        .contains_key(&domain_fact_id));
    assert!(compiler
        .environment_stack
        .named_function_definitions
        .contains_key(&defining_equality_fact_id));
}

#[test]
fn finite_sequence_rejects_a_missing_local_domain_fact_id() {
    let mut results = execute_finite_sequence_definition();
    finite_sequence_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("finite sequence retains verification")
        .assumption_infers
        .store_fact_outputs[1]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_finite_sequence.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("finite-sequence domain without a local FactId must fail closed");
    assert!(error.contains("finite-sequence domain store has no FactId"));
}

fn execute_matrix_definition() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have matrix entry_matrix matrix(R, 2, 3) for row <= 2, column <= 3, entry_matrix(row, column) = row + column\nentry_matrix(2, 3) = 2 + 3\n",
            "direct_matrix.lit",
        )
        .expect("execute matrix definition and application")
}

fn matrix_result_mut(results: &mut [StmtResult]) -> &mut SuccessHaveMatrixStmtResult {
    let [StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveMatrixStmt(result),
    )), _] = results
    else {
        panic!("expected a matrix definition followed by an application fact")
    };
    result
}

#[test]
fn matrix_compiles_two_parameter_and_two_domain_results_in_one_child_environment() {
    let mut results = execute_matrix_definition();
    let result = matrix_result_mut(&mut results);
    let verification = result
        .verification
        .as_ref()
        .expect("matrix retains combined verification");
    assert_eq!(verification.bound_checks.len(), 4);
    assert_eq!(verification.assumption_infers.store_fact_outputs.len(), 4);
    let local_fact_ids = verification
        .assumption_infers
        .store_fact_outputs
        .iter()
        .map(|store| store.fact_id.expect("matrix local store retains FactId"))
        .collect::<Vec<_>>();
    let defining_equality_fact_id = result.common.infers.store_fact_outputs[1]
        .fact_id
        .expect("matrix equality retains its outer FactId");
    let mut compiler = StmtResultToLeanCompiler::new("direct_matrix.lit");

    assert!(compiler
        .compile_have_matrix_stmt_result_to_lean_source(result)
        .expect("compile matrix directly"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    assert_eq!(compiler.declarations.len(), 4);
    assert!(compiler.declarations[0]
        .contains("noncomputable def entry_matrix : Litex.FnTelescope.Carrier"));
    assert!(compiler.declarations[0].contains("__arg1"));
    assert!(compiler.declarations[0].contains("__arg2"));
    assert!(compiler.declarations[0].contains("fun __arg_domain => ULift.up"));
    assert!(compiler.declarations[1].contains("Litex.matrixSet.{0} Litex.R (2 : Nat) (3 : Nat)"));
    assert!(compiler.declarations[2].contains("Litex.fnTelescopeSet"));
    for fact_id in local_fact_ids {
        assert!(!compiler.environment_stack.fact_names.contains_key(&fact_id));
    }
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.row_index_binding.id()));
    assert!(!compiler
        .environment_stack
        .symbol_names
        .contains_key(&result.statement.col_index_binding.id()));
    assert!(compiler
        .environment_stack
        .named_function_definitions
        .contains_key(&defining_equality_fact_id));
}

#[test]
fn matrix_rejects_a_missing_local_column_domain_fact_id() {
    let mut results = execute_matrix_definition();
    matrix_result_mut(&mut results)
        .verification
        .as_mut()
        .expect("matrix retains verification")
        .assumption_infers
        .store_fact_outputs[3]
        .fact_id = None;

    let error = StmtResultToLeanCompiler::new("direct_matrix.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("matrix column domain without a local FactId must fail closed");
    assert!(error.contains("matrix domain store 1 has no FactId"));
}

#[test]
fn registered_set_rule_rejects_stale_fingerprint() {
    let rule_id =
        RuleId::new(SET_POWER_SET_MEMBERSHIP_OF_SUBSET_RULE_ID).expect("valid stable rule id");
    let stale_fingerprint =
        RuleFingerprint::from_hex("0".repeat(64)).expect("valid forged fingerprint shape");
    assert!(registered_set_rule(&rule_id, &stale_fingerprint).is_none());
}

fn execute_registered_power_set_membership() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have A set = R\nhave B set = C\ntrust A $subset B\nA $in power_set(B)\n",
            "direct_registered_power_set_membership.lit",
        )
        .expect("execute registered power-set membership")
}

fn run_registered_rule_test(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("stmt-result-direct-compiler-test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("spawn direct-compiler test thread")
        .join()
        .expect("direct-compiler test panicked");
}

#[test]
fn registered_set_rule_compiles_directly_from_its_recursive_certificate() {
    run_registered_rule_test(|| {
        let results = execute_registered_power_set_membership();
        let [set_a, set_b, _, result] = results.as_slice() else {
            panic!("expected two set definitions, one trust boundary, and one result")
        };
        let result = result
            .factual_success()
            .expect("registered set rule result is factual");
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            panic!("expected registered builtin proof")
        };
        let mut compiler =
            StmtResultToLeanCompiler::new("direct_registered_power_set_membership.lit");
        compiler
            .compile_stmt_result_to_lean_source(set_a)
            .expect("compile first set definition");
        compiler
            .compile_stmt_result_to_lean_source(set_b)
            .expect("compile second set definition");
        for (index, child) in builtin.subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .expect("registered set child is factual");
            let SuccessFactProofResult::StoredFactCitation(citation) = child.proof() else {
                panic!("registered set child must cite an exact source fact")
            };
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
            .expect("compile registered set rule directly")
            .expect("registered set rule must not use compatibility IR");
        assert!(
            generated.contains("Litex.SetRules.inPowerSetOfSubset"),
            "{generated}"
        );
    });
}

#[test]
fn registered_set_rule_result_rejects_a_stale_fingerprint() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_power_set_membership();
        let StmtResult::Success(SuccessStmtResult::Fact(result)) = &mut results[3] else {
            panic!("expected registered power-set membership Result")
        };
        let verification = std::rc::Rc::get_mut(&mut result.verification)
            .expect("test result has one verification owner");
        let SuccessFactProofResult::BuiltinRule(proof) = verification.proof_mut() else {
            panic!("expected registered builtin proof")
        };
        let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) = proof.evidence.typed_mut()
        else {
            panic!("expected registered local certificate")
        };
        evidence.semantic_fingerprint =
            RuleFingerprint::from_hex("0".repeat(64)).expect("valid forged fingerprint shape");

        let error = StmtResultToLeanCompiler::new("direct_registered_power_set_membership.lit")
            .construct_lean_proof_from_direct_fact_result(result)
            .expect_err("a stale registry certificate must fail closed");
        assert!(error.contains("stale local builtin fingerprint"), "{error}");
    });
}

#[test]
fn common_arithmetic_sign_rule_combines_its_child_results_directly() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
            .compile_stmt_result_to_lean_source(objects)
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
            generated.contains(
                "Litex.Rules.complexAddPreservesLessEqualComponentwise (__domain1) (__domain2)"
            ),
            "{generated}"
        );
    });
}

#[test]
fn registered_componentwise_order_addition_rejects_swapped_semantic_children() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_componentwise_order_addition();
        let builtin = registered_componentwise_order_addition_builtin_mut(&mut results);
        assert_eq!(builtin.subgoals.len(), 6);
        builtin.subgoals.swap(4, 5);

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

#[test]
fn registered_componentwise_order_addition_rejects_stale_fingerprint() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_componentwise_order_addition();
        let builtin = registered_componentwise_order_addition_builtin_mut(&mut results);
        let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) = builtin.evidence.typed_mut()
        else {
            panic!("expected registered local builtin evidence")
        };
        evidence.semantic_fingerprint =
            RuleFingerprint::from_hex("0".repeat(64)).expect("valid forged fingerprint shape");

        let error =
            StmtResultToLeanCompiler::new("direct_registered_componentwise_order_addition.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("stale registered order fingerprint must fail closed");
        assert!(error.contains("stale local builtin fingerprint"), "{error}");
    });
}

fn execute_registered_subtraction_sign_and_greater_to_greater_equal_rules() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
            generated.contains("Litex.Rules.complexSubNonnegativeOfLessEqual (__domain1)"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Rules.complexSubPositiveOfLess (__domain1)"),
            "{generated}"
        );
        assert!(
            generated.contains("Litex.Lt.toLe (__domain1)"),
            "{generated}"
        );
    });
}

#[test]
fn registered_subtraction_sign_rejects_reordered_parameter_and_semantic_children() {
    run_registered_rule_test(|| {
        let mut results = execute_registered_subtraction_sign_and_greater_to_greater_equal_rules();
        let builtin = registered_single_forall_conclusion_builtin_mut(&mut results[0]);
        assert_eq!(builtin.subgoals.len(), 3);
        builtin.subgoals.swap(0, 2);

        let error =
            StmtResultToLeanCompiler::new("direct_registered_subtraction_sign_and_order.lit")
                .compile_stmt_results_to_lean_source(&results)
                .expect_err("reordered registered subtraction-sign children must fail closed");
        assert!(error.contains("expected membership fact"), "{error}");
    });
}

#[test]
fn clear_resets_result_visibility_and_opens_a_fresh_lean_namespace() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "have A set = R\nclear\nhave A set = C\n",
                "direct_clear_compiler_environment.lit",
            )
            .expect("execute a same-name definition after clear");
        let generated = StmtResultToLeanCompiler::new("direct_clear_compiler_environment.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile clear as an environment-layer operation");
        assert!(generated.contains("abbrev A : Litex.Set := Litex.R"));
        assert!(generated.contains("namespace __AfterClear01"));
        assert!(generated.contains("abbrev A : Litex.Set := Litex.C"));
        assert!(generated.contains("end __AfterClear01"));
    });
}

#[test]
fn source_with_only_do_nothing_produces_valid_declaration_free_lean_source() {
    run_registered_rule_test(|| {
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "do_nothing\n",
                "direct_do_nothing_result.lit",
            )
            .expect("execute do_nothing");
        let generated = StmtResultToLeanCompiler::new("direct_do_nothing_result.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile a declaration-free successful Result stream");
        assert!(generated.contains("namespace __Compiler_direct_do_nothing_result"));
        assert!(!generated.contains("theorem __fact"));
    });
}

fn execute_order_transitivity() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
fn order_transitivity_compiles_from_carrier_and_order_children_directly() {
    run_registered_rule_test(|| {
        let mut results = execute_order_transitivity();
        order_transitivity_builtin_mut(&mut results);
        let generated = StmtResultToLeanCompiler::new("direct_order_transitivity.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile typed order transitivity");
        assert!(
            generated.contains("Litex.Le.transLt (__domain1) (__domain2)"),
            "{generated}"
        );
    });
}

#[test]
fn order_transitivity_rejects_reversed_order_children() {
    run_registered_rule_test(|| {
        let mut results = execute_order_transitivity();
        let builtin = order_transitivity_builtin_mut(&mut results);
        let child_count = builtin.subgoals.len();
        assert!(child_count >= 3);
        builtin.subgoals.swap(child_count - 2, child_count - 1);
        let error = StmtResultToLeanCompiler::new("direct_order_transitivity.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("reversed transitivity path must fail closed");
        assert!(error.contains("changed its ordered path"), "{error}");
    });
}

fn execute_strategy_definition_with_local_proof_environment() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "prop reflexive(x R):\n    x = x\n\nstrategy prove_reflexive:\n    ? forall x R:\n        $reflexive(x)\n    x = x\n    by def $reflexive(x)\n\nstop strategy prove_reflexive\nuse strategy prove_reflexive\n",
            "direct_strategy_definition_compiler_environment.lit",
        )
        .expect("execute a verified strategy with one local parameter scope")
}

#[test]
fn strategy_definition_compiles_from_recursive_well_definedness_and_local_proof_scope() {
    run_registered_rule_test(|| {
        let results = execute_strategy_definition_with_local_proof_environment();
        let [_, StmtResult::Success(SuccessStmtResult::DefStrategyStmt(strategy)), _, _] =
            results.as_slice()
        else {
            panic!("expected predicate, strategy, stop, and use Results")
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
        assert!(generated.contains("intro x __h0_1"), "{generated}");
        assert!(
            generated.contains("have __step2 : reflexive x"),
            "{generated}"
        );
    });
}

#[test]
fn strategy_definition_rejects_a_result_missing_its_local_parameter_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_strategy_definition_with_local_proof_environment();
        let [_, StmtResult::Success(SuccessStmtResult::DefStrategyStmt(strategy)), _, _] =
            results.as_mut_slice()
        else {
            panic!("expected predicate, strategy, stop, and use Results")
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
        assert!(generated.contains("intro x __h0_1"), "{generated}");
        assert!(
            generated.contains("Litex.Le.refl (((Litex.In.rep x __h0_1 : ℝ)) : ℂ)"),
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
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
        let mut results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
                .compile_stmt_result_to_lean_source(prefix)
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
    crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
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
        let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
                "setting RealElement(x R)\n\nforall [RealElement]:\n    x = x\n",
                "direct_setting_elaboration_result.lit",
            )
            .expect("execute one setting and one elaborated forall");
        let [StmtResult::Success(SuccessStmtResult::DefInterfaceStmt(
            SuccessDefInterfaceStmtResult::DefSettingStmt(setting),
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

#[test]
fn def_struct_result_retains_each_local_verification_phase_without_synthetic_statements() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "struct ValueBox<S set>:\n    value S\n    <=>:\n        value = value\n",
            "def_struct_result_contract.lit",
        )
        .expect("execute struct Result contract fixture");
    let [StmtResult::Success(SuccessStmtResult::DefInterfaceStmt(
        SuccessDefInterfaceStmtResult::DefStructStmt(result),
    ))] = results.as_slice()
    else {
        panic!("expected one successful def-struct Result")
    };

    let local = result
        .run_in_local_env
        .as_ref()
        .expect("verified struct must retain its local verification flow");
    assert!(local.structure_parameter_definition.is_some());
    assert!(local.structure_domains.is_empty());
    assert_eq!(local.field_types.len(), 1);
    assert_eq!(local.field_types[0].field_index, 0);
    assert_eq!(local.field_types[0].binding.name(), "value");

    let field_scope = &local.field_scope_run_in_local_env;
    assert_eq!(field_scope.field_definitions.len(), 1);
    assert_eq!(field_scope.field_definitions[0].field_index, 0);
    assert_eq!(field_scope.equivalent_facts.len(), 1);
    assert!(field_scope.equivalent_facts[0].store.fact_id.is_some());
    let json = display_stmt_result_json_v2(&results[0]);
    assert!(json.contains("\"run_in_local_env\""), "{json}");
    assert!(json.contains("\"equivalent_facts\""), "{json}");
    let compiler_error = StmtResultToLeanCompiler::new("def_struct_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results)
        .expect_err("unsupported struct lowering must fail closed");
    assert!(compiler_error.contains("DefStructStmt"), "{compiler_error}");
}

#[test]
fn def_algo_result_retains_retagged_parameters_and_the_exact_default_check() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            "have fn identity(x R) R = x\nhave algo for identity(x):\n    x\n",
            "def_algo_result_contract.lit",
        )
        .expect("execute algorithm Result contract fixture");
    let [_, StmtResult::Success(SuccessStmtResult::DefAlgoStmt(result))] = results.as_slice()
    else {
        panic!("expected function declaration followed by def-algo Result")
    };

    let local = result
        .run_in_local_env
        .as_ref()
        .expect("verified algorithm must retain its local verification flow");
    assert_eq!(local.parameter_retagging.len(), 1);
    assert_eq!(local.parameter_retagging[0].parameter_index, 0);
    assert_eq!(local.parameter_retagging[0].source_binding.name(), "x");
    assert!(!local.requirement_facts.is_empty());
    assert!(local.cases.is_empty());
    assert!(local.default_return.is_some());
    assert!(local.coverage.is_none());
    assert!(local
        .default_return
        .as_ref()
        .expect("default check")
        .verification
        .is_true());
    let mut child_results = Vec::new();
    let StmtResult::Success(success) = &results[1] else {
        unreachable!("the statement was already matched as successful")
    };
    success.visit_child_results(&mut |child| child_results.push(child.statement()));
    assert_eq!(
        child_results.len(),
        1,
        "the generic Result visitor must expose the exact default-return check"
    );
    let json = display_stmt_result_json_v2(&results[1]);
    assert!(json.contains("\"parameter_retagging\""), "{json}");
    assert!(json.contains("\"default_return\""), "{json}");
    let compiler_error = StmtResultToLeanCompiler::new("def_algo_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results[1..])
        .expect_err("unsupported algorithm lowering must fail closed");
    assert!(compiler_error.contains("DefAlgoStmt"), "{compiler_error}");
}

#[test]
fn inductive_function_result_retains_both_local_flows_and_recursive_cases() {
    let results = crate::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source::execute_litex_source_to_stmt_results(
            r#"have fn step(x R+) R+ = (x + 2 / x) / 2
have fn iterate(n N) R+ by induc n from 0:
    case n = 0: 1
    case n > 0: step(iterate(n - 1))
"#,
            "have_fn_by_induc_result_contract.lit",
        )
        .expect("execute inductive-function Result contract fixture");
    let [_, StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnByInducStmt(result),
    ))] = results.as_slice()
    else {
        panic!("expected helper function followed by inductive-function Result")
    };

    let verification = result
        .verification
        .as_ref()
        .expect("verified inductive function must retain verification");
    assert_eq!(
        verification
            .well_definedness_run_in_local_env
            .parameters_and_domain
            .parameter_groups
            .len(),
        1
    );
    let local = &verification.verification_run_in_local_env;
    assert!(local.measure.measure_integer_check.is_true());
    assert!(local.measure.lower_bound_integer_check.is_true());
    assert!(local.measure.lower_bound_check.is_true());
    assert!(local.recursive_function.membership_store.fact_id.is_some());
    assert!(local.cases.coverage_check.is_true());
    assert_eq!(local.cases.mutual_exclusions.len(), 1);
    assert_eq!(local.cases.mutual_exclusions[0].left_case_index, 0);
    assert_eq!(local.cases.mutual_exclusions[0].right_case_index, 1);
    assert!(local.cases.mutual_exclusions[0]
        .negated_atom_check
        .is_true());
    assert_eq!(local.cases.cases.len(), 2);
    for case in &local.cases.cases {
        assert!(case.assumption_store.fact_id.is_some());
        let SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) = &case.body else {
            panic!("fixture cases must retain equal-to bodies")
        };
        assert!(body.return_membership_check.is_true());
    }
    let mut visited_children = 0;
    let StmtResult::Success(success) = &results[1] else {
        unreachable!("the statement was already matched as successful")
    };
    success.visit_child_results(&mut |_| visited_children += 1);
    assert_eq!(
        visited_children, 7,
        "the generic Result visitor must expose three measure checks, coverage, one disjointness check, and two return checks"
    );
    let json = display_stmt_result_json_v2(&results[1]);
    assert!(
        json.contains("\"well_definedness_run_in_local_env\""),
        "{json}"
    );
    assert!(json.contains("\"mutual_exclusions\""), "{json}");
    let compiler_error = StmtResultToLeanCompiler::new("have_fn_by_induc_result_contract.lit")
        .compile_stmt_results_to_lean_source(&results[1..])
        .expect_err("unsupported inductive-function lowering must fail closed");
    assert!(
        compiler_error.contains("HaveFnByInducStmt"),
        "{compiler_error}"
    );
}

#[test]
fn trusted_definition_results_do_not_invent_verification_evidence() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("trusted_definition_results.lit");
    runtime.replace_current_execution_mode(ExecutionMode::Trusted);
    let (results, error) = crate::pipeline::pipeline::run_source_code(
        r#"struct TrustedBox:
    value R
have fn trustedIdentity(x R) R = x
have algo for trustedIdentity(x):
    x
have fn trustedIterate(n N) R by induc n from 0:
    case n = 0: 0
    case n > 0: trustedIterate(n - 1)
"#,
        &mut runtime,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(results.len(), 4);

    let StmtResult::Success(SuccessStmtResult::DefInterfaceStmt(
        SuccessDefInterfaceStmtResult::DefStructStmt(result),
    )) = &results[0]
    else {
        panic!("expected trusted struct Result")
    };
    assert!(result.run_in_local_env.is_none());

    let StmtResult::Success(SuccessStmtResult::DefAlgoStmt(result)) = &results[2] else {
        panic!("expected trusted algorithm Result")
    };
    assert!(result.run_in_local_env.is_none());

    let StmtResult::Success(SuccessStmtResult::DefObjStmt(
        SuccessDefObjStmtResult::HaveFnByInducStmt(result),
    )) = &results[3]
    else {
        panic!("expected trusted inductive-function Result")
    };
    assert!(result.verification.is_none());
}
