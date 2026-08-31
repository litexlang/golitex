use super::super::*;
use super::builtin_evidence_and_fact_ids::{
    closed_natural_membership_result_mut, execute_closed_natural_membership,
};
use super::run_registered_rule_test;

fn execute_direct_forall_proof() -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
    assert!(compiler.declarations[0].contains("∀ {__carrier1 : Type} (__p1 : __carrier1)"));
    assert!(compiler.declarations[0].contains("intro __carrier1 x __h"));
    assert!(
        compiler.declarations[0].contains("have __prior0_0"),
        "{}",
        compiler.declarations[0]
    );
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
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
    assert!(declaration.matches("have __infer0_").count() >= 4);
    assert!(declaration.contains("Litex.Rules.naturalRepNonnegative (__h"));
    assert!(declaration.contains("Litex.Rules.complexEqNatInN"));
    assert!(!declaration.contains("complexAddInN (__h0_1)"));
    assert_eq!(compiler.environment_stack.environments.len(), 1);
    for fact_id in inferred_fact_ids {
        assert!(!compiler.environment_stack.fact_names.contains_key(&fact_id));
    }
}

#[test]
fn forall_proof_rejects_natural_inference_citing_the_wrong_parameter_fact_id() {
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
        let results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
        assert!(declaration.contains("have __infer0_0 : Litex.Lt (0 : ℂ)"));
        assert!(declaration.contains("Litex.Rules.positiveRealCarrierPositive (__h"));
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
        let mut results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
        let results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                "forall f fn(x R) R:\n    f = f\n",
                "direct_forall_function_parameter.lit",
            )
            .expect("execute forall with a function parameter");
        let generated = StmtResultToLeanCompiler::new("direct_forall_function_parameter.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile function-parameter forall directly");

        assert!(
            generated.contains("intro __carrier1 f __h") && generated.contains("Litex.Same.refl f"),
            "function parameter lost its carrier or membership contract: {generated}"
        );
    });
}

#[test]
fn forall_registered_set_parameter_checks_are_validated_without_lean_proof_terms() {
    run_registered_rule_test(|| {
        let results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
            generated.contains("intro __carrier1 a __h")
                && generated.contains("__domain1")
                && generated.contains(":= __domain1"),
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
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        "witness $is_nonempty_set({1, 2}) from 1\n",
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
        let results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "have a, b R\ntrust a != b\nb != a\n",
            "direct_not_equal_symmetry.lit",
        )
        .expect("execute a symbolic symmetry example");
    let [objects, trusted, symmetric] = results.as_slice() else {
        panic!("expected object choice, source trust, and symmetric fact")
    };
    let mut compiler = StmtResultToLeanCompiler::new("direct_not_equal_symmetry.lit");
    compiler
        .compile_stmt_result(objects)
        .expect("compile object bindings");
    compiler
        .compile_stmt_result(trusted)
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
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
    let json = crate::output::render_statement_result_json(&results[0]);
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
    let mut results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
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
        let results =
            crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
                source,
                "direct_arithmetic_closure.lit",
            )
            .unwrap_or_else(|error| panic!("execute {expected_theorem}: {error}"));
        let [objects, fact] = results.as_slice() else {
            panic!("{expected_theorem} source must return two Results")
        };
        let mut compiler = StmtResultToLeanCompiler::new("direct_arithmetic_closure.lit");
        compiler
            .compile_stmt_result(objects)
            .unwrap_or_else(|error| panic!("compile binders for {expected_theorem}: {error}"));
        compiler
            .compile_stmt_result(fact)
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
    let results =
        crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
            "let A = {1}\nlet B = {2}\ntrust {1} $superset {2}\nB $subset A\n",
            "direct_set_relation_duality.lit",
        )
        .expect("execute set-relation duality source");
    let [set_a, set_b, trusted, dual_result] = results.as_slice() else {
        panic!("expected two set aliases, trusted premise, and dual result")
    };
    let dual = dual_result
        .factual_success()
        .expect("duality result is factual");
    let SuccessFactProofResult::Reuse(reuse) = dual.proof() else {
        panic!("transparent set aliases must retain the outer proof reuse")
    };
    let SuccessFactProofResult::Transform(transparent) = reuse.source.proof() else {
        panic!("transparent set aliases must retain their definition reduction")
    };
    assert!(matches!(
        transparent.rule,
        FactTransformationRule::TransparentDefinitionReduction(_)
    ));
    let SuccessFactProofResult::BuiltinRule(proof) = transparent.source.proof() else {
        panic!("the reduced relation must retain its builtin duality proof")
    };
    assert!(matches!(
        proof.evidence.typed(),
        Some(BuiltinRuleEvidence::SetRelationDuality(
            SetRelationDualityBuiltinRule::SubsetFromSuperset
        ))
    ));
    let [_source_result] = proof.subgoals.as_slice() else {
        panic!("duality must retain one source Result")
    };
    let StmtResult::Success(SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustStmt(
        trusted,
    ))) = trusted
    else {
        panic!("the source premise must remain the trusted relation")
    };
    let [trusted_store] = trusted.common.infers.store_fact_outputs.as_slice() else {
        panic!("the trusted premise must retain one exact store")
    };
    let trusted_fact_id = trusted_store
        .fact_id
        .expect("the trusted premise must retain its FactId");
    let trusted_fact = trusted_store.itself_and_why_itself_is_stored.0.clone();
    let mut compiler = StmtResultToLeanCompiler::new("direct_set_relation_duality.lit");
    compiler
        .compile_stmt_result(set_a)
        .expect("compile first set alias");
    compiler
        .compile_stmt_result(set_b)
        .expect("compile second set alias");
    compiler
        .environment_stack
        .fact_names
        .insert(trusted_fact_id, "__fact0".to_string());
    compiler
        .environment_stack
        .fact_propositions
        .insert(trusted_fact_id, trusted_fact);
    let proof = compiler
        .construct_lean_proof_from_direct_fact_result(dual)
        .expect("compile typed duality")
        .expect("duality must not use compatibility IR");
    assert!(proof.contains("__fact"), "{proof}");
}
