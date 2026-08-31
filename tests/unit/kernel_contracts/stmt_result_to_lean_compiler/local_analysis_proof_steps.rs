use super::super::*;
use super::run_registered_rule_test;
use std::rc::Rc;

const LOCAL_REAL_COMPLETENESS_SOURCE: &str = r#"
thm local_real_completeness:
    ? forall S set, upper R:
        S $subset R
        $is_nonempty_set(S)
        forall member R:
            member $in S
            =>:
                member <= upper
        =>:
            exist L R st {$is_real_least_upper_bound(S, L)}
    release thm real_least_upper_bound_exists(S, upper)
"#;

const LOCAL_TRANSPARENT_SET_MEMBERSHIP_SOURCE: &str = r#"
thm local_transparent_set_membership:
    ? forall marker R:
        marker = marker
        =>:
            marker = marker
    have E power_set(R) = {x R: x = 0}
    0 $in E
    marker = marker
"#;

const LOCAL_REAL_GLB_SOURCE: &str = r#"
thm local_real_glb_boundary:
    ? forall S set, lower R:
        S $subset R
        $is_nonempty_set(S)
        forall member R:
            member $in S
            =>:
                lower <= member
        =>:
            exist L R st {$is_real_greatest_lower_bound(S, L)}
    release thm real_greatest_lower_bound_exists(S, lower)
"#;

const RATIONAL_DENSITY_NATIVE_WITNESS_SOURCE: &str = r#"
release thm rational_between_reals(0, 1)
obtain q from exist rational Q st {0 < rational and rational < 1}
0 < q
q < 1
"#;

fn execute_source(source: &str, path: &str) -> Vec<StmtResult> {
    crate::stmt_result_to_lean_compiler::source_compilation::execute_litex_source_for_lean_compilation(
        source, path,
    )
    .expect("execute local analysis proof-step tracer")
}

fn theorem_proof_steps_mut(results: &mut [StmtResult]) -> &mut [StmtResult] {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(theorem),
    ))] = results
    else {
        panic!("expected one named theorem Result")
    };
    theorem
        .verification
        .as_mut()
        .expect("named theorem must retain verification")
        .proof_steps
        .as_mut_slice()
}

#[test]
fn local_real_completeness_replays_the_typed_builtin_application() {
    run_registered_rule_test(|| {
        let results = execute_source(
            LOCAL_REAL_COMPLETENESS_SOURCE,
            "local_real_completeness.lit",
        );
        let generated = StmtResultToLeanCompiler::new("local_real_completeness.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile local real-completeness proof step");

        assert!(
            generated.contains("Litex.Rules.realLeastUpperBoundExists"),
            "{generated}"
        );
        assert!(generated.contains("have __step1_0 : ∃"), "{generated}");
        for forbidden in ["LitexObject", "Litex.Object", "sorry", "axiom "] {
            assert!(
                !generated.contains(forbidden),
                "forbidden `{forbidden}` in:\n{generated}"
            );
        }
    });
}

#[test]
fn rational_density_keeps_the_mathlib_witness_in_the_exact_rational_carrier() {
    run_registered_rule_test(|| {
        let results = execute_source(
            RATIONAL_DENSITY_NATIVE_WITNESS_SOURCE,
            "rational_density_native_witness.lit",
        );
        let generated = StmtResultToLeanCompiler::new("rational_density_native_witness.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile rational-density introduction and elimination");

        assert!(
            generated.contains("∃ (rational : (Litex.Q).Carrier)"),
            "{generated}"
        );
        assert!(
            generated.contains("noncomputable def q : (Litex.Q).Carrier"),
            "{generated}"
        );
        assert!(
            generated.contains("theorem __fact3 : Litex.Lt"),
            "{generated}"
        );
        assert!(
            generated.contains("theorem __fact4 : Litex.Lt"),
            "{generated}"
        );
        for forbidden in ["LitexObject", "Litex.Object", "sorry", "axiom "] {
            assert!(
                !generated.contains(forbidden),
                "forbidden `{forbidden}` in:\n{generated}"
            );
        }
    });
}

#[test]
fn local_real_completeness_rejects_a_changed_requirement_schema() {
    run_registered_rule_test(|| {
        let mut results = execute_source(
            LOCAL_REAL_COMPLETENESS_SOURCE,
            "local_real_completeness.lit",
        );
        let proof_steps = theorem_proof_steps_mut(&mut results);
        let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) =
            &mut proof_steps[0]
        else {
            panic!("expected local release-thm as proof step one")
        };
        let verification = application
            .verification
            .as_mut()
            .expect("local release-thm retains verification");
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &mut verification.source
        else {
            panic!("real completeness retains builtin theorem evidence")
        };
        source.requirement_roles.pop();

        let error = StmtResultToLeanCompiler::new("local_real_completeness.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("a changed builtin requirement schema must fail closed");
        assert!(
            error.contains("typed requirement schema")
                || error.contains("requirement role")
                || error.contains("requirement count"),
            "{error}"
        );
    });
}

#[test]
fn local_transparent_set_membership_replays_the_defining_fact_id() {
    run_registered_rule_test(|| {
        let results = execute_source(
            LOCAL_TRANSPARENT_SET_MEMBERSHIP_SOURCE,
            "local_transparent_set_membership.lit",
        );
        let generated = StmtResultToLeanCompiler::new("local_transparent_set_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile transparent local set membership");

        assert!(generated.contains("unfold E"), "{generated}");
        assert!(
            generated.contains("Litex.Rules.inSetBuilder"),
            "{generated}"
        );
        assert!(generated.contains("simpa [E]"), "{generated}");
        let json = crate::output::display_stmt_result_json_v2(&theorem_proof_steps(&results)[1]);
        assert!(json.contains("TransparentDefinitionReduction"), "{json}");
        assert!(json.contains("defining_equality_fact_id"), "{json}");
    });
}

fn theorem_proof_steps(results: &[StmtResult]) -> &[StmtResult] {
    let [StmtResult::Success(SuccessStmtResult::Definition(
        SuccessDefinitionStmtResult::DefThmStmt(theorem),
    ))] = results
    else {
        panic!("expected one named theorem Result")
    };
    theorem
        .verification
        .as_ref()
        .expect("named theorem must retain verification")
        .proof_steps
        .as_slice()
}

#[test]
fn local_transparent_set_membership_rejects_a_changed_definition_fact_id() {
    run_registered_rule_test(|| {
        let mut results = execute_source(
            LOCAL_TRANSPARENT_SET_MEMBERSHIP_SOURCE,
            "local_transparent_set_membership.lit",
        );
        let proof_steps = theorem_proof_steps_mut(&mut results);
        let (definition_steps, membership_steps) = proof_steps.split_at_mut(1);
        let StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::HaveObjEqualStmt(definition),
        )) = &definition_steps[0]
        else {
            panic!("expected local set definition as proof step one")
        };
        let wrong_fact_id = definition.common.infers.store_fact_outputs[0]
            .fact_id
            .expect("local definition type fact retains a FactId");
        let membership = membership_steps[0]
            .factual_success_mut()
            .expect("proof step two is a membership fact");
        let verification = Rc::get_mut(&mut membership.verification)
            .expect("membership verification is not shared in this Result");
        let SuccessFactProofResult::Reuse(reuse) = verification.proof_mut() else {
            panic!("expected outer membership proof reuse")
        };
        let transformed = Rc::get_mut(&mut reuse.source)
            .expect("membership transformation is not shared in this Result");
        let SuccessFactProofResult::Transform(transformation) = transformed.proof_mut() else {
            panic!("expected transparent membership transformation")
        };
        let FactTransformationRule::TransparentDefinitionReduction(evidence) =
            &mut transformation.rule
        else {
            panic!("expected transparent-definition reduction evidence")
        };
        evidence.definitions[0].defining_equality_fact_id = wrong_fact_id;

        let error = StmtResultToLeanCompiler::new("local_transparent_set_membership.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("a changed defining FactId must fail closed");
        assert!(error.contains("FactId"), "{error}");
    });
}

#[test]
fn local_real_glb_replays_the_typed_builtin_application() {
    run_registered_rule_test(|| {
        let results = execute_source(LOCAL_REAL_GLB_SOURCE, "local_real_glb_boundary.lit");
        let generated = StmtResultToLeanCompiler::new("local_real_glb_boundary.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect("compile local real greatest-lower-bound proof step");
        assert!(
            generated.contains("Litex.Rules.realGreatestLowerBoundExists"),
            "{generated}"
        );
        assert!(generated.contains("have __step1_0 : ∃"), "{generated}");
        for forbidden in ["LitexObject", "Litex.Object", "sorry", "axiom "] {
            assert!(
                !generated.contains(forbidden),
                "forbidden `{forbidden}` in:\n{generated}"
            );
        }
    });
}

#[test]
fn local_real_glb_rejects_a_changed_requirement_schema() {
    run_registered_rule_test(|| {
        let mut results = execute_source(LOCAL_REAL_GLB_SOURCE, "local_real_glb_boundary.lit");
        let proof_steps = theorem_proof_steps_mut(&mut results);
        let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) =
            &mut proof_steps[0]
        else {
            panic!("expected local release-thm as proof step one")
        };
        let verification = application
            .verification
            .as_mut()
            .expect("local release-thm retains verification");
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &mut verification.source
        else {
            panic!("real GLB completeness retains builtin theorem evidence")
        };
        source.requirement_roles.pop();

        let error = StmtResultToLeanCompiler::new("local_real_glb_boundary.lit")
            .compile_stmt_results_to_lean_source(&results)
            .expect_err("a changed GLB builtin requirement schema must fail closed");
        assert!(
            error.contains("typed requirement schema")
                || error.contains("requirement role")
                || error.contains("requirement count"),
            "{error}"
        );
    });
}
