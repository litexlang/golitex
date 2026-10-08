use super::compile_run;
use crate::prelude::*;

fn execute(source: &str) -> (RunLitexCodeResult, Runtime) {
    let command =
        parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
            .expect("strict command");
    let mut runtime = Runtime::new(command);
    let result = runtime.run_litex_code(source).expect("execute source");
    assert!(
        result.success,
        "test input must already be successfully verified"
    );
    (result, runtime)
}

#[test]
fn combined_unit_preserves_only_legal_scope_dependencies() {
    let source = "1 = 1\n$is_set(1)\n1 $in R\nforall a C:\n    a = a\nforall a R:\n    a $in C\nforall a C, b C:\n    b != 0\n    =>:\n        a / b = a / b\n";
    let (result, runtime) = execute(source);
    assert_eq!(result.statement_results.len(), 6);
    assert!(compile_run(&result, &runtime, "combined_scope").is_ok());
}

#[test]
fn available_lean_identity_does_not_replace_an_unsupported_winning_route() {
    let (result, runtime) = execute("1 = 1\nforall a C:\n    a + 0 = a\n");
    let error = compile_run(&result, &runtime, "unsupported_add_zero")
        .expect_err("Rational evidence is not implemented");
    assert_eq!(error.statement_index, Some(2));
    assert_eq!(error.route, "Equality/BuiltinRule");
}

#[test]
fn known_wd_requires_the_exact_recorded_subject() {
    let (mut result, runtime) = execute("1 = 1\n2 = 2\n$is_set(1)\n");
    let two = match &result.statement_results[1] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
            match &success.verify_result {
                VerifyFactResult::Equality(proof) => match proof.as_ref() {
                    VerifyEqualityResult::Success(proof) => proof.fact.left.clone(),
                    VerifyEqualityResult::Failed(_) => panic!("verified equality"),
                },
                _ => panic!("equality result"),
            }
        }
        _ => panic!("successful fact"),
    };
    let other_id = runtime
        .top_exec_env()
        .well_defined_objects
        .lookup(&two)
        .expect("two's WD record");
    let success = match &mut result.statement_results[2] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => success,
        _ => panic!("successful fact"),
    };
    let atomic = match &mut success.verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified sethood"),
        },
        _ => panic!("atomic result"),
    };
    match &mut atomic.well_defined_proof.well_defined_of_each_parameter[0] {
        ObjWellDefinedProof::ByKnown { wd_id, .. } => *wd_id = other_id,
        ObjWellDefinedProof::ByDef { .. } => panic!("sethood should reuse one's WD"),
    }
    let error = compile_run(&result, &runtime, "wrong_wd_subject")
        .expect_err("another object's cache is not this certificate");
    assert_eq!(error.route, "WD/ByKnown");
}

#[test]
fn a_missing_wd_id_is_not_recovered_from_a_true_goal() {
    let (mut result, runtime) = execute("1 = 1\n$is_set(1)\n");
    let success = match &mut result.statement_results[1] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => success,
        _ => panic!("successful fact"),
    };
    let atomic = match &mut success.verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified sethood"),
        },
        _ => panic!("atomic result"),
    };
    match &mut atomic.well_defined_proof.well_defined_of_each_parameter[0] {
        ObjWellDefinedProof::ByKnown { wd_id, .. } => *wd_id = WellDefinednessId::new(u64::MAX),
        ObjWellDefinedProof::ByDef { .. } => panic!("sethood should reuse one's WD"),
    }
    let error = compile_run(&result, &runtime, "missing_wd_id")
        .expect_err("the cited WD identity must resolve");
    assert_eq!(error.route, "WdId/Resolution");
}

#[test]
fn closed_forall_assumptions_do_not_escape_into_the_next_forall() {
    let (mut result, runtime) = execute("forall a R:\n    a = a\nforall b R:\n    b $in C\n");
    assert!(compile_run(&result, &runtime, "valid_scopes").is_ok());
    let old_id = forall_proof_mut(&mut result.statement_results[0])
        .introduced_params
        .defined_params
        .stored_fact_ids[0];
    let second = forall_proof_mut(&mut result.statement_results[1]);
    let atomic = match &mut second.proved_then_facts[0].verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified membership"),
        },
        _ => panic!("atomic result"),
    };
    let member = match &mut atomic.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
            match &mut proof.reason {
                StructuralMembershipReason::StandardSuperset(child) => child,
                _ => panic!("standard-superset route"),
            }
        }
        _ => panic!("structural membership"),
    };
    match &mut member.reason {
        StructuralMembershipReason::Known(proof) => proof.cite_fact_id = old_id,
        _ => panic!("R-membership citation"),
    }
    let error = compile_run(&result, &runtime, "escaped_scope")
        .expect_err("the earlier binder assumption is closed");
    assert_eq!(error.route, "FactId/Resolution");
}

#[test]
fn division_reflexivity_replays_nonzero_evidence_before_reflexivity() {
    let (mut result, runtime) =
        execute("forall a C, b C:\n    b != 0\n    =>:\n        a / b = a / b\n");
    assert!(compile_run(&result, &runtime, "valid_division").is_ok());
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = match &mut forall.proved_then_facts[0].verify_result {
        VerifyFactResult::Equality(proof) => match proof.as_mut() {
            VerifyEqualityResult::Success(proof) => proof,
            VerifyEqualityResult::Failed(_) => panic!("verified equality"),
        },
        _ => panic!("equality result"),
    };
    match &mut equality.well_defined_proof.left {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Div(proof),
                ),
            ..
        } => {
            proof.requirement_fact_verified.remove(0);
        }
        _ => panic!("division WD by construction"),
    }
    let error = compile_run(&result, &runtime, "missing_division_requirement")
        .expect_err("reflexivity cannot skip construction legality");
    assert_eq!(error.route, "WD/Arithmetic");
}

#[test]
fn presentation_strings_do_not_determine_the_generated_proof() {
    let (mut result, runtime) = execute("1 = 1\n$is_set(1)\n");
    let original = compile_run(&result, &runtime, "presentation_independence")
        .expect("supported typed results");
    result.statement_texts = vec!["trust 1 = 2".to_string(), "unrelated display".to_string()];
    result.normal_json = Some("not a proof or even valid JSON".to_string());
    let altered = compile_run(&result, &runtime, "presentation_independence")
        .expect("presentation has no proof role");
    assert_eq!(original, altered);
}

#[test]
fn live_wd_cache_does_not_replace_a_missing_replayed_producer() {
    let (mut result, runtime) = execute("1 = 1\n$is_set(1)\n");
    assert!(compile_run(&result, &runtime, "complete_producers").is_ok());
    result.statement_results.remove(0);
    let error = compile_run(&result, &runtime, "missing_constructor")
        .expect_err("the live cache contains a subject, not an emitted proof");
    assert_eq!(error.route, "WD/Producer");
}

#[test]
fn known_membership_replays_all_argument_identity_evidence() {
    let (mut result, runtime) = execute("forall a R:\n    a $in C\n");
    assert!(compile_run(&result, &runtime, "complete_argument_evidence").is_ok());
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let atomic = match &mut forall.proved_then_facts[0].verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified membership"),
        },
        _ => panic!("atomic result"),
    };
    let child = match &mut atomic.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
            match &mut proof.reason {
                StructuralMembershipReason::StandardSuperset(child) => child,
                _ => panic!("standard-superset route"),
            }
        }
        _ => panic!("structural membership"),
    };
    match &mut child.reason {
        StructuralMembershipReason::Known(proof) => {
            proof.why_parameters_of_known_fact_are_equal_to_givens.pop();
        }
        _ => panic!("membership citation"),
    }
    let error = compile_run(&result, &runtime, "missing_argument_evidence")
        .expect_err("a citation must not discard its transport evidence");
    assert_eq!(error.route, "KnownAtomic");
}

fn forall_proof_mut(result: &mut ExecStmtResult) -> &mut VerifyForallFactSuccess {
    match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
            match &mut success.verify_result {
                VerifyFactResult::ForallFact(proof) => match proof.as_mut() {
                    VerifyForallFactResult::Success(
                        VerifyForallFactProof::ByLocalIntroduction(proof),
                    ) => proof,
                    _ => panic!("local-introduction forall"),
                },
                _ => panic!("forall result"),
            }
        }
        _ => panic!("successful fact"),
    }
}
