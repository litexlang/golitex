use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::AddObjWellDefinedProof;
use crate::execute::ExecDefThmForallProof;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../../lean/examples/nested_named_add_zero/statement.lit");
const RECIPROCAL_SOURCE: &str = "prop is_nonzero(x R):\n    x != 0\n\nhave fn reciprocal(x R: x != 0) R = 1 / x\n\nthm reciprocal_product:\n    ? forall x R:\n        $is_nonzero(x)\n        =>:\n            reciprocal(x) * x = 1\n    reciprocal(x) = 1 / x\n    reciprocal(x) * x = (1 / x) * x\n    (1 / x) * x = 1\n\nhave denominator R = 2\nby def $is_nonzero(denominator)\nlet answer = reciprocal(denominator)\nby thm reciprocal_product(denominator) => reciprocal(denominator) * denominator = 1\nreciprocal(denominator) = 1 / denominator\n1 / denominator = 1 / 2\nanswer = 1 / 2\n";

fn theorem_body(result: &mut ExecStmtResult) -> &mut ExecDefThmForallProof {
    match &mut super::named_theorem_mut(result).body {
        ExecDefThmBodyProof::Forall(proof) => proof,
        _ => panic!("actual forall theorem body"),
    }
}

fn caller_wd(proof: &mut ExecByThmStmtSuccess) -> &mut EqualFactWellDefinedProof {
    match &mut proof.selected_wd {
        FactWellDefinedProof::Equality(wd) => wd,
        _ => panic!("actual equality caller WD"),
    }
}

fn caller_add(proof: &mut ExecByThmStmtSuccess) -> &mut AddObjWellDefinedProof {
    match &mut caller_wd(proof).left {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Add(proof),
                ),
            ..
        } => proof,
        _ => panic!("actual caller construction of the selected sum"),
    }
}

#[test]
fn named_call_wd_retains_the_caller_construction_after_closing_the_call() {
    let (mut result, compiler) = super::execute(SOURCE);
    let body = theorem_body(&mut result.statement_results[1]);
    assert_eq!(
        body.proof_steps.len(),
        1,
        "the body is the original direct call"
    );
    let call = super::by_theorem_mut(&mut body.proof_steps[0]);
    assert!(matches!(
        caller_wd(call).left,
        ObjWellDefinedProof::ByDef { .. }
    ));
    assert_eq!(caller_add(call).child_obj_well_defined.len(), 2);
    let output = super::compile_run(&result, &compiler, "nested_named_add_zero")
        .expect("the caller's actual WD construction closes the named theorem");
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn named_call_wd_rejects_a_deleted_reordered_or_wrong_caller_construction() {
    for change in ["deleted", "reordered", "wrong"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let call = super::by_theorem_mut(
            &mut theorem_body(&mut result.statement_results[1]).proof_steps[0],
        );
        match change {
            "deleted" => caller_add(call).child_obj_well_defined.clear(),
            "reordered" => caller_add(call).child_obj_well_defined.swap(0, 1),
            "wrong" => {
                super::replace_wd_subject(&mut caller_wd(call).left, super::number_object("7"))
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["WD/"]);
    }
}

#[test]
fn named_call_wd_cannot_replace_the_caller_construction_with_closed_call_wd() {
    let (mut result, compiler) = super::execute(SOURCE);
    let call =
        super::by_theorem_mut(&mut theorem_body(&mut result.statement_results[1]).proof_steps[0]);
    let (obj, wd_id) = match &super::equality_proof(&call.selected_proof)
        .well_defined_proof
        .left
    {
        ObjWellDefinedProof::ByKnown { obj, wd_id } => (obj.clone(), *wd_id),
        _ => panic!("selection cites the call-local construction"),
    };
    caller_wd(call).left = ObjWellDefinedProof::ByKnown { obj, wd_id };
    super::phase2_rejected(&result, &compiler, "closed_call_wd", &["WdId/", "WD/"]);
}

#[test]
fn named_call_wd_cannot_use_the_cache_id_created_by_its_own_later_store() {
    let source = format!("{SOURCE}    let later = y + 0\n");
    let (mut result, compiler) = super::execute(&source);
    super::compile_run(&result, &compiler, "caller_store_order").unwrap();
    let body = theorem_body(&mut result.statement_results[1]);
    let (obj, wd_id) = match &super::let_definition(&body.proof_steps[1]).value_well_defined {
        VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByKnown { obj, wd_id }) => {
            (obj.clone(), *wd_id)
        }
        _ => panic!("the later alias cites the completed caller construction's WD cache"),
    };
    let call = super::by_theorem_mut(&mut body.proof_steps[0]);
    caller_wd(call).left = ObjWellDefinedProof::ByKnown { obj, wd_id };
    super::phase2_rejected(&result, &compiler, "future_caller_store", &["WD/"]);
}

#[test]
fn named_call_wd_cannot_use_a_closed_or_future_membership_producer() {
    let source = "thm add_zero:\n    ? forall x C:\n        x + 0 = x\nthm add_zero_again:\n    ? forall y C:\n        y + 0 = y\n    by thm add_zero(y) => y + 0 = y\n    y $in C\n";
    for change in ["closed", "future"] {
        let (mut result, compiler) = super::execute(source);
        super::compile_run(&result, &compiler, "ordered_caller_wd").unwrap();
        let body = theorem_body(&mut result.statement_results[1]);
        let future = super::fact_statement(&body.proof_steps[1])
            .store_and_infer_result
            .primary_fact_id();
        let call = super::by_theorem_mut(&mut body.proof_steps[0]);
        let closed = super::atomic_proof_mut(&mut call.type_proofs[0])
            .fact
            .fact_id();
        let requirement =
            super::atomic_proof_mut(&mut caller_add(call).requirement_fact_verified[0]);
        match &mut requirement.searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                proof.cite_fact_id = if change == "future" { future } else { closed };
            }
            _ => panic!("actual caller membership citation"),
        }
        super::phase2_rejected(&result, &compiler, change, &["FactId/"]);
    }
}

#[test]
fn named_call_wd_replays_the_original_guarded_reciprocal_call_order() {
    let (result, compiler) = super::execute(RECIPROCAL_SOURCE);
    let output = super::compile_run(&result, &compiler, "guarded_reciprocal_call")
        .expect("the original guarded call's caller WD is retained before its final store");
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn named_call_wd_keeps_missing_guards_and_false_selections_rejected() {
    for source in [
        "thm divide_self:\n    ? forall x C:\n        x != 0\n        =>:\n            x / x = 1\nhave d C\nby thm divide_self(d) => d / d = 1\n",
        "thm add_zero:\n    ? forall x R:\n        x + 0 = x\nby thm add_zero(2) => 2 + 0 = 3\n",
    ] {
        let command = parse_launch_command(&[
            "-strict".to_string(),
            "-e".to_string(),
            source.to_string(),
        ])
        .unwrap();
        let mut runtime = Runtime::new(command);
        let result = runtime.run_litex_code(source).unwrap();
        assert!(!result.success && result.session_error.is_none());
        let last = result.statement_results.len() - 1;
        assert!(result.statement_results[..last]
            .iter()
            .all(|statement| !statement.is_failed()));
        assert!(matches!(
            result.statement_results[last],
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(_)))
        ));
        let compiler = super::LitexToLeanCompiler::new(runtime);
        let error = super::compile_run(&result, &compiler, "invalid_named_call")
            .expect_err("an invalid invocation cannot become a compiled source run");
        assert_eq!(error.route, "source_failed");
    }
}
