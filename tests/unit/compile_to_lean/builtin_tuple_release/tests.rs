use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCE: &str = "thm recover_point:\n    ? forall p cart(R, R):\n        p = (p(1), p(2))\n    release thm tuple_equal_from_coordinates(p, (p(1), p(2)))\n";

fn release(result: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(proof),
    )) = &mut result.statement_results[0]
    else {
        panic!("source theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut proof.body else {
        panic!("forall proof")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(proof),
    )) = &mut body.proof_steps[0]
    else {
        panic!("builtin tuple release")
    };
    proof
}

#[test]
fn builtin_tuple_release_replays_its_domains_and_every_coordinate() {
    let (mut result, compiler) = super::execute(SOURCE);
    assert_eq!(release(&mut result).dom_proofs.len(), 2);
    assert!(compiler
        .compile_run(&result, "tuple_release")
        .unwrap()
        .contains("Litex.FiniteFunction.cart_ext"));
}

#[test]
fn builtin_tuple_release_rejects_missing_or_reordered_coordinates() {
    for missing in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = release(&mut result);
        if missing {
            proof.dom_proofs.pop();
        } else {
            proof.dom_proofs.swap(0, 1);
        }
        compiler
            .compile_run(&result, "corrupt_tuple_release")
            .expect_err("each original ordered coordinate proof is required");
    }
}

#[test]
fn builtin_tuple_release_rejects_a_missing_complete_domain() {
    let (mut result, compiler) = super::execute(SOURCE);
    release(&mut result).function_domain = None;
    assert_eq!(
        compiler
            .compile_run(&result, "missing_domain")
            .unwrap_err()
            .route,
        "TupleTheorem/CompleteDomains"
    );
}
