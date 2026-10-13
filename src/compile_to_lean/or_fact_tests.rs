use super::LitexToLeanCompiler;
use crate::prelude::*;

const SOURCE: &str =
    "claim:\n    ? forall n N:\n        n = 0 or n > 0\n    n >= 0\nhave n N\nn = 0 or n > 0\n";

fn checked() -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(SOURCE).expect("Or source");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

#[test]
fn or_replays_integer_coverage_and_exact_known_forall_instantiation() {
    let (result, compiler) = checked();
    let lean = compiler
        .compile_run(&result, "original_or_coverage")
        .expect("Or original routes");
    assert!(lean.contains("Litex.integerSuccessorTail"));
    assert!(lean.contains("Or.elim"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn or_rejects_missing_original_branch_formation() {
    let (mut result, compiler) = checked();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[2]
    else {
        panic!("source Or");
    };
    let VerifyFactResult::OrFact(verify) = &mut fact.verify_result else {
        panic!("Or result");
    };
    let VerifyOrFactResult::Success(proof) = verify.as_mut() else {
        panic!("Or success");
    };
    proof.well_defined_proof.branches.clear();
    assert!(compiler
        .compile_run(&result, "missing_or_wd")
        .unwrap_err()
        .route
        .contains("FormationArity"));
}

#[test]
fn or_rejects_changed_original_branch_subject() {
    let (mut result, compiler) = checked();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[2]
    else {
        panic!("source Or");
    };
    let VerifyFactResult::OrFact(verify) = &mut fact.verify_result else {
        panic!("Or result");
    };
    let VerifyOrFactResult::Success(proof) = verify.as_mut() else {
        panic!("Or success");
    };
    proof.fact.facts.swap(0, 1);
    assert!(compiler.compile_run(&result, "changed_or_subject").is_err());
}

#[test]
fn or_integer_tail_rejects_swapped_original_memberships() {
    use crate::execute::execute_proof_block_stmt::{
        ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
    };
    let (mut result, compiler) = checked();
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &mut result.statement_results[0]
    else {
        panic!("original claim");
    };
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("universal claim");
    };
    let VerifyFactResult::OrFact(verify) = &mut body.conclusion_proofs[0] else {
        panic!("original disjunction");
    };
    let VerifyOrFactResult::Success(proof) = verify.as_mut() else {
        panic!("successful disjunction");
    };
    let OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(
        selected,
    )) = &mut proof.searched_proof
    else {
        panic!("selected integer coverage");
    };
    std::mem::swap(&mut selected.subject_in_z, &mut selected.base_in_z);
    assert_eq!(
        compiler
            .compile_run(&result, "swapped_integer_memberships")
            .unwrap_err()
            .route,
        "Or/IntegerTailMembership"
    );
}
