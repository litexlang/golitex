use super::source_position::{SourceOwner, SourcePosition};
use super::LitexToLeanCompiler;
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecClaimStmtSuccess, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const PLAIN: &str = "claim:\n    ? 1 = 1\n    1 = 1\n1 = 1\n";
const FORALL: &str = "claim:\n    ? forall x R:\n        x != 0\n        =>:\n            x / x = 1\n    x / x = 1\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn claim(statement: &ExecStmtResult) -> &ExecClaimStmtSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = statement
    else {
        panic!("successful claim result");
    };
    claim
}

fn claim_mut(statement: &mut ExecStmtResult) -> &mut ExecClaimStmtSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = statement
    else {
        panic!("successful claim result");
    };
    claim
}

fn forall_mut(
    claim: &mut ExecClaimStmtSuccess,
) -> &mut crate::execute::execute_proof_block_stmt::ExecClaimForallProof {
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("forall body");
    };
    body
}

#[test]
fn plain_claim_replays_body_conclusion_and_parent_store() {
    let (result, compiler) = checked(PLAIN);
    let claim = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::NonForall(body) = &claim.body else {
        panic!("direct goal body");
    };
    assert_eq!(body.proof_steps.len(), claim.statement.proof.len());
    assert_eq!(
        claim.stored.primary_fact_id(),
        claim.statement.fact.fact_id()
    );
    let lean = compiler
        .compile_run(&result, "plain_claim")
        .expect("claim replay");
    assert!(lean.contains(&format!(
        "theorem h_{}",
        claim.statement.fact.fact_id().value()
    )));
    assert!(!lean.contains("sorry"));
}

#[test]
fn forall_claim_captures_distinct_original_and_body_headers() {
    let (result, compiler) = checked(FORALL);
    let claim = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::Forall(body) = &claim.body else {
        panic!("forall body");
    };
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) =
        &claim.goal_wd
    else {
        panic!("original goal formation");
    };
    assert_eq!(
        body.introduced_params
            .defined_params
            .store_and_infer_results
            .len(),
        1
    );
    assert_eq!(body.assumed_dom_facts.len(), 1);
    assert_ne!(
        goal.introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id(),
        body.introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id(),
    );
    compiler
        .compile_run(&result, "forall_claim")
        .expect("both captured headers replay");
}

#[test]
fn claim_replays_body_local_have_without_exporting_its_identifier() {
    let source = "claim:\n    ? forall x R:\n        x + 0 = x\n    have helper R = x\n    helper + 0 = helper\n    x + 0 = x\n";
    let (result, compiler) = checked(source);
    compiler
        .compile_run(&result, "claim_local_have")
        .expect("ordered local producer replay");
}

#[test]
fn named_route_replays_the_same_real_parameter_alias_capture() {
    let source = "thm alias_claim_comparison:\n    ? forall x R:\n        x + 0 = x\n    have helper R = x\n    helper + 0 = helper\n    x + 0 = x\n";
    let (result, compiler) = checked(source);
    compiler
        .compile_run(&result, "named_real_parameter_alias")
        .expect("the same shared numeric WD route has its actual R header certificate");
}

#[test]
fn claim_local_alias_identifier_cannot_be_seen_early_or_escape_after_store() {
    let source = "claim:\n    ? forall x R:\n        x + 0 = x\n    have helper R = x\n    helper + 0 = helper\n    x + 0 = x\n";
    let (result, compiler) = checked(source);
    let proof = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::Forall(body) = &proof.body else {
        panic!("actual forall body")
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(alias)),
    )) = &body.proof_steps[0]
    else {
        panic!("actual typed alias producer")
    };
    let object = Obj::Identifier(IdentifierObj::from_bound_name(
        &alias.statement.param_def.groups[0].params[0],
    ));
    let original = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let early = SourcePosition::new(Some(&original), SourceOwner::Claim(proof), 1);
    assert_eq!(
        compiler
            .compile_object_reference(&object, &early)
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
    let completed_alias = SourcePosition { before: 2, ..early };
    assert!(compiler
        .compile_object_reference(&object, &completed_alias)
        .is_ok());
    let closed = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert_eq!(
        compiler
            .compile_object_reference(&object, &closed)
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
}

#[test]
fn claim_cursor_rejects_future_body_fact_and_seals_helper_after_store() {
    let (result, compiler) = checked(FORALL);
    let proof = claim(&result.statement_results[0]);
    let ExecClaimBodyProof::Forall(body) = &proof.body else {
        panic!("forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &body.proof_steps[0] else {
        panic!("actual body fact");
    };
    let helper = step.store_and_infer_result.primary_fact_id();
    let outer = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let before_body = SourcePosition::new(Some(&outer), SourceOwner::Claim(proof), 2);
    assert_eq!(
        before_body
            .visible_fact(helper, &compiler.runtime)
            .unwrap_err()
            .route,
        "FactId/Producer"
    );
    let after_body = SourcePosition {
        before: 3,
        ..before_body
    };
    assert!(after_body.visible_fact(helper, &compiler.runtime).is_ok());
    let sealed = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert!(sealed.visible_fact(helper, &compiler.runtime).is_err());
    assert!(sealed
        .visible_fact(proof.stored.primary_fact_id(), &compiler.runtime)
        .is_ok());
}

#[test]
fn claim_rejects_missing_actual_parameter_introduction() {
    let (mut result, compiler) = checked(FORALL);
    forall_mut(claim_mut(&mut result.statement_results[0]))
        .introduced_params
        .defined_params
        .store_and_infer_results
        .clear();
    assert!(compiler
        .compile_run(&result, "missing_claim_parameter")
        .is_err());
}

#[test]
fn claim_rejects_missing_actual_domain_assumption() {
    let (mut result, compiler) = checked(FORALL);
    forall_mut(claim_mut(&mut result.statement_results[0]))
        .assumed_dom_facts
        .clear();
    let error = compiler
        .compile_run(&result, "missing_claim_domain")
        .expect_err("domain capture required");
    assert_eq!(error.route, "Forall/Domain");
}

#[test]
fn claim_rejects_missing_conclusion_and_mismatched_source_step() {
    let (mut result, compiler) = checked(FORALL);
    forall_mut(claim_mut(&mut result.statement_results[0]))
        .conclusion_proofs
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_claim_conclusion")
            .unwrap_err()
            .route,
        "Claim/Stages"
    );
    let (mut result, compiler) = checked(PLAIN);
    claim_mut(&mut result.statement_results[0])
        .statement
        .proof
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_claim_source_step")
            .unwrap_err()
            .route,
        "Claim/Stages"
    );
}

#[test]
fn claim_rejects_original_goal_that_differs_from_parent_store() {
    let (mut result, compiler) =
        checked("claim:\n    ? 1 = 1\n    1 = 1\nclaim:\n    ? 2 = 2\n    2 = 2\n");
    let other = claim(&result.statement_results[1]).statement.fact.clone();
    claim_mut(&mut result.statement_results[0]).statement.fact = other;
    assert!(compiler.compile_run(&result, "claim_other_goal").is_err());
}

#[test]
fn sketch_checks_its_body_without_a_claim_conclusion() {
    let (result, compiler) = checked("sketch:\n    1 = 1\n");
    let lean = compiler.compile_run(&result, "sketch_boundary").unwrap();
    assert!(lean.contains("private theorem _sketch_1"));
    assert!(!lean.lines().any(|line| line.starts_with("theorem h_")));
}
