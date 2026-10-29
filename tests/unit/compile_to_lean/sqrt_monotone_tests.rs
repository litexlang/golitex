use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::{
        less_equal::LessEqualFactSearchProofByBuiltinRule,
        sqrt_defined_order::SqrtMonotoneFromDefinedRootsProof,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/sqrt_monotone/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut SqrtMonotoneFromDefinedRootsProof {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &mut run.statement_results[0]
    else {
        panic!("successful claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &mut body.proof_steps[0]
    else {
        panic!("successful fact")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &mut statement.verify_result else {
        panic!("atomic fact")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified fact")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::SqrtMonotoneFromDefinedRoots(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected square-root monotonicity")
    };
    rule
}

#[test]
fn sqrt_monotonicity_replays_selected_argument_order() {
    let (mut run, compiler) = super::execute(SOURCE);
    selected_rule(&mut run);
    let lean = compiler.compile_run(&run, "sqrt_monotone").unwrap();
    assert!(lean.contains("Litex.sqrtMonotone"));
    let reversed =
        include_str!("../../../lean/examples/sqrt_monotone_reversed_premise/statement.lit");
    let (mut run, compiler) = super::execute(reversed);
    selected_rule(&mut run);
    assert!(compiler
        .compile_run(&run, "sqrt_monotone_reversed")
        .unwrap()
        .contains("Litex.sqrtMonotone"));
}

#[test]
fn sqrt_monotonicity_rejects_changed_premise() {
    let (mut run, compiler) = super::execute(SOURCE);
    let VerifyFactResult::AtomicExceptEquality(result) =
        &mut selected_rule(&mut run).arguments_order
    else {
        panic!("atomic premise")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified premise")
    };
    let AtomicFact::LessEqualFact(fact) = &mut proof.fact else {
        panic!("weak order premise")
    };
    fact.right = Obj::Literal(Literal::Number(Number::new("3".into())));
    compiler
        .compile_run(&run, "invalid_sqrt_monotone")
        .expect_err("wrong premise");
}

#[test]
fn sqrt_monotonicity_requires_goal_wd_and_nonnegative_domain() {
    let (mut run, compiler) = super::execute(SOURCE);
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("forall")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &mut body.proof_steps[0] else {
        panic!("fact")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &mut stmt.verify_result else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified")
    };
    proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter
        .clear();
    compiler
        .compile_run(&run, "missing_sqrt_order_wd")
        .expect_err("missing goal WD");
    let source = "claim:\n    ? forall x R, y R:\n        x <= y\n        =>:\n            sqrt(x) <= sqrt(y)\n    sqrt(x) <= sqrt(y)";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
