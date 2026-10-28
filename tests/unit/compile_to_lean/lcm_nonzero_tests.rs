use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::{
        common_relation_nonzero::LcmNonzeroFromNonzeroOperandsProof,
        not_equal::NotEqualFactSearchProofByBuiltinRule,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/lcm_nonzero/statement.lit");
const REVERSED: &str = include_str!("../../../lean/examples/lcm_nonzero_reversed/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut LcmNonzeroFromNonzeroOperandsProof {
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::LcmNonzeroFromNonzeroOperands(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected lcm nonzero rule")
    };
    rule
}

#[test]
fn lcm_nonzero_replays_both_recorded_premises() {
    let (mut run, compiler) = super::execute(SOURCE);
    selected_rule(&mut run);
    let lean = compiler.compile_run(&run, "lcm_nonzero").unwrap();
    assert!(lean.contains("Litex.lcmNonzeroOfArgs"));
    let (run, compiler) = super::execute(REVERSED);
    compiler.compile_run(&run, "lcm_nonzero_reversed").unwrap();
}

#[test]
fn lcm_nonzero_rejects_swapped_premises() {
    let (mut run, compiler) = super::execute(SOURCE);
    let rule = selected_rule(&mut run);
    std::mem::swap(&mut rule.first_nonzero, &mut rule.second_nonzero);
    compiler
        .compile_run(&run, "wrong_lcm_premises")
        .expect_err("swapped operands");
}

#[test]
fn lcm_nonzero_rejects_missing_object_wd() {
    let (mut run, compiler) = super::execute(SOURCE);
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
    proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter
        .clear();
    compiler
        .compile_run(&run, "missing_lcm_wd")
        .expect_err("missing object WD");
}

#[test]
fn lcm_with_a_zero_operand_is_not_proved_nonzero() {
    for source in ["lcm(0,3) != 0", "lcm(3,0) != 0"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
