use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    verify_atomic_except_equality::{
        result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
        search_atomic_except_equality_fact_proof_by_builtin_rules::{
            common_relation_nonzero::LogNonzeroFromNonunitArgumentProof,
            not_equal::NotEqualFactSearchProofByBuiltinRule,
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule,
    },
    verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const NONUNIT: &str =
    include_str!("../../../lean/examples/log_nonzero_positive_nonunit/statement.lit");
const ABOVE: &str = include_str!("../../../lean/examples/log_nonzero_above_one/statement.lit");
const BELOW: &str = include_str!("../../../lean/examples/log_nonzero_below_one/statement.lit");
const MIXED: &str = include_str!("../../../lean/examples/log_nonzero_mixed_guards/statement.lit");
const REVERSED: &str = include_str!("../../../lean/examples/log_nonzero_reversed/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut LogNonzeroFromNonunitArgumentProof {
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
            NotEqualFactSearchProofByBuiltinRule::LogNonzeroFromNonunitArgument(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected log nonzero rule")
    };
    rule
}

#[test]
fn log_nonzero_replays_all_three_selected_guard_variants() {
    for (source, variant) in [(NONUNIT, 0), (ABOVE, 1), (BELOW, 2)] {
        let (mut run, compiler) = super::execute(source);
        let rule = selected_rule(&mut run);
        let correct = |g: &LogAlgebraBaseProof| match variant {
            0 => matches!(g, LogAlgebraBaseProof::PositiveNonunit(_)),
            1 => matches!(g, LogAlgebraBaseProof::GreaterThanOne(_)),
            _ => matches!(g, LogAlgebraBaseProof::BelowOne(_)),
        };
        assert!(correct(&rule.base_proof) && correct(&rule.argument_proof));
        let lean = compiler.compile_run(&run, "log_nonzero").expect(source);
        assert!(lean.contains("Litex.logNonzeroOfGuards"));
    }
    for source in [MIXED, REVERSED] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "log_nonzero_reversed").unwrap();
    }
}

#[test]
fn log_nonzero_rejects_swapped_guards() {
    let (mut run, compiler) = super::execute(NONUNIT);
    let rule = selected_rule(&mut run);
    std::mem::swap(&mut rule.base_proof, &mut rule.argument_proof);
    compiler
        .compile_run(&run, "wrong_log_guards")
        .expect_err("swapped subjects");
}

#[test]
fn log_nonzero_rejects_missing_object_wd() {
    let (mut run, compiler) = super::execute(NONUNIT);
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
        .compile_run(&run, "missing_log_wd")
        .expect_err("missing object WD");
}

#[test]
fn logarithm_of_one_is_not_proved_nonzero() {
    let command =
        parse_launch_command(&["-strict".into(), "-e".into(), "log(2,1) != 0".into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code("log(2,1) != 0").unwrap().success);
}
