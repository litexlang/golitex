use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{
        AbsNonzeroFromArgBuiltinRuleProof, NotEqualFactSearchProofByBuiltinRule,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/absolute_value_nonzero/statement.lit");
const REVERSED: &str =
    include_str!("../../../lean/examples/absolute_value_nonzero_reversed/statement.lit");
const COMPUTED_ZERO: &str =
    include_str!("../../../lean/examples/absolute_value_nonzero_computed_zero/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut AbsNonzeroFromArgBuiltinRuleProof {
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
            NotEqualFactSearchProofByBuiltinRule::AbsNonzeroFromArg(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected abs nonzero rule")
    };
    rule
}

#[test]
fn abs_nonzero_replays_selected_rule_and_original_premise() {
    for source in [SOURCE, REVERSED, COMPUTED_ZERO] {
        let (mut run, compiler) = super::execute(source);
        selected_rule(&mut run);
        let lean = compiler.compile_run(&run, "abs_nonzero").expect(source);
        assert!(lean.contains("Litex.absNonzeroOfArg"));
    }
}

#[test]
fn abs_nonzero_rejects_nonzero_proof_about_another_argument() {
    let (mut run, compiler) = super::execute(SOURCE);
    let premise = &mut selected_rule(&mut run).arg_nonzero_proof;
    let VerifyFactResult::AtomicExceptEquality(result) = premise else {
        panic!("atomic nonzero premise")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified premise")
    };
    let AtomicFact::NotEqualFact(fact) = &mut proof.fact else {
        panic!("nonzero fact")
    };
    fact.left = Obj::Literal(Literal::Number(Number::new("3".into())));
    compiler
        .compile_run(&run, "wrong_abs_argument")
        .expect_err("different argument");
}

#[test]
fn zero_absolute_value_is_not_proved_nonzero() {
    let source = "have x R = 0\n|x| != 0";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
