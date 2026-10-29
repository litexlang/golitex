use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchedProof, AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/division_shrinks_positive/statement.lit");

fn atomic(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        p,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut p.proof_steps[0] else {
        panic!("fact")
    };
    super::atomic_proof_mut(&mut p.verify_result)
}

#[test]
fn division_shrink_replays_the_selected_positive_and_gt_one_proofs() {
    let (mut run, compiler) = super::execute(SOURCE);
    assert!(matches!(
        atomic(&mut run).searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::DivByGtOneLessSelf(_)
            )
        )
    ));
    assert!(compiler
        .compile_run(&run, "division_shrink")
        .unwrap()
        .contains("Litex.divByGtOneLessSelf"));
}

#[test]
fn division_shrink_rejects_swapped_premises() {
    let (mut run, compiler) = super::execute(SOURCE);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::DivByGtOneLessSelf(p),
        ),
    ) = &mut atomic(&mut run).searched_proof
    else {
        panic!("rule")
    };
    std::mem::swap(&mut p.numerator_pos_proof, &mut p.denominator_gt_one_proof);
    compiler
        .compile_run(&run, "swapped_division_premises")
        .expect_err("original ordered subjects required");
}

#[test]
fn division_shrink_rejects_missing_operand_wd() {
    let (mut run, compiler) = super::execute(SOURCE);
    atomic(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter
        .clear();
    compiler
        .compile_run(&run, "division_without_wd")
        .expect_err("original operand formation required");
}

#[test]
fn division_shrink_is_false_for_a_zero_numerator() {
    let source = "have a R = 0\na/2 < a";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}
