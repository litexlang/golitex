use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{
        InequalityFromSumNonzeroBuiltinRuleProof, NotEqualFactSearchProofByBuiltinRule,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../lean/examples/inequality_from_nonzero_sum/statement.lit");
const REVERSED: &str =
    include_str!("../../../lean/examples/inequality_from_reversed_nonzero_sum/statement.lit");
const SWAPPED: &str =
    include_str!("../../../lean/examples/inequality_from_swapped_nonzero_sum/statement.lit");
const ZERO_SUB: &str =
    include_str!("../../../lean/examples/inequality_zero_sub_from_nonzero_sum/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut InequalityFromSumNonzeroBuiltinRuleProof {
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
            NotEqualFactSearchProofByBuiltinRule::InequalityFromSumNonzero(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected nonzero sum rule")
    };
    rule
}

#[test]
fn nonzero_sum_replays_exact_citation_and_orientations() {
    for source in [SOURCE, REVERSED, SWAPPED, ZERO_SUB] {
        let (mut run, compiler) = super::execute(source);
        let id = selected_rule(&mut run)
            .premise_proof
            .cite_fact_id()
            .expect("fact id");
        let lean = compiler
            .compile_run(&run, "nonzero_sum_inequality")
            .expect(source);
        assert!(lean.contains("Litex.notSameNegOfNonzeroSum"));
        assert!(lean.contains(&format!("h_{}", id.value())));
    }
}

#[test]
fn nonzero_sum_rejects_wrong_citation_or_subject() {
    for change in ["citation", "subject", "zero"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let premise = &mut selected_rule(&mut run).premise_proof;
        match change {
            "citation" => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                    premise.searched_proof.as_mut()
                else {
                    panic!("known fact")
                };
                known.cite_fact_id = FactId::new(u64::MAX);
            }
            "subject" => {
                let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                    panic!("nonzero fact")
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &mut fact.left else {
                    panic!("sum")
                };
                sum.left = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
            }
            _ => {
                let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                    panic!("nonzero fact")
                };
                fact.right = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
        }
        compiler
            .compile_run(&run, "wrong_nonzero_sum")
            .expect_err(change);
    }
}

#[test]
fn nonzero_sum_rejects_missing_goal_wd() {
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
        .compile_run(&run, "missing_nonzero_sum_wd")
        .expect_err("missing goal WD");
}

#[test]
fn nonzero_sum_premise_is_required() {
    let source = "claim:\n    ? forall a C, b C:\n        =>:\n            a != -b\n    a != -b\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
