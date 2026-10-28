use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{
        AtomicExceptEqualityFactKnownProof, AtomicExceptEqualityFactSearchedProof,
        VerifyAtomicExceptEqualityFactResult,
    },
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule,
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SIN: &str = include_str!("../../../lean/examples/sine_nonzero_under_negation/statement.lit");
const COS: &str =
    include_str!("../../../lean/examples/cosine_nonzero_under_negation/statement.lit");
const SIN_ZERO: &str =
    include_str!("../../../lean/examples/sine_nonzero_under_zero_subtraction/statement.lit");
const COS_ZERO: &str =
    include_str!("../../../lean/examples/cosine_nonzero_under_zero_subtraction/statement.lit");

fn selected_premise(
    run: &mut RunLitexCodeResult,
    sine: bool,
) -> &mut AtomicExceptEqualityFactKnownProof {
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(rule),
    ) = &mut proof.searched_proof
    else {
        panic!("selected builtin")
    };
    match rule {
        NotEqualFactSearchProofByBuiltinRule::SinNonzeroNegation(p) if sine => {
            &mut p.source_nonzero
        }
        NotEqualFactSearchProofByBuiltinRule::CosNonzeroNegation(p) if !sine => {
            &mut p.source_nonzero
        }
        _ => panic!("wrong selected trig rule"),
    }
}

#[test]
fn trig_negation_replays_original_citation_and_both_spellings() {
    for (source, sine, theorem) in [
        (SIN, true, "Litex.sinNonzeroOfNegatedArg"),
        (COS, false, "Litex.cosNonzeroOfNegatedArg"),
        (SIN_ZERO, true, "Litex.sinNonzeroOfNegatedArg"),
        (COS_ZERO, false, "Litex.cosNonzeroOfNegatedArg"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let id = selected_premise(&mut run, sine)
            .cite_fact_id()
            .expect("fact id");
        let lean = compiler
            .compile_run(&run, "trig_negation_nonzero")
            .expect(source);
        assert!(lean.contains(theorem));
        assert!(lean.contains(&format!("h_{}", id.value())));
    }
}

#[test]
fn trig_negation_rejects_wrong_citation_argument_or_zero() {
    for (source, sine) in [(SIN, true), (COS, false)] {
        for change in ["citation", "argument", "zero"] {
            let (mut run, compiler) = super::execute(source);
            let premise = selected_premise(&mut run, sine);
            match change {
                "citation" => {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                        premise.searched_proof.as_mut()
                    else {
                        panic!("known fact")
                    };
                    known.cite_fact_id = FactId::new(u64::MAX);
                }
                "argument" => {
                    let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                        panic!("nonzero fact")
                    };
                    let wrong = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
                    match &mut fact.left {
                        Obj::TrigOperator(TrigOperator::Sin(p)) => p.arg = wrong,
                        Obj::TrigOperator(TrigOperator::Cos(p)) => p.arg = wrong,
                        _ => panic!("trig source"),
                    }
                }
                _ => {
                    let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                        panic!("nonzero fact")
                    };
                    fact.right = Obj::Literal(Literal::Number(Number::new("1".into())));
                }
            }
            compiler
                .compile_run(&run, "wrong_trig_negation")
                .expect_err(change);
        }
    }
}

#[test]
fn trig_negation_rejects_missing_goal_wd() {
    for source in [SIN, COS] {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(claim),
        )) = &mut run.statement_results[0]
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
            .compile_run(&run, "missing_trig_negation_wd")
            .expect_err("missing object WD");
    }
}

#[test]
fn trig_negation_requires_a_nonzero_source() {
    let source = "sin(-0) != 0";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
