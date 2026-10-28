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

const TAN: &str = include_str!("../../../lean/examples/tangent_nonzero_from_sine/statement.lit");
const COT: &str =
    include_str!("../../../lean/examples/cotangent_nonzero_from_cosine/statement.lit");
const TAN_REV: &str =
    include_str!("../../../lean/examples/tangent_nonzero_from_sine_reversed/statement.lit");
const COT_REV: &str =
    include_str!("../../../lean/examples/cotangent_nonzero_from_cosine_reversed/statement.lit");

fn selected_premise(
    run: &mut RunLitexCodeResult,
    tangent: bool,
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
        NotEqualFactSearchProofByBuiltinRule::TanNonzeroFromSin(p) if tangent => {
            &mut p.numerator_nonzero
        }
        NotEqualFactSearchProofByBuiltinRule::CotNonzeroFromCos(p) if !tangent => {
            &mut p.numerator_nonzero
        }
        _ => panic!("wrong selected trig rule"),
    }
}

#[test]
fn trig_quotient_nonzero_replays_recorded_numerator_citation() {
    for (source, tangent, theorem) in [
        (TAN, true, "Litex.tanNonzeroOfSin"),
        (COT, false, "Litex.cotNonzeroOfCos"),
        (TAN_REV, true, "Litex.tanNonzeroOfSin"),
        (COT_REV, false, "Litex.cotNonzeroOfCos"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let id = selected_premise(&mut run, tangent)
            .cite_fact_id()
            .expect("fact id");
        let lean = compiler
            .compile_run(&run, "trig_quotient_nonzero")
            .expect(source);
        assert!(lean.contains(theorem));
        assert!(lean.contains(&format!("h_{}", id.value())));
    }
}

#[test]
fn trig_quotient_nonzero_rejects_wrong_citation_or_argument() {
    for (source, tangent) in [(TAN, true), (COT, false)] {
        for change in ["citation", "argument", "zero"] {
            let (mut run, compiler) = super::execute(source);
            let premise = selected_premise(&mut run, tangent);
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
                        _ => panic!("trig numerator"),
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
                .compile_run(&run, "wrong_trig_quotient")
                .expect_err(change);
        }
    }
}

#[test]
fn trig_quotient_nonzero_rejects_missing_goal_wd() {
    for source in [TAN, COT] {
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
            .compile_run(&run, "missing_trig_quotient_wd")
            .expect_err("missing object WD");
    }
}

#[test]
fn trig_quotient_requires_nonzero_numerator_and_domain() {
    for source in ["tan(0) != 0", "cot(0) != 0"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
