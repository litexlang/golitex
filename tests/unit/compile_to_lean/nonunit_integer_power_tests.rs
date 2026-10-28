use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    verify_atomic_except_equality::{
        result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
        search_atomic_except_equality_fact_proof_by_builtin_rules::{
            common_relation_nonzero::PositiveNonunitIntegerPowerProof,
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
    include_str!("../../../lean/examples/positive_nonunit_integer_power/statement.lit");
const ABOVE: &str =
    include_str!("../../../lean/examples/nonunit_integer_power_above_one/statement.lit");
const BELOW: &str =
    include_str!("../../../lean/examples/nonunit_integer_power_below_one/statement.lit");
const NEGATIVE: &str =
    include_str!("../../../lean/examples/nonunit_negative_integer_power/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut PositiveNonunitIntegerPowerProof {
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
            NotEqualFactSearchProofByBuiltinRule::PositiveNonunitIntegerPower(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected nonunit integer power rule")
    };
    rule
}

#[test]
fn nonunit_integer_power_replays_all_base_guard_variants() {
    for (source, variant) in [(NONUNIT, 0), (ABOVE, 1), (BELOW, 2)] {
        let (mut run, compiler) = super::execute(source);
        let guard = &selected_rule(&mut run).base_proof;
        assert!(match variant {
            0 => matches!(guard, LogAlgebraBaseProof::PositiveNonunit(_)),
            1 => matches!(guard, LogAlgebraBaseProof::GreaterThanOne(_)),
            _ => matches!(guard, LogAlgebraBaseProof::BelowOne(_)),
        });
        let lean = compiler
            .compile_run(&run, "nonunit_integer_power")
            .expect(source);
        assert!(lean.contains("Litex.powerNonunitOfGuards"));
    }
    let (mut run, compiler) = super::execute(NEGATIVE);
    selected_rule(&mut run);
    compiler
        .compile_run(&run, "negative_nonunit_power")
        .unwrap();
}

#[test]
fn nonunit_integer_power_rejects_wrong_exponent_evidence() {
    for change in ["integer", "nonzero"] {
        let (mut run, compiler) = super::execute(NONUNIT);
        let rule = selected_rule(&mut run);
        let evidence = if change == "integer" {
            &mut rule.exponent_integer
        } else {
            &mut rule.exponent_nonzero
        };
        let VerifyFactResult::AtomicExceptEquality(result) = evidence else {
            panic!("atomic premise")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
            panic!("verified premise")
        };
        let wrong = Obj::Literal(Literal::Number(Number::new("3".into())));
        match &mut proof.fact {
            AtomicFact::InFact(f) => f.element = wrong,
            AtomicFact::NotEqualFact(f) => f.left = wrong,
            _ => panic!("unexpected premise"),
        }
        compiler
            .compile_run(&run, "wrong_power_exponent")
            .expect_err(change);
    }
}

#[test]
fn nonunit_integer_power_rejects_wrong_base_guard_and_missing_wd() {
    for change in ["base", "wd"] {
        let (mut run, compiler) = super::execute(NONUNIT);
        if change == "base" {
            let LogAlgebraBaseProof::PositiveNonunit(guard) =
                &mut selected_rule(&mut run).base_proof
            else {
                panic!("nonunit guard")
            };
            let VerifyFactResult::AtomicExceptEquality(result) = &mut guard.nonunit_proof else {
                panic!("atomic guard")
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
                panic!("verified guard")
            };
            let AtomicFact::NotEqualFact(fact) = &mut proof.fact else {
                panic!("nonunit fact")
            };
            fact.left = Obj::Literal(Literal::Number(Number::new("3".into())));
        } else {
            let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
                ExecClaimStmtResult::Success(claim),
            )) = &mut run.statement_results[0]
            else {
                panic!("successful claim")
            };
            let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
                panic!("forall body")
            };
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
                &mut body.proof_steps[0]
            else {
                panic!("successful fact")
            };
            let VerifyFactResult::AtomicExceptEquality(result) = &mut statement.verify_result
            else {
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
        }
        compiler
            .compile_run(&run, "wrong_nonunit_power")
            .expect_err(change);
    }
}

#[test]
fn unit_or_zero_exponent_is_not_proved_nonunit() {
    for source in ["2^0 != 1", "1^3 != 1"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
