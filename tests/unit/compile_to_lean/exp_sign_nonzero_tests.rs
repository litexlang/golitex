use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule,
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const EXP: &str = include_str!("../../../lean/examples/real_exponential_nonzero/statement.lit");
const EXP_REVERSED: &str =
    include_str!("../../../lean/examples/real_exponential_nonzero_reversed/statement.lit");
const SIGN: &str = include_str!("../../../lean/examples/real_sign_nonzero/statement.lit");
const SIGN_REVERSED: &str =
    include_str!("../../../lean/examples/real_sign_nonzero_reversed/statement.lit");
const REFLECT: &str =
    include_str!("../../../lean/examples/real_sign_reflects_nonzero/statement.lit");
const REFLECT_REVERSED: &str =
    include_str!("../../../lean/examples/real_sign_reflects_nonzero_reversed/statement.lit");
const COMPUTED_ZERO: &str =
    include_str!("../../../lean/examples/real_sign_nonzero_computed_zero/statement.lit");

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut NotEqualFactSearchProofByBuiltinRule {
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
        panic!("selected builtin rule")
    };
    rule
}

#[test]
fn exp_and_sign_nonzero_replay_original_results() {
    for source in [
        EXP,
        EXP_REVERSED,
        SIGN,
        SIGN_REVERSED,
        REFLECT,
        REFLECT_REVERSED,
        COMPUTED_ZERO,
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "exp_sign_nonzero")
            .expect(source);
        if source == EXP || source == EXP_REVERSED {
            assert!(lean.contains("Litex.expNonzero"));
        } else {
            assert!(lean.contains("Litex.signZeroIffArgZero"));
        }
    }
}

#[test]
fn sign_nonzero_rejects_forged_citation_and_subject() {
    for change in ["citation", "subject"] {
        let (mut run, compiler) = super::execute(SIGN);
        let NotEqualFactSearchProofByBuiltinRule::SignNonzeroFromArgument(rule) =
            selected_rule(&mut run)
        else {
            panic!("sign nonzero rule")
        };
        let premise = &mut rule.argument_nonzero;
        if change == "citation" {
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                premise.searched_proof.as_mut()
            else {
                panic!("known fact")
            };
            citation.cite_fact_id = FactId::new(u64::MAX);
        } else {
            let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                panic!("nonzero fact")
            };
            fact.left = Obj::Literal(Literal::Number(Number::new("3".into())));
        }
        compiler
            .compile_run(&run, "wrong_sign_premise")
            .expect_err(change);
    }
}

#[test]
fn sign_reflection_rejects_changed_real_membership_and_citation() {
    for change in ["membership", "citation"] {
        let (mut run, compiler) = super::execute(REFLECT);
        let NotEqualFactSearchProofByBuiltinRule::SignNonzeroReflection(rule) =
            selected_rule(&mut run)
        else {
            panic!("sign reflection rule")
        };
        if change == "citation" {
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                rule.sign_nonzero.searched_proof.as_mut()
            else {
                panic!("known sign fact")
            };
            citation.cite_fact_id = FactId::new(u64::MAX);
        } else {
            let VerifyFactResult::AtomicExceptEquality(result) = &mut rule.real_proof else {
                panic!("real membership")
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
                panic!("verified membership")
            };
            let AtomicFact::InFact(fact) = &mut proof.fact else {
                panic!("membership")
            };
            fact.set = Obj::StandardSet(StandardSet::C);
        }
        compiler
            .compile_run(&run, "wrong_sign_reflection")
            .expect_err(change);
    }
}

#[test]
fn zero_sign_is_not_proved_nonzero() {
    let source = "have x R = 0\nsign(x) != 0";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
