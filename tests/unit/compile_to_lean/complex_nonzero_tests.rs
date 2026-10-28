use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule,
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const CONJ: &str = include_str!("../../../lean/examples/complex_conjugate_nonzero/statement.lit");
const ABS: &str = include_str!("../../../lean/examples/complex_modulus_nonzero/statement.lit");
const CONJ_REV: &str =
    include_str!("../../../lean/examples/complex_conjugate_nonzero_reversed/statement.lit");
const ABS_REV: &str =
    include_str!("../../../lean/examples/complex_modulus_nonzero_reversed/statement.lit");

fn selected_premise(run: &mut RunLitexCodeResult, conjugate: bool) -> &mut VerifyFactResult {
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
        NotEqualFactSearchProofByBuiltinRule::ConjugateNonzeroFromArgument(p) if conjugate => {
            &mut p.argument_nonzero
        }
        NotEqualFactSearchProofByBuiltinRule::ComplexModulusNonzero(p) if !conjugate => {
            &mut p.arg_nonzero_proof
        }
        _ => panic!("wrong selected complex rule"),
    }
}

#[test]
fn complex_nonzero_replays_selected_rule_and_original_premise() {
    for (source, conjugate, theorem) in [
        (CONJ, true, "Litex.conjugateNonzeroOfArg"),
        (ABS, false, "Litex.complexAbsNonzeroOfArg"),
    ] {
        let (mut run, compiler) = super::execute(source);
        selected_premise(&mut run, conjugate);
        let lean = compiler.compile_run(&run, "complex_nonzero").expect(source);
        assert!(lean.contains(theorem));
    }
    for source in [CONJ_REV, ABS_REV] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "complex_nonzero_reversed")
            .expect(source);
    }
}

#[test]
fn complex_nonzero_rejects_wrong_argument_evidence() {
    for (source, conjugate) in [(CONJ, true), (ABS, false)] {
        let (mut run, compiler) = super::execute(source);
        let VerifyFactResult::AtomicExceptEquality(result) = selected_premise(&mut run, conjugate)
        else {
            panic!("atomic premise")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
            panic!("verified premise")
        };
        let AtomicFact::NotEqualFact(fact) = &mut proof.fact else {
            panic!("nonzero fact")
        };
        fact.left = Obj::Literal(Literal::Number(Number::new("3".into())));
        compiler
            .compile_run(&run, "wrong_complex_argument")
            .expect_err("different argument");
    }
}

#[test]
fn complex_nonzero_rejects_missing_object_wd() {
    for source in [CONJ, ABS] {
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
            .compile_run(&run, "missing_complex_wd")
            .expect_err("missing object WD");
    }
}

#[test]
fn zero_complex_values_are_not_proved_nonzero() {
    for source in ["have z C = 0\nconj(z) != 0", "have z C = 0\nC_abs(z) != 0"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
