use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{
        NotEqualFactSearchProofByBuiltinRule, SqrtNonzeroFromPositiveArgBuiltinRuleProof,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::prelude::*;

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut SqrtNonzeroFromPositiveArgBuiltinRuleProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[1]
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
            NotEqualFactSearchProofByBuiltinRule::SqrtNonzeroFromPositiveArg(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected sqrt nonzero rule")
    };
    rule
}

#[test]
fn sqrt_nonzero_replays_selected_rule_in_both_orientations() {
    for source in ["have x R+\nsqrt(x) != 0", "have x R+\n0 != sqrt(x)"] {
        let (mut run, compiler) = super::execute(source);
        selected_rule(&mut run);
        let lean = compiler.compile_run(&run, "sqrt_nonzero").expect(source);
        assert!(lean.contains("Litex.sqrtNonzeroOfPositive"));
    }
}

#[test]
fn sqrt_nonzero_rejects_a_positive_proof_about_another_object() {
    let (mut run, compiler) = super::execute("have x R+\nsqrt(x) != 0");
    let positive = &mut selected_rule(&mut run).arg_positive_proof;
    let VerifyFactResult::AtomicExceptEquality(result) = positive else {
        panic!("atomic positive premise")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified positive premise")
    };
    let AtomicFact::LessFact(fact) = &mut proof.fact else {
        panic!("positive order")
    };
    fact.right = Obj::Literal(Literal::Number(Number::new("3".into())));
    compiler
        .compile_run(&run, "wrong_sqrt_positive")
        .expect_err("different argument");
}

#[test]
fn zero_sqrt_is_not_proved_nonzero() {
    let source = "have x R = 0\nsqrt(x) != 0";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
