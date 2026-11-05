use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{
        AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
        VerifyAtomicExceptEqualityFactSuccess,
    },
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule,
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::prelude::*;

const SOURCE: &str = r#"# Euler's number is different from one.
e != 1
"#;
const REVERSED: &str = r#"# One is different from Euler's number.
1 != e
"#;
const COMPUTED: &str = r#"# Euler's number differs from a computed representation of one.
1+0 != e
"#;

fn selected(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[0]
    else {
        panic!("successful fact")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &mut statement.verify_result else {
        panic!("atomic fact")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified fact")
    };
    assert!(matches!(
        &proof.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                NotEqualFactSearchProofByBuiltinRule::EulerNonunit(_)
            )
        )
    ));
    proof
}

#[test]
fn euler_nonunit_replays_selected_rule_and_exact_one() {
    for source in [SOURCE, REVERSED, COMPUTED] {
        let (mut run, compiler) = super::execute(source);
        selected(&mut run);
        let lean = compiler.compile_run(&run, "euler_nonunit").expect(source);
        assert!(lean.contains("Litex.eulerNonunit"));
    }
}

#[test]
fn euler_nonunit_rejects_changed_subject_one_and_missing_wd() {
    for change in ["subject", "one", "wd"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let proof = selected(&mut run);
        let wrong = Obj::Literal(Literal::Number(Number::new("2".into())));
        if change == "wd" {
            proof
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .clear();
        } else {
            let AtomicFact::NotEqualFact(fact) = &mut proof.fact else {
                panic!("inequality")
            };
            if change == "subject" {
                fact.left = wrong
            } else {
                fact.right = wrong
            }
        }
        compiler
            .compile_run(&run, "wrong_euler_nonunit")
            .expect_err(change);
    }
}

#[test]
fn one_is_not_proved_distinct_from_itself() {
    let source = "1 != 1";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
