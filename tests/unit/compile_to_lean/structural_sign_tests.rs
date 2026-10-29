use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_real_sign_proof::{RealSign, StructuralRealSignProof, StructuralRealSignReason};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;

const DIVISION: &str = "have r R+\n0 < r/2\n";

fn quotient(run: &mut RunLitexCodeResult) -> &mut StructuralRealSignProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[1] else {
        panic!("division fact")
    };
    let proof = super::atomic_proof_mut(&mut p.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof
    else {
        panic!("builtin")
    };
    let AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
        LessFactSearchProofByBuiltinRule::StructuralRealSign(p),
    ) = rule
    else {
        panic!("selected structural sign")
    };
    p
}

#[test]
fn selected_positive_division_replays_its_original_sign_tree() {
    let (run, compiler) = super::execute(DIVISION);
    let lean = compiler.compile_run(&run, "positive_quotient").unwrap();
    assert!(lean.contains("Litex.divPositive"));
}

#[test]
fn selected_positive_division_rejects_a_changed_sign_or_operand() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(DIVISION);
        let root = quotient(&mut run);
        if mutation == 0 {
            root.sign = RealSign::Nonnegative;
        } else {
            let StructuralRealSignReason::Div { left, right } = &mut root.reason else {
                panic!("quotient tree")
            };
            if mutation == 1 {
                left.element = Obj::StandardSet(StandardSet::R);
            } else {
                right.sign = RealSign::Negative;
            }
        }
        compiler
            .compile_run(&run, "invalid_positive_quotient")
            .expect_err("exact positive source operands");
    }
}

#[test]
fn selected_even_power_nonnegativity_replays_the_recorded_base_and_exponent() {
    let (run, compiler) = super::execute("forall x R:\n    x^2>=0\n");
    assert!(compiler
        .compile_run(&run, "even_power")
        .unwrap()
        .contains("Litex.powStructuralNonnegativeOfEven"));
}
