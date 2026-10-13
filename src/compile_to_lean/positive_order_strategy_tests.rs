use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::NonnegativeSumIsNonnegativeStrategySingleStep;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;

const SUM: &str = "claim:\n    ? forall a R, b R:\n        a > 0\n        b > 0\n        =>:\n            a + b > 0\n    a + b > 0\n";
const QUOTIENT: &str = "claim:\n    ? forall a R, b R:\n        a > 0\n        b > 0\n        =>:\n            a / b > 0\n    a / b > 0\n";

fn run(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    (result, LitexToLeanCompiler::new(runtime))
}

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let (result, compiler) = run(source);
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, compiler)
}

fn selected_mut(
    result: &mut RunLitexCodeResult,
) -> &mut AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        proof,
    ))) = &mut result.statement_results[0]
    else {
        panic!("actual claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut proof.body else {
        panic!("actual forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut body.proof_steps[0] else {
        panic!("actual body step")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut step.verify_result else {
        panic!("actual atomic result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(selected) =
        &mut proof.searched_proof
    else {
        panic!("actual strategy route")
    };
    selected
}

#[test]
fn positive_sum_and_quotient_replay_selected_strategy_and_original_constructor_wd() {
    for (source, namespace, bridge) in [
        (SUM, "positive_sum_strategy", "Litex.addPositive"),
        (QUOTIENT, "positive_quotient_strategy", "Litex.divPositive"),
    ] {
        let (mut result, compiler) = checked(source);
        assert!(matches!(
            selected_mut(&mut result),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(_)
                | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(
                    _
                )
        ));
        let lean = compiler
            .compile_run(&result, namespace)
            .expect("actual ordered positivity replay");
        assert!(lean.contains(bridge));
        assert!(lean.contains("_litex_positive_result.wd.1"));
        if source == QUOTIENT {
            assert!(lean.contains("_litex_positive_result.wd.2.2"));
        }
    }
}

#[test]
fn positive_sum_strategy_accepts_the_original_less_goal_orientation() {
    let (result, compiler) = checked("claim:\n    ? forall a R, b R:\n        0 < a\n        0 < b\n        =>:\n            0 < a + b\n    0 < a + b\n");
    compiler
        .compile_run(&result, "positive_sum_less_orientation")
        .expect("source strict-zero orientation");
}

#[test]
fn positive_strategy_rejects_wrong_ordered_operand_capture() {
    for source in [SUM, QUOTIENT] {
        let (mut result, compiler) = checked(source);
        match selected_mut(&mut result) {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(proof) => {
                proof.requirement_facts.swap(0, 1)
            }
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(
                proof,
            ) => proof.requirement_facts.swap(0, 1),
            _ => panic!("selected supported source strategy"),
        }
        assert_eq!(
            compiler
                .compile_run(&result, "positive_wrong_operand")
                .unwrap_err()
                .route,
            "PositiveOrder/RequirementSubject"
        );
    }
}

#[test]
fn positive_strategy_rejects_missing_requirement_proof() {
    for source in [SUM, QUOTIENT] {
        let (mut result, compiler) = checked(source);
        match selected_mut(&mut result) {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(proof) => {
                proof.proof_of_requirement_facts.pop();
            }
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(
                proof,
            ) => {
                proof.proof_of_requirement_facts.pop();
            }
            _ => panic!("selected supported source strategy"),
        }
        assert_eq!(
            compiler
                .compile_run(&result, "positive_missing_proof")
                .unwrap_err()
                .route,
            "PositiveOrder/Requirements"
        );
    }
}

#[test]
fn switching_selected_positive_sum_to_nonnegative_strategy_stays_rejected() {
    let (mut result, compiler) = checked(SUM);
    let selected = selected_mut(&mut result);
    let AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(proof) = selected
    else {
        panic!("actual positive sum")
    };
    let replacement = NonnegativeSumIsNonnegativeStrategySingleStep {
        requirement_facts: std::mem::take(&mut proof.requirement_facts),
        proof_of_requirement_facts: std::mem::take(&mut proof.proof_of_requirement_facts),
    };
    *selected = AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(
        replacement,
    );
    assert_eq!(
        compiler
            .compile_run(&result, "changed_positive_strategy")
            .unwrap_err()
            .route,
        "Atomic/BuiltinStrategy"
    );
}

#[test]
fn product_strategy_remains_a_nearest_unsupported_boundary() {
    let source = SUM.replace("a + b", "a * b");
    let (result, compiler) = checked(&source);
    assert_eq!(
        compiler
            .compile_run(&result, "positive_product_boundary")
            .unwrap_err()
            .route,
        "Atomic/BuiltinStrategy"
    );
}

#[test]
fn negative_numerator_cannot_become_a_positive_quotient_source_proof() {
    let (result, compiler) =
        run("claim:\n    ? forall x R+:\n        -1 / x > 0\n    -1 / x > 0\n");
    assert!(!result.success && result.session_error.is_none());
    assert_eq!(
        compiler
            .compile_run(&result, "negative_numerator_boundary")
            .unwrap_err()
            .route,
        "source_failed"
    );
}
