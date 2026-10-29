use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{greater::GreaterFactSearchProofByBuiltinRule, greater_equal::GreaterEqualFactSearchProofByBuiltinRule};
use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_real_sign_proof::{RealSign, StructuralRealSignProof, StructuralRealSignReason};
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;

const SUM: &str = "claim:\n    ? forall a R, b R:\n        a > 0\n        b > 0\n        =>:\n            a + b > 0\n    a + b > 0\n";
const QUOTIENT: &str = "claim:\n    ? forall a R, b R:\n        a > 0\n        b > 0\n        =>:\n            a / b > 0\n    a / b > 0\n";
const PRODUCT: &str = "claim:\n    ? forall a R, b R:\n        a > 0\n        b > 0\n        =>:\n            a * b > 0\n    a * b > 0\n";
const LESS_SUM: &str = "claim:\n    ? forall a R, b R:\n        0 < a\n        0 < b\n        =>:\n            0 < a + b\n    0 < a + b\n";

fn run(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("source run");
    (result, LitexToLeanCompiler::new(runtime))
}

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let (result, compiler) = run(source);
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, compiler)
}

fn selected_mut(result: &mut RunLitexCodeResult) -> &mut StructuralRealSignProof {
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
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
            GreaterFactSearchProofByBuiltinRule::StructuralRealSign(selected),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual structural sign route")
    };
    selected
}

#[test]
fn positive_sum_and_quotient_replay_selected_strategy_and_original_constructor_wd() {
    for (source, namespace, bridge) in [
        (SUM, "positive_sum_strategy", "Litex.addPositive"),
        (QUOTIENT, "positive_quotient_strategy", "Litex.divPositive"),
        (PRODUCT, "positive_product_strategy", "Litex.mulPositive"),
    ] {
        let (mut result, compiler) = checked(source);
        assert!(matches!(
            selected_mut(&mut result).reason,
            StructuralRealSignReason::Add { .. }
                | StructuralRealSignReason::Div { .. }
                | StructuralRealSignReason::Mul { .. }
        ));
        let lean = compiler
            .compile_run(&result, namespace)
            .expect("actual ordered positivity replay");
        assert!(lean.contains(bridge));
        assert!(lean.contains(".wd.1"));
        if source == QUOTIENT {
            assert!(lean.contains(".wd.2.2"));
        }
    }
}

#[test]
fn positive_sum_builtin_accepts_the_original_less_goal_orientation() {
    let (mut result, compiler) = checked(LESS_SUM);
    let children = selected_sum_builtin_mut(&mut result);
    assert_ne!(
        super::helper::source_subject(&children.left_positive_proof)
            .unwrap()
            .fact_id(),
        super::helper::source_subject(&children.right_positive_proof)
            .unwrap()
            .fact_id(),
    );
    compiler
        .compile_run(&result, "positive_sum_less_orientation")
        .expect("source strict-zero orientation");
}

fn selected_sum_builtin_mut(result: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::SumBothPositiveBuiltinRuleProof{
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
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule::SumBothPositive(proof))) = &mut proof.searched_proof else { panic!("actual SumBothPositive builtin") };
    proof
}

#[test]
fn positive_sum_builtin_rejects_wrong_child_order_and_deleted_child_citation() {
    let (mut result, compiler) = checked(LESS_SUM);
    let selected = selected_sum_builtin_mut(&mut result);
    std::mem::swap(
        &mut selected.left_positive_proof,
        &mut selected.right_positive_proof,
    );
    assert_eq!(
        compiler
            .compile_run(&result, "sum_wrong_child")
            .unwrap_err()
            .route,
        "PositiveSum/ChildSubject"
    );
    let (mut result, compiler) = checked(LESS_SUM);
    let selected = selected_sum_builtin_mut(&mut result);
    let VerifyFactResult::AtomicExceptEquality(child) = &mut selected.left_positive_proof else {
        panic!("actual atomic child")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(child) = child.as_mut() else {
        panic!("actual successful child")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
        &mut child.searched_proof
    else {
        panic!("actual original child citation")
    };
    citation
        .why_parameters_of_known_fact_are_equal_to_givens
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "sum_deleted_child_evidence")
            .unwrap_err()
            .route,
        "KnownAtomic"
    );
}

#[test]
fn positive_strategy_rejects_wrong_ordered_operand_capture() {
    for source in [SUM, QUOTIENT, PRODUCT] {
        let (mut result, compiler) = checked(source);
        match &mut selected_mut(&mut result).reason {
            StructuralRealSignReason::Add { left, right }
            | StructuralRealSignReason::Div { left, right }
            | StructuralRealSignReason::Mul { left, right } => std::mem::swap(left, right),
            _ => panic!("selected binary sign"),
        }
        let error = compiler
            .compile_run(&result, "positive_wrong_operand")
            .unwrap_err();
        assert!(matches!(
            error.route.as_str(),
            "StructuralPositive/BinaryOperands" | "StructuralPositive/DivisionOperands"
        ));
    }
}

#[test]
fn positive_strategy_rejects_missing_requirement_proof() {
    for source in [SUM, QUOTIENT, PRODUCT] {
        let (mut result, compiler) = checked(source);
        let left = match &mut selected_mut(&mut result).reason {
            StructuralRealSignReason::Add { left, .. }
            | StructuralRealSignReason::Div { left, .. }
            | StructuralRealSignReason::Mul { left, .. } => left,
            _ => panic!("selected binary sign"),
        };
        let StructuralRealSignReason::Known { source, .. } = &mut left.reason else {
            panic!("actual original sign citation");
        };
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            source.searched_proof.as_mut()
        else {
            panic!("known sign");
        };
        citation
            .why_parameters_of_known_fact_are_equal_to_givens
            .clear();
        assert_eq!(
            compiler
                .compile_run(&result, "positive_missing_proof")
                .unwrap_err()
                .route,
            "KnownAtomic"
        );
    }
}

#[test]
fn switching_selected_positive_sum_to_nonnegative_stays_rejected() {
    let (mut result, compiler) = checked(SUM);
    selected_mut(&mut result).sign = RealSign::Nonnegative;
    assert_eq!(
        compiler
            .compile_run(&result, "changed_positive_sign")
            .unwrap_err()
            .route,
        "StructuralPositive/Sign"
    );
}

#[test]
fn negative_factor_product_strategy_remains_a_nearest_unsupported_boundary() {
    let source = "claim:\n    ? forall a R, b R:\n        a < 0\n        b < 0\n        =>:\n            a * b > 0\n    a * b > 0\n";
    let (result, compiler) = checked(source);
    assert_eq!(
        compiler
            .compile_run(&result, "positive_product_boundary")
            .unwrap_err()
            .route,
        "StructuralPositive/BinarySigns"
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
