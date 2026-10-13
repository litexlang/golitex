use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty, InFactSearchProofByKnownSpecialProperty,
};
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

const POSITIVE_CLAIM: &str = "claim:\n    ? forall x R+:\n        x + 0 = x\n    x + 0 = x\n";
const REFINE_CLAIM: &str =
    "claim:\n    ? forall x R:\n        x > 0\n        =>:\n            x $in R+\n    x $in R+\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn body(
    statement: &ExecStmtResult,
) -> &crate::execute::execute_proof_block_stmt::ExecClaimForallProof {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        proof,
    ))) = statement
    else {
        panic!("actual claim")
    };
    let ExecClaimBodyProof::Forall(body) = &proof.body else {
        panic!("actual forall body")
    };
    body
}

fn body_mut(
    statement: &mut ExecStmtResult,
) -> &mut crate::execute::execute_proof_block_stmt::ExecClaimForallProof {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        proof,
    ))) = statement
    else {
        panic!("actual claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut proof.body else {
        panic!("actual forall body")
    };
    body
}

fn sign(
    store: &StoreFactAndInferResult,
) -> &crate::store_fact_and_infer::InferInFactSignedStandardSetSignResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &store.infer else {
        panic!("actual membership inference")
    };
    rules
        .iter()
        .find_map(|rule| match rule {
            InferInFactResult::SignedStandardSetSign(sign) => Some(sign),
            _ => None,
        })
        .expect("actual signed rule")
}

fn sign_mut(
    store: &mut StoreFactAndInferResult,
) -> &mut crate::store_fact_and_infer::InferInFactSignedStandardSetSignResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &mut store.infer
    else {
        panic!("actual membership inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferInFactResult::SignedStandardSetSign(sign) => Some(sign),
            _ => None,
        })
        .expect("actual signed rule")
}

#[test]
fn positive_generic_binder_preserves_carrier_and_actual_sign_stores() {
    let (result, compiler) = checked(POSITIVE_CLAIM);
    let captured = sign(
        &body(&result.statement_results[0])
            .introduced_params
            .defined_params
            .store_and_infer_results[0],
    );
    assert_eq!(captured.derived.len(), 3);
    let lean = compiler
        .compile_run(&result, "positive_generic_binder")
        .expect("actual refinement and numeric evidence");
    assert!(lean.contains("Litex.RPos"));
    assert!(lean.contains("Litex.inRPos_positive"));
    assert!(lean.contains("Litex.positiveRealToComplex"));
    assert!(lean.contains("_Host_i"));
    for store in &captured.derived {
        assert!(lean.contains(&format!("have h_{}", store.primary_fact_id().value())));
    }
}

#[test]
fn known_strict_order_refines_only_its_actual_positive_endpoint() {
    let (result, compiler) = checked(REFINE_CLAIM);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) =
        &body(&result.statement_results[0]).proof_steps[0]
    else {
        panic!("membership body step")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &step.verify_result else {
        panic!("atomic member")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful member")
    };
    assert!(matches!(
        &proof.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
            AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
                InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(_)
            )
        )
    ));
    let lean = compiler
        .compile_run(&result, "positive_known_order")
        .expect("selected strict premise replay");
    assert!(lean.contains("Litex.inRPos_intro"));
}

#[test]
fn positive_refinement_rejects_changed_selected_order_endpoint() {
    let (mut result, compiler) = checked(REFINE_CLAIM);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) =
        &mut body_mut(&mut result.statement_results[0]).proof_steps[0]
    else {
        panic!("membership body step")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut step.verify_result else {
        panic!("atomic member")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful member")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(selected),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected actual strict order")
    };
    match &mut selected.positive_order.fact {
        AtomicFact::LessFact(f) => f.left = f.right.clone(),
        AtomicFact::GreaterFact(f) => f.right = f.left.clone(),
        _ => panic!("original strict family"),
    }
    assert_eq!(
        compiler
            .compile_run(&result, "positive_other_endpoint")
            .unwrap_err()
            .route,
        "PositiveReal/OrderSubject"
    );
}

#[test]
fn positive_sign_consumer_rejects_missing_original_store_and_changed_subject() {
    let (mut result, compiler) = checked(POSITIVE_CLAIM);
    sign_mut(
        std::rc::Rc::get_mut(
            &mut body_mut(&mut result.statement_results[0])
                .introduced_params
                .defined_params
                .store_and_infer_results[0],
        )
        .expect("test-owned parameter store"),
    )
    .derived
    .pop();
    assert!(compiler
        .compile_run(&result, "missing_positive_store")
        .is_err());
    let (mut result, compiler) = checked(POSITIVE_CLAIM);
    let StoreFactResult::AtomicFact(store) = &mut sign_mut(
        std::rc::Rc::get_mut(
            &mut body_mut(&mut result.statement_results[0])
                .introduced_params
                .defined_params
                .store_and_infer_results[0],
        )
        .expect("test-owned parameter store"),
    )
    .derived[0]
        .store
    else {
        panic!("actual atomic projection")
    };
    let AtomicFact::LessFact(fact) = &mut store.fact else {
        panic!("actual strict projection")
    };
    fact.left = fact.right.clone();
    assert!(compiler
        .compile_run(&result, "changed_positive_store")
        .is_err());
}

#[test]
fn positive_literal_and_rational_memberships_replay_checked_closed_values() {
    let (result, compiler) = checked("1 $in R+\n(1 + 1) / 3 $in R+\n$is_nonempty_set(R+)\n");
    let lean = compiler
        .compile_run(&result, "positive_closed_values")
        .expect("closed certificates");
    assert!(lean.contains("Litex.numberInRPos"));
    assert!(lean.contains("Litex.rPosNonempty"));
}

#[test]
fn positive_function_return_observation_preserves_the_actual_call_object() {
    let source = "have fn positive_identity(x R+) R+ = x\nforall x R+:\n    positive_identity(x) + 0 = x\nfn(x R+) R+ {x}(1) + 0 = 1\n";
    let (result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "positive_function_observation")
        .expect("actual positive call construction and numeric return projection");
    assert!(lean.contains("Litex.call"));
    assert!(lean.contains("Litex.positiveRealToComplex"));
}

#[test]
fn positive_closed_membership_rejects_changed_certificate_value() {
    let (mut result, compiler) = checked("1 $in R+\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut result.statement_results[0]
    else {
        panic!("closed member")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut step.verify_result else {
        panic!("atomic member")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("successful member")
    };
    let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
        ClosedAtomicExceptEqualityCalculationProof::In(
            ClosedMembershipCalculationProof::StandardSet { value, .. },
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual closed certificate")
    };
    *value = ClosedScalarValue::Decimal("0".into());
    assert_eq!(
        compiler
            .compile_run(&result, "positive_zero_certificate")
            .unwrap_err()
            .route,
        "PositiveReal/ClosedValue"
    );
}

#[test]
fn other_signed_carriers_remain_rejected_boundaries() {
    let (result, compiler) = checked("forall x R-:\n    x = x\n");
    assert!(compiler
        .compile_run(&result, "negative_real_boundary")
        .is_err());
}
