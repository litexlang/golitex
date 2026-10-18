use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::execute_fact_stmt::known_tuple::KnownFunctionTupleApplicability;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_known_special_property::{
    EqualFactSearchProofByKnownSpecialProperty, FnTupleProjectionKnownProof, FnTupleValueKnownProof,
};
use crate::prelude::*;

// The original geo declaration and theorem, without a replacement proof.
const VEC: &str = "have fn vec(A, B cart(R, R)) cart(R, R) = (B(1) - A(1), B(2) - A(2))\n\nthm vec_coordinate_formula:\n    ? forall a, b cart(R, R):\n        vec(a, b) = (b(1) - a(1), b(2) - a(2))\n";
const PROJECTION: &str = "have fn vec(A, B cart(R, R)) cart(R, R) = (B(1) - A(1), B(2) - A(2))\n\nthm first_coordinate:\n    ? forall a, b cart(R, R):\n        vec(a, b)(1) = b(1) - a(1)\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source executes");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn conclusion(result: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &mut result.statement_results[1]
    else {
        panic!("original successful theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
        panic!("original forall proof");
    };
    assert!(body.proof_steps.is_empty());
    let VerifyFactResult::Equality(result) = &mut body.conclusion_proofs[0] else {
        panic!("original equality result");
    };
    let VerifyEqualityResult::Success(result) = result.as_mut() else {
        panic!("successful original equality");
    };
    result
}

fn tuple_value(result: &mut RunLitexCodeResult) -> &mut FnTupleValueKnownProof {
    let EqualFactSearchedProof::ByKnownSpecialProperty(
        EqualFactSearchProofByKnownSpecialProperty::FnTupleValue(proof),
    ) = &mut conclusion(result).searched_proof
    else {
        panic!("the source really selected FnTupleValue");
    };
    proof
}

fn projection(result: &mut RunLitexCodeResult) -> &mut FnTupleProjectionKnownProof {
    let EqualFactSearchedProof::ByKnownSpecialProperty(
        EqualFactSearchProofByKnownSpecialProperty::FnTupleProjection(proof),
    ) = &mut conclusion(result).searched_proof
    else {
        panic!("the source really selected FnTupleProjection");
    };
    proof
}

#[test]
fn known_tuple_value_replays_original_vec_source_route() {
    let (mut result, compiler) = checked(VEC);
    let payload = tuple_value(&mut result);
    assert!(!payload.reversed);
    assert!(payload.subject_equal.path.is_empty());
    assert!(!payload.function.function_equal.path.is_empty());
    assert!(matches!(
        payload.function.applicability,
        KnownFunctionTupleApplicability::AllSignaturesMatch { .. }
    ));
    let lean = compiler
        .compile_run(&result, "vec_coordinate_formula")
        .expect("original tuple-value result compiles");
    assert!(lean.contains("have _litex_signature_"));
    assert!(lean.contains("Litex.FunctionSemantics.call_graphValue"));
    assert!(lean.contains("have _litex_body_eq"));
}

#[test]
fn known_tuple_value_replays_original_reversed_route() {
    let reversed = VEC.replace(
        "vec(a, b) = (b(1) - a(1), b(2) - a(2))",
        "(b(1) - a(1), b(2) - a(2)) = vec(a, b)",
    );
    let (mut result, compiler) = checked(&reversed);
    assert!(tuple_value(&mut result).reversed);
    compiler
        .compile_run(&result, "vec_coordinate_formula_reversed")
        .expect("the original reversed route compiles");
}

#[test]
fn known_tuple_value_rejects_changed_substitution() {
    let (mut result, compiler) = checked(VEC);
    tuple_value(&mut result).function.value.args.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&result, "changed_tuple")
            .unwrap_err()
            .route,
        "Equality/FnTupleSubstitution"
    );
}

#[test]
fn known_tuple_value_rejects_missing_tuple_component() {
    let (mut result, compiler) = checked(VEC);
    tuple_value(&mut result).function.value.args.pop();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_tuple_component")
            .unwrap_err()
            .route,
        "Equality/FnTupleSubstitution"
    );
}

#[test]
fn known_tuple_value_rejects_changed_coordinate_receiver() {
    let (mut result, compiler) = checked(VEC);
    let payload = tuple_value(&mut result);
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(coordinate)) =
        payload.function.value.args[0].as_mut()
    else {
        panic!("original coordinate subtraction");
    };
    let (Obj::FnObj(left), Obj::FnObj(right)) =
        (coordinate.left.as_mut(), coordinate.right.as_ref())
    else {
        panic!("original coordinate applications");
    };
    left.head = right.head.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "changed_coordinate_receiver")
            .unwrap_err()
            .route,
        "Equality/FnTupleSubstitution"
    );
}

#[test]
fn known_tuple_value_rejects_missing_function_path() {
    let (mut result, compiler) = checked(VEC);
    tuple_value(&mut result)
        .function
        .function_equal
        .path
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_function_path")
            .unwrap_err()
            .route,
        "Equality/FnTupleBody"
    );
}

#[test]
fn known_tuple_value_rejects_missing_selected_signature() {
    let (mut result, compiler) = checked(VEC);
    let KnownFunctionTupleApplicability::AllSignaturesMatch { signatures, .. } =
        &mut tuple_value(&mut result).function.applicability
    else {
        panic!("original named-function applicability");
    };
    signatures.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_signature")
            .unwrap_err()
            .route,
        "Equality/FnTupleSelectedSignature"
    );
}

#[test]
fn known_tuple_value_rejects_relabelled_literal_applicability() {
    let (mut result, compiler) = checked(VEC);
    tuple_value(&mut result).function.applicability =
        KnownFunctionTupleApplicability::AnonymousLiteral;
    assert_eq!(
        compiler
            .compile_run(&result, "changed_applicability")
            .unwrap_err()
            .route,
        "Equality/FnTupleApplicability"
    );
}

#[test]
fn known_tuple_value_rejects_changed_subject_path() {
    let (mut result, compiler) = checked(VEC);
    let payload = tuple_value(&mut result);
    payload.subject_equal.path = payload.function.function_equal.path.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "changed_subject_path")
            .unwrap_err()
            .route,
        "Equality/PathOrder"
    );
}

#[test]
fn known_tuple_value_rejects_changed_value_path() {
    let (mut result, compiler) = checked(VEC);
    let payload = tuple_value(&mut result);
    payload.value_equal = Box::new(EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(KnownEqualityPathProof::new(
            payload.function.function_equal.path.clone(),
        )),
    ));
    assert_eq!(
        compiler
            .compile_run(&result, "changed_value_path")
            .unwrap_err()
            .route,
        "Equality/PathOrder"
    );
}

#[test]
fn known_tuple_projection_replays_original_two_layer_call() {
    let (mut result, compiler) = checked(PROJECTION);
    let Obj::FnObj(call) = &conclusion(&mut result).fact.left else {
        panic!("original projected call");
    };
    assert_eq!(call.body.len(), 2);
    let payload = projection(&mut result);
    assert_eq!(payload.index, 1);
    assert!(!payload.reversed);
    assert!(payload.subject_equal.path.is_empty());
    let lean = compiler
        .compile_run(&result, "original_first_coordinate")
        .expect("original projection result compiles");
    assert!(lean.contains("have _litex_coordinate_eq"));
    assert!(lean.contains("have _litex_component_eq"));
}

#[test]
fn known_tuple_projection_replays_reversed_second_coordinate() {
    let source = PROJECTION.replace("vec(a, b)(1) = b(1) - a(1)", "b(2) - a(2) = vec(a, b)(2)");
    let (mut result, compiler) = checked(&source);
    let payload = projection(&mut result);
    assert_eq!(payload.index, 2);
    assert!(payload.reversed);
    compiler
        .compile_run(&result, "original_reversed_second_coordinate")
        .expect("original reversed projection result compiles");
}

#[test]
fn known_tuple_projection_rejects_zero_index() {
    let (mut result, compiler) = checked(PROJECTION);
    projection(&mut result).index = 0;
    assert_eq!(
        compiler
            .compile_run(&result, "zero_coordinate")
            .unwrap_err()
            .route,
        "Equality/FnTupleProjectionIndex"
    );
}

#[test]
fn known_tuple_projection_rejects_changed_in_range_index() {
    let (mut result, compiler) = checked(PROJECTION);
    projection(&mut result).index = 2;
    assert_eq!(
        compiler
            .compile_run(&result, "changed_coordinate")
            .unwrap_err()
            .route,
        "Equality/FnTupleProjectionIndex"
    );
}

#[test]
fn known_tuple_projection_rejects_changed_tuple_substitution() {
    let (mut result, compiler) = checked(PROJECTION);
    projection(&mut result).function.value.args.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&result, "changed_projected_tuple")
            .unwrap_err()
            .route,
        "Equality/FnTupleSubstitution"
    );
}

#[test]
fn known_tuple_projection_rejects_missing_selected_signature() {
    let (mut result, compiler) = checked(PROJECTION);
    let KnownFunctionTupleApplicability::AllSignaturesMatch { signatures, .. } =
        &mut projection(&mut result).function.applicability
    else {
        panic!("original named-function applicability");
    };
    signatures.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_projection_signature")
            .unwrap_err()
            .route,
        "Equality/FnTupleSelectedSignature"
    );
}

#[test]
fn known_tuple_projection_rejects_changed_component_path() {
    let (mut result, compiler) = checked(PROJECTION);
    let payload = projection(&mut result);
    payload.component_equal = Box::new(EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(KnownEqualityPathProof::new(
            payload.function.function_equal.path.clone(),
        )),
    ));
    assert_eq!(
        compiler
            .compile_run(&result, "changed_component_path")
            .unwrap_err()
            .route,
        "Equality/PathOrder"
    );
}
