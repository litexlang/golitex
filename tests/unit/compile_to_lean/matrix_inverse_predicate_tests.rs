use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../lean/examples/native_matrix_inverse_predicates/statement.lit");

#[test]
fn native_matrix_inverse_predicate_compiler_replays_checked_source() {
    let (run, compiler) = super::execute(SOURCE);
    let output = super::compile_run(&run, &compiler, "native_matrix_inverse_predicates").unwrap();
    assert!(output.contains("Litex.IsMatrixInvValue"));
    assert!(output.contains("Litex.MatrixInversibleValue"));
    assert!(output.contains("Litex.matrixInversibleOfNonzero"));
    assert!(output.contains("Litex.matrixInversibleNonzero"));
    assert!(output.contains("Litex.isMatrixInvOfProducts"));
    assert!(output.contains("Litex.isMatrixInvProducts"));
    assert!(!output.contains("sorry"));
    assert!(!output.contains("axiom "));
}

#[test]
fn native_matrix_inverse_predicate_compiler_rejects_mismatched_determinant_subject() {
    let (mut run, compiler) = super::execute(
        "forall n N,A matrix(C,n,n):\n    det(A,n)!=0\n    =>:\n        $matrix_inversible(A,n)",
    );
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let VerifyFactResult::AtomicExceptEquality(result) =
        &mut forall.proved_then_facts[0].verify_result
    else {
        panic!("predicate result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = result.as_mut() else {
        panic!("predicate proof")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::MatrixInversibleFact(p),
    ) = &mut p.searched_proof
    else {
        panic!("determinant rule")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = p.determinant_nonzero.as_mut() else {
        panic!("nonzero result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(nonzero) = result.as_mut() else {
        panic!("nonzero premise")
    };
    let AtomicFact::NotEqualFact(f) = &mut nonzero.fact else {
        panic!("nonzero subject")
    };
    f.right = Obj::Literal(Literal::Number(Number {
        normalized_value: "1".into(),
    }));
    assert!(super::compile_run(&run, &compiler, "changed_matrix_determinant").is_err());
}

#[test]
fn native_matrix_inverse_predicate_compiler_rejects_missing_inference_conclusion() {
    let (mut run, compiler) = super::execute(
        "forall n N,A,B matrix(C,n,n):\n    $is_matrix_inv(A,B,n)\n    =>:\n        det(A,n)!=0",
    );
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::IsMatrixInvFact(rules),
    )) = &mut forall.assumed_dom_facts[0].store_and_infer.infer
    else {
        panic!("candidate inference")
    };
    let crate::store_fact_and_infer::InferIsMatrixInvFactResult::DefinitionAndDeterminant(p) =
        &mut rules[0];
    p.derived.pop();
    assert!(super::compile_run(&run, &compiler, "missing_matrix_inverse_conclusion").is_err());
}
