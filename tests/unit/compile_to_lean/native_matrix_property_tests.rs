use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::search_native_matrix_property::{MatrixPropertyApplicationProof, MatrixPropertyRequirementProof, MatrixPropertySumForm, NativeMatrixPropertyProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;

#[test]
fn native_matrix_properties_compile_all_22_current_source_conclusions() {
    let source = include_str!("../../../examples/test_objs/native_matrix_properties.lit");
    let (run, compiler) = super::execute(source);
    let output = compiler
        .compile_run(&run, "native_matrix_properties")
        .unwrap();
    assert!(output.contains("euclideanNormTriangleNaturalFormula"));
    assert!(output.contains("matrixInverseOfCandidate"));
    assert!(output.contains("matrixRankLeRows"));
    println!("compiled_22_output_bytes={}", output.len());
    assert_eq!(
        output,
        compiler
            .compile_run(&run, "native_matrix_properties")
            .unwrap()
    );
}

#[test]
fn native_matrix_properties_compile_reverse_equalities() {
    let source =
        include_str!("../../../lean/examples/native_matrix_properties_reverse/statement.lit");
    let (run, compiler) = super::execute(source);
    let output = compiler
        .compile_run(&run, "native_matrix_properties_reverse")
        .unwrap();
    assert!(output.contains("_matrix_law.symm"));
}

fn order_application(statement: &mut ExecStmtResult) -> &mut MatrixPropertyApplicationProof {
    let all = super::forall_proof_mut(statement);
    let selected =
        &mut super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result).searched_proof;
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::NativeMatrixProperty(p),
        ),
    ) = selected
    else {
        panic!("native matrix order");
    };
    match p {
        NativeMatrixPropertyProof::RankRows(p) => &mut p.application,
        NativeMatrixPropertyProof::EuclideanTriangle(p) => &mut p.application,
        _ => panic!("selected test rule"),
    }
}

#[test]
fn native_matrix_properties_compiler_rejects_corrupt_selection_premises_and_matches() {
    let source = "forall m,n N,A matrix(C,m,n):\n    matrix_rank(A,m,n)<=m";
    for change in [
        "count",
        "order",
        "id",
        "args",
        "conclusion",
        "orientation",
        "match",
        "schema",
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = order_application(&mut run.statement_results[0]);
        match change {
            "count" => {
                p.requirement_proofs.pop();
            }
            "order" => p.requirement_proofs.swap(0, 1),
            "id" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[0] else {
                    panic!();
                };
                f.fact_id = FactId::new(u64::MAX);
            }
            "args" => p.arguments.swap(1, 2),
            "conclusion" => {
                let AtomicFact::LessEqualFact(f) = &mut p.conclusion else {
                    panic!();
                };
                f.right = Obj::Literal(Literal::Number(Number {
                    normalized_value: "0".into(),
                }));
            }
            "orientation" => p.matching.reversed = true,
            "match" => {
                p.matching.comparisons.pop();
            }
            "schema" => p.schema = p.requirements[0].clone(),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, change).is_err(),
            "accepted {change}"
        );
    }
}

#[test]
fn native_matrix_properties_compiler_rejects_corrupt_natural_sum_and_zero_alpha() {
    let triangle="forall n N,u,v cart_n(C,n):\n    euclidean_norm(fn(k closed_range(1,n)) C {u(k)+v(k)},n)<=euclidean_norm(u,n)+euclidean_norm(v,n)";
    let (mut run, compiler) = super::execute(triangle);
    let p = order_application(&mut run.statement_results[0]);
    let MatrixPropertySumForm::Natural { original, .. } = &mut p.sum_form else {
        panic!("natural sum");
    };
    *original = p.arguments[0].clone();
    assert!(compiler.compile_run(&run, "wrong_sum").is_err());

    let source="forall n N,v cart_n(C,n):\n    v=fn(k closed_range(1,n)) C {0}\n    =>:\n        euclidean_norm(v,n)=0";
    let (mut run, compiler) = super::execute(source);
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let selected =
        &mut super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result).searched_proof;
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::NativeMatrixProperty(
            NativeMatrixPropertyProof::EuclideanZeroIntro(p),
        ),
    ) = selected
    else {
        panic!("native zero introduction");
    };
    let MatrixPropertyRequirementProof::ZeroVectorAlpha { comparison, .. } =
        p.application.requirement_proofs.last_mut().unwrap()
    else {
        panic!("alpha bridge");
    };
    comparison.right = p.application.arguments[0].clone();
    assert!(compiler.compile_run(&run, "wrong_alpha").is_err());
}
