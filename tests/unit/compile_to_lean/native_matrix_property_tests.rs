use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::search_native_matrix_property::{MatrixPropertyApplicationProof, MatrixPropertyRequirementProof, MatrixPropertySumForm, NativeMatrixPropertyProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;

#[test]
fn native_matrix_properties_compile_all_22_current_source_conclusions() {
    let source = r#"# Native finite matrix properties: direct checks of existing BT contracts.
# Run: target/release/litex -strict -lang en -f examples/test_objs/native_matrix_properties.lit
# Formerly rejected tracer, preserved exactly:
# thm audit_rank_rows_direct:
#     ? forall m,n N,A matrix(C,m,n):
#         matrix_rank(A,m,n)<=m
# The direct statement now checks the same rank-bounds contract without release.
# Wrong rank bounds, missing zero/inverse premises and mismatched dimensions are
# executable negative tests in tests/unit/execute/native_matrix/properties.rs.

thm native_rank_rows_direct:
    ? forall m,n N,A matrix(C,m,n):
        matrix_rank(A,m,n)<=m

thm native_rank_cols_direct:
    ? forall m,n N,A matrix(C,m,n):
        matrix_rank(A,m,n)<=n

thm native_rank_product_left_direct:
    ? forall m,k,n N,A matrix(C,m,k),B matrix(C,k,n):
        matrix_rank(matrix_mul(A,B,m,k,n),m,n)<=matrix_rank(A,m,k)

thm native_rank_product_right_direct:
    ? forall m,k,n N,A matrix(C,m,k),B matrix(C,k,n):
        matrix_rank(matrix_mul(A,B,m,k,n),m,n)<=matrix_rank(B,k,n)

thm native_inner_self_real_direct:
    ? forall n N,v cart_n(C,n):
        inner_product(v,v,n) $in R

thm native_inner_self_nonnegative_direct:
    ? forall n N,v cart_n(C,n):
        0<=re(inner_product(v,v,n))

thm native_inner_self_imaginary_direct:
    ? forall n N,v cart_n(C,n):
        img(inner_product(v,v,n))=0

thm native_euclidean_nonnegative_direct:
    ? forall n N,v cart_n(C,n):
        0<=euclidean_norm(v,n)

thm native_frobenius_nonnegative_direct:
    ? forall m,n N,A matrix(C,m,n):
        0<=frobenius_norm(A,m,n)

thm native_cauchy_schwarz_direct:
    ? forall n N,u,v cart_n(C,n):
        C_abs(inner_product(u,v,n))<=euclidean_norm(u,n)*euclidean_norm(v,n)

thm native_euclidean_scale_direct:
    ? forall n N,z C,v cart_n(C,n):
        euclidean_norm(fn(k closed_range(1,n)) C {z*v(k)},n)=C_abs(z)*euclidean_norm(v,n)

thm native_euclidean_triangle_direct:
    ? forall n N,u,v cart_n(C,n):
        euclidean_norm(fn(k closed_range(1,n)) C {u(k)+v(k)},n)<=euclidean_norm(u,n)+euclidean_norm(v,n)

thm native_inner_linear_right_direct:
    ? forall n N,u,v,w cart_n(C,n),a,b C:
        inner_product(u,fn(k closed_range(1,n)) C {a*v(k)+b*w(k)},n)=a*inner_product(u,v,n)+b*inner_product(u,w,n)

thm native_frobenius_triangle_direct:
    ? forall m,n N,A,B matrix(C,m,n):
        frobenius_norm(matrix_add(A,B,m,n),m,n)<=frobenius_norm(A,m,n)+frobenius_norm(B,m,n)

thm native_euclidean_zero_elim_direct:
    ? forall n N,v cart_n(C,n):
        euclidean_norm(v,n)=0
        =>:
            v=fn(k closed_range(1,n)) C {0}

thm native_euclidean_zero_intro_direct:
    ? forall n N,v cart_n(C,n):
        v=fn(k closed_range(1,n)) C {0}
        =>:
            euclidean_norm(v,n)=0

thm native_frobenius_zero_elim_direct:
    ? forall m,n N,A matrix(C,m,n):
        frobenius_norm(A,m,n)=0
        =>:
            A=zero_matrix(m,n)

thm native_frobenius_zero_intro_direct:
    ? forall m,n N,A matrix(C,m,n):
        A=zero_matrix(m,n)
        =>:
            frobenius_norm(A,m,n)=0

thm native_euclidean_square_sum_direct:
    ? forall n N,v cart_n(C,n):
        euclidean_norm(v,n)^2=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) R {C_abs(v(k))^2})

thm native_frobenius_square_sum_direct:
    ? forall m,n N,A matrix(C,m,n):
        frobenius_norm(A,m,n)^2=finite_set_sum(closed_range(1,m),fn(r closed_range(1,m)) R {finite_set_sum(closed_range(1,n),fn(c closed_range(1,n)) R {C_abs(A(r,c))^2})})

thm native_apply_adjoint_direct:
    ? forall m,n N,A matrix(C,m,n),u cart_n(C,n),v cart_n(C,m):
        inner_product(matrix_apply(A,u,m,n),v,m)=inner_product(u,matrix_apply(conjugate_transpose(A,m,n),v,n,m),n)

thm native_inverse_from_predicate_direct:
    ? forall n N,A,B matrix(C,n,n):
        $is_matrix_inv(A,B,n)
        =>:
            matrix_inv(A,n)=B
"#;
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
