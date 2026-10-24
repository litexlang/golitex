use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn accepted(rt: &mut Runtime, source: &str) {
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{source}\n{}",
        crate::json_output::emit_run_detailed(&run, rt, "matrix_completion", None)
    );
}
const MATRIX: &str = "have fn A(r closed_range(1,2),c closed_range(1,2)) R=r+c";

#[test]
fn native_matrix_exact_evaluation_keeps_the_inherited_permission_ceiling() {
    use crate::execute::execute_eval_stmt::{evaluate_obj::evaluate_obj, helper::ActiveAlgoCalls};
    use crate::prelude::*;
    let mut rt = runtime();
    let v = Obj::ProductShape(ProductShape::Tuple(Tuple {
        args: vec![2, 3, 5]
            .into_iter()
            .map(|n| Box::new(super::matrix_number(n)))
            .collect(),
    }));
    let diag = Obj::MatrixOperator(MatrixOperator::Diagonal(MatrixDiagonal {
        vector: Box::new(v),
        order: Box::new(super::matrix_number(3)),
    }));
    let source = crate::execute::execute_fact_stmt::matrix_operations::determinant(
        diag,
        super::matrix_number(3),
    );
    rt.verify_obj_well_definedness(&source, VerifyState::top_level())
        .unwrap();
    let Obj::MatrixOperator(op) = &source else {
        unreachable!()
    };
    let body = rt.matrix_scalar_definition(op).unwrap();
    for level in [
        VerifyStateLevel::DefinitionAndForall,
        VerifyStateLevel::BuiltinRule,
        VerifyStateLevel::KnownSpecialProperty,
        VerifyStateLevel::Direct,
    ] {
        let mut context = ActiveAlgoCalls::new();
        context.proof_mode = true;
        context.function_proof_state = VerifyState::new(level);
        let result = evaluate_obj(&mut rt, &body, 0, &mut context).unwrap();
        match level {
            VerifyStateLevel::DefinitionAndForall | VerifyStateLevel::BuiltinRule => {
                assert_eq!(result.ok().unwrap().readable_string(), "30")
            }
            VerifyStateLevel::KnownSpecialProperty | VerifyStateLevel::Direct => {
                assert!(result.is_err(), "native evaluation reopened truth search")
            }
            VerifyStateLevel::Strategy => unreachable!(),
        }
        for proof in context.function_evaluations {
            let body = proof.expansion.expanded_body();
            assert!(super::exact_matrix_evaluation_source(body));
        }
    }
}

#[test]
fn native_matrix_arithmetic_preserves_order_shapes_and_real_codomain() {
    let mut rt = runtime();
    for source in [MATRIX,
        "have fn B(r closed_range(1,2),c closed_range(1,2)) R=r-c",
        "matrix_add(A,B,2,2)(1,2)=2",
        "matrix_sub(A,B,2,2)(1,2)=4",
        "matrix_scale(i,A,2,2)(1,2)=3*i",
        "matrix_mul(A,B,2,2,2)(1,1)=3",
        "matrix_mul(B,A,2,2,2)(1,1)=-3",
        "matrix_mul(A,B,2,2,2) $in matrix(R,2,2)",
        "matrix_apply(A,(1,2),2,2)(1)=8",
        "matrix_apply(A,(1,2),2,2) $in cart_n(R,2)",
        "matrix_power(A,2,2)(1,1)=13",
        "diagonal_matrix((2,3),2)(1,2)=0",
        "outer_product((2,3),(4,5),2,2)(2,1)=12",
        "forall m,n N,first,second matrix(R,m,n):\n    matrix_add(first,second,m,n) $in matrix(R,m,n)",
        "forall n,p N,mat matrix(C,n,n):\n    matrix_power(mat,n,p) $in matrix(C,n,n)",
    ] {accepted(&mut rt,source)}
}

#[test]
fn native_matrix_minors_arbitrary_small_orders_and_inverse_use_exact_values() {
    let mut rt = runtime();
    for source in [
        MATRIX,
        "matrix_minor(A,2,1,1)(1,1)=4",
        "matrix_minor(A,2,2,2)(1,1)=2",
        "matrix_cofactor(A,2,1,2)=-3",
        "matrix_adjugate(A,2)(1,1)=4",
        "det(diagonal_matrix((2,3,5),3),3)=30",
        "release thm matrix_det_identity(4)",
        "det(identity_matrix(4),4)=1",
        "det(A,2)=-1",
        "det(A,2)!=0",
        "matrix_inverse(A,2)(1,1)=-4",
        "matrix_inverse(A,2)(1,2)=3",
        "release thm matrix_rank_invertible(A,2)",
        "matrix_rank(A,2,2)=2",
    ] {
        accepted(&mut rt, source)
    }
}

#[test]
fn native_matrix_standard_complex_geometry_and_norm_closure() {
    let mut rt = runtime();
    for source in [
        MATRIX,
        "have fn imaginary_vector(k closed_range(1,1)) C=i",
        "have fn one_vector(k closed_range(1,1)) R=1",
        "inner_product(imaginary_vector,imaginary_vector,1)=1",
        "inner_product(imaginary_vector,one_vector,1)=-i",
        "inner_product(one_vector,imaginary_vector,1)=i",
        "outer_product(imaginary_vector,imaginary_vector,1,1)(1,1)=-1",
        "euclidean_norm((3,4),2)=5",
        "release thm frobenius_norm_square(A,2,2)",
        "frobenius_norm(A,2,2)^2=38",
        "release thm inner_product_cauchy_schwarz((1,i),(i,2),2)",
        "release thm euclidean_norm_triangle((1,i),(i,2),2)",
        "forall n N,u,v cart_n(C,n):\n    euclidean_norm(u,n)*euclidean_norm(v,n) $in R",
        "forall m,n N,mat matrix(C,m,n):\n    matrix_rank(mat,m,n)+1 $in N",
    ] {
        accepted(&mut rt, source)
    }
}

#[test]
fn native_matrix_candidates_and_zero_dimensions_keep_proof_obligations() {
    let mut rt = runtime();
    for source in [
        "release thm matrix_mul_identity(identity_matrix(2),2,2)",
        "release thm matrix_invertible_from_candidate(identity_matrix(2),identity_matrix(2),2)",
        "release thm matrix_inverse_from_candidate(identity_matrix(2),identity_matrix(2),2)",
        "matrix_inverse(identity_matrix(2),2)=identity_matrix(2)",
        "release thm matrix_rank_from_factorization(identity_matrix(2),identity_matrix(2),identity_matrix(2),identity_matrix(2),identity_matrix(2),2,2,2)",
        "matrix_rank(identity_matrix(2),2,2)=2",
        "release thm matrix_mul_zero(zero_matrix(2,0),2,0,3)",
        "matrix_mul(zero_matrix(2,0),zero_matrix(0,3),2,0,3)=zero_matrix(2,3)",
        "det(zero_matrix(0,0),0)=1",
        "det(zero_matrix(0,0),0)!=0",
        "matrix_inverse(zero_matrix(0,0),0) $in matrix(R,0,0)",
        "release thm matrix_rank_zero(0,3)",
        "matrix_rank(zero_matrix(0,3),0,3)=0",
        "inner_product(tuple(),tuple(),0)=0",
        "euclidean_norm(tuple(),0)=0",
        "frobenius_norm(zero_matrix(0,3),0,3)=0",
    ] {accepted(&mut rt,source)}
}

#[test]
fn native_matrix_missing_premises_wrong_values_and_domains_reject_transactionally() {
    for bad in [
        "let bad=matrix_mul(A,A,2,3,2)",
        "let bad=matrix_add(A,A,2,3)",
        "let bad=matrix_apply(A,(1,2,3),2,2)",
        "let bad=matrix_power(A,2,-1)",
        "let bad=matrix_minor(A,2,0,1)",
        "let bad=matrix_minor(zero_matrix(0,0),0,1,1)",
        "let bad=matrix_inverse(zero_matrix(2,2),2)",
        "let bad=matrix_scale(0,matrix_inverse(zero_matrix(2,2),2),2,2)",
        "matrix_scale(i,A,2,2) $in matrix(R,2,2)",
        "inner_product((i,1),(1,0),2)=i",
        "frobenius_norm(identity_matrix(2),2,2)=1",
        "matrix_rank(A,2,2)=1",
        "release thm matrix_inverse_from_candidate(A,A,2)",
        "release thm matrix_rank_from_factorization(A,A,A,A,A,2,1,2)",
        "release thm matrix_rank_bounds(A,2)",
        "let bad=matrix_rank(A,-1,2)",
    ] {
        let mut rt = runtime();
        accepted(&mut rt, MATRIX);
        let before: usize = rt
            .execution_environments_stack
            .iter()
            .map(|env| env.facts.facts_by_id.len())
            .sum();
        let run = rt.run_litex_code(bad).unwrap();
        assert!(
            !run.success && run.session_error.is_none(),
            "negative accepted or terminated: {bad}"
        );
        let after: usize = rt
            .execution_environments_stack
            .iter()
            .map(|env| env.facts.facts_by_id.len())
            .sum();
        assert_eq!(before, after, "failed statement leaked facts: {bad}");
        accepted(&mut rt, "A(1,1)=2");
        accepted(&mut rt, "have bad R=2");
    }
}
