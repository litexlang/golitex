use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
fn accepted(rt: &mut Runtime, source: &str) {
    let result = rt.run_litex_code(source).unwrap();
    assert!(
        result.success && result.session_error.is_none(),
        "{source}\n{}",
        crate::json_output::emit_run_detailed(&result, rt, "native_matrix", None)
    );
}

#[test]
fn native_matrix_function_spaces_and_explicit_domains() {
    let mut rt = runtime(OutputLanguage::English);
    for statement in [
        "forall S set,n N:\n    cart_n(S,n)=finite_seq(S,n)=fn(k closed_range(1,n)) S",
        "forall S set,m,n N:\n    matrix(S,m,n)=fn(r closed_range(1,m),c closed_range(1,n)) S",
        "have fn rectangular(r closed_range(1,2),c closed_range(1,3)) R=r+c",
        "rectangular $in matrix(R,2,3)",
        "release thm fn_set_member(rectangular,matrix(C,2,3))",
        "forall S set,m,n N,mat matrix(S,m,n),r closed_range(1,m),c closed_range(1,n):\n    mat(r,c) $in S",
        "have MatrixAlias set=matrix(R,2,3)",
        "have aliased MatrixAlias=rectangular",
        "aliased(2,3) $in R",
        "have fn empty(r closed_range(1,0),c closed_range(1,3)) R=0",
        "empty $in matrix(R,0,3)",
    ] {accepted(&mut rt,statement)}
}

#[test]
fn native_matrix_numeric_tracer_needs_no_precomputed_coordinates() {
    let mut rt = runtime(OutputLanguage::English);
    for statement in [
        "have fn A(r closed_range(1,2),c closed_range(1,2)) R=r+c",
        "A $in matrix(R,2,2)",
        "det(A,2)=-1",
        "transpose(A,2,2)(1,2)=3",
        "trace(A,2)=6",
        "det(A,2)+2=1",
        "zero_matrix(2,3)(2,3)=0",
        "zero_matrix(2,3) $in matrix(R,2,3)",
        "identity_matrix(3)(2,2)=1",
        "identity_matrix(3)(1,2)=0",
        "identity_matrix(3) $in matrix(C,3,3)",
        "by fn_extension transpose(transpose(A,2,2),2,2)=A",
    ] {
        accepted(&mut rt, statement)
    }
}

#[test]
fn native_matrix_complex_and_degenerate_exact_values() {
    let mut rt = runtime(OutputLanguage::English);
    for statement in [
        "have fn F(r closed_range(1,2),c closed_range(1,3)) C=r+c+i",
        "transpose(F,2,3)(3,2)=5+i",
        "conjugate_transpose(F,2,3)(3,2)=5-i",
        "by fn_extension conjugate_transpose(conjugate_transpose(F,2,3),3,2)=F",
        "have fn one(r closed_range(1,1),c closed_range(1,1)) C=i",
        "det(one,1)=i",
        "trace(one,1)=i",
        "have fn empty(r closed_range(1,0),c closed_range(1,0)) C=0",
        "det(empty,0)=1",
        "trace(empty,0)=0",
        "det(zero_matrix(2,2),2)=0",
        "trace(identity_matrix(3),3)=3",
    ] {
        accepted(&mut rt, statement)
    }
}

#[test]
fn native_matrix_returned_functions_retain_actual_matrix_domains() {
    let mut rt = runtime(OutputLanguage::English);
    for statement in [
        "have fn make(t R) matrix(R,2,2)=fn(r closed_range(1,2),c closed_range(1,2)) R {t+r+c}",
        "make(1)(2,1)=4",
        "have fn flip(t R) matrix(R,2,2)=transpose(make(t),2,2)",
        "flip(1)(1,2)=4",
        "trace(make(1),2)=8",
    ] {
        accepted(&mut rt, statement)
    }
}

#[test]
fn native_matrix_rejects_missing_shape_scalar_and_value_evidence_and_keeps_context() {
    for target in [
        "let bad=matrix(R,-1,3)",
        "let bad=matrix(R,1/2,3)",
        "let bad=zero_matrix(-1,3)",
        "let bad=identity_matrix(-1)",
        "let bad=det(square,-1)",
        "let bad=det(square,1/2)",
        "let bad=det(rectangular,2)",
        "let bad=trace(rectangular,2)",
        "let bad=transpose(rectangular,3,2)",
        "let bad=det(wide,2)",
        "zero_matrix(2,3)(0,1)=0",
        "identity_matrix(3)(4,4)=1",
        "transpose(rectangular,2,3)(1,3)=4",
        "transpose(rectangular,2,3)(1)(2)=3",
        "complex $in matrix(R,2,2)",
        "det(square,2)=1",
        "trace(square,2)=0",
        "forall mat matrix(R,2,2):\n    det(mat,2)=0",
        "forall mat matrix(C,2,2):\n    det(mat,2) $in R",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        accepted(
            &mut rt,
            "have fn square(r closed_range(1,2),c closed_range(1,2)) R=r+c",
        );
        accepted(
            &mut rt,
            "have fn rectangular(r closed_range(1,2),c closed_range(1,3)) R=r+c",
        );
        accepted(&mut rt, "have fn wide(r N+,c N+) R=r+c");
        accepted(
            &mut rt,
            "have fn complex(r closed_range(1,2),c closed_range(1,2)) C=r+c+i",
        );
        let result = rt.run_litex_code(target).unwrap();
        assert!(!result.success, "unexpected proof of {target}");
        assert!(
            result.session_error.is_none(),
            "hard session error: {target}"
        );
        accepted(&mut rt, "square(2,1)=3");
    }
}

#[test]
fn native_matrix_rule_outputs_retain_checked_call_and_exact_evaluation_evidence() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        accepted(
            &mut rt,
            "have fn A(r closed_range(1,2),c closed_range(1,2)) R=r+c",
        );
        let result = rt.run_litex_code("det(A,2)=-1").unwrap();
        assert!(result.success, "{language:?}");
        let detailed = crate::json_output::emit_run_detailed(&result, &rt, "matrix-proof", None);
        assert!(detailed.contains("MatrixScalarDefinition"), "{detailed}");
        if language == OutputLanguage::English {
            assert!(detailed.contains("function_evaluations"), "{detailed}");
            assert!(detailed.contains("application_well_defined"), "{detailed}");
        }
        let normal = crate::json_output::emit_run_normal(&result, &rt, "matrix-proof", None);
        assert!(!normal.contains("internal_bug"));
    }
}

#[test]
fn native_matrix_singleton_delta_does_not_assume_different_names_are_unequal() {
    let mut rt = runtime(OutputLanguage::English);
    // Numeric identity components are exact; unrelated symbols do not become
    // distinct merely because they have different names.
    let result = rt
        .run_litex_code("forall x,y closed_range(1,3):\n    identity_matrix(3)(x,y)=0")
        .unwrap();
    assert!(!result.success);
    assert!(result.session_error.is_none());
    accepted(&mut rt, "identity_matrix(3)(1,2)=0");
}

#[test]
fn native_matrix_generic_carriers_components_and_congruence() {
    let mut rt = runtime(OutputLanguage::English);
    for statement in [
        "forall m,n N:\n    zero_matrix(m,n) $in matrix(C,m,n)",
        "forall n N:\n    identity_matrix(n) $in matrix(R,n,n)",
        "forall A matrix(R,2,3):\n    transpose(A,2,3) $in matrix(R,3,2)",
        "forall A matrix(C,2,3),r closed_range(1,3),c closed_range(1,2):\n    transpose(A,2,3)(r,c)=A(c,r)",
        "forall A matrix(R,2,2):\n    det(A,2) $in R",
        "forall A matrix(C,2,2):\n    trace(A,2) $in C",
        "forall A,B matrix(C,2,2):\n    A=B\n    =>:\n        det(A,2)=det(B,2)\n        trace(A,2)=trace(B,2)\n        transpose(A,2,2)=transpose(B,2,2)",
    ] {accepted(&mut rt,statement)}
}

#[test]
fn native_matrix_parsing_rejects_wrong_arity_and_reserved_declarations() {
    for statement in [
        "let bad=matrix(R,2)",
        "let bad=matrix(R,2,3,4)",
        "let bad=zero_matrix(2)",
        "let bad=identity_matrix(2,3)",
        "let bad=transpose(0,2)",
        "let bad=conjugate_transpose(0,2)",
        "let bad=det(0)",
        "let bad=trace(0)",
        "let det=0",
        "let trace=0",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = rt.run_litex_code(statement).unwrap();
        assert!(!result.success, "{statement}");
        assert!(result.session_error.is_none(), "{statement}");
        accepted(&mut rt, "1+1=2");
    }
}
