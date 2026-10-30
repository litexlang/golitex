use crate::prelude::*;
fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}
fn check(rt: &mut Runtime, source: &str, expected: bool) {
    let run = rt.run_litex_code(source).unwrap();
    assert_eq!(
        run.success,
        expected,
        "{source}\n{}",
        crate::json_output::project_run_detailed(&run, rt, "test", None).stringify()
    );
    assert!(run.session_error.is_none(), "{source}");
}
// name, generic direct theorem, original explicit application.
const CASES: &[(&str, &str, &str)] = &[
    (
        "NativeMatrixMulAssociative",
        r#"thm direct_mul_associative:
    ? forall m,k,p,n N,A matrix(C,m,k),B matrix(C,k,p),D matrix(C,p,n):
        matrix_mul(matrix_mul(A,B,m,k,p),D,m,p,n)=matrix_mul(A,matrix_mul(B,D,k,p,n),m,k,n)
"#,
        r#"    by thm matrix_mul_associative(A,B,D,m,k,p,n) => matrix_mul(matrix_mul(A,B,m,k,p),D,m,p,n)=matrix_mul(A,matrix_mul(B,D,k,p,n),m,k,n)
"#,
    ),
    (
        "NativeMatrixMulDistributiveLeft",
        r#"thm direct_mul_distributive_left:
    ? forall m,k,n N,A matrix(C,m,k),B,D matrix(C,k,n):
        matrix_mul(A,matrix_add(B,D,k,n),m,k,n)=matrix_add(matrix_mul(A,B,m,k,n),matrix_mul(A,D,m,k,n),m,n)
"#,
        r#"    by thm matrix_mul_distributive_left(A,B,D,m,k,n) => matrix_mul(A,matrix_add(B,D,k,n),m,k,n)=matrix_add(matrix_mul(A,B,m,k,n),matrix_mul(A,D,m,k,n),m,n)
"#,
    ),
    (
        "NativeMatrixMulDistributiveRight",
        r#"thm direct_mul_distributive_right:
    ? forall m,k,n N,A,B matrix(C,m,k),D matrix(C,k,n):
        matrix_mul(matrix_add(A,B,m,k),D,m,k,n)=matrix_add(matrix_mul(A,D,m,k,n),matrix_mul(B,D,m,k,n),m,n)
"#,
        r#"    by thm matrix_mul_distributive_right(A,B,D,m,k,n) => matrix_mul(matrix_add(A,B,m,k),D,m,k,n)=matrix_add(matrix_mul(A,D,m,k,n),matrix_mul(B,D,m,k,n),m,n)
"#,
    ),
    (
        "NativeMatrixMulIdentityLeft",
        r#"thm direct_mul_identity_left:
    ? forall m,n N,A matrix(C,m,n):
        matrix_mul(identity_matrix(m),A,m,m,n)=A
"#,
        r#"    by thm matrix_mul_identity(A,m,n) => matrix_mul(identity_matrix(m),A,m,m,n)=A
"#,
    ),
    (
        "NativeMatrixMulIdentityRight",
        r#"thm direct_mul_identity_right:
    ? forall m,n N,A matrix(C,m,n):
        matrix_mul(A,identity_matrix(n),m,n,n)=A
"#,
        r#"    by thm matrix_mul_identity(A,m,n) => matrix_mul(A,identity_matrix(n),m,n,n)=A
"#,
    ),
    (
        "NativeMatrixMulZeroRight",
        r#"thm direct_mul_zero_right:
    ? forall m,n,p N,A matrix(C,m,n):
        matrix_mul(A,zero_matrix(n,p),m,n,p)=zero_matrix(m,p)
"#,
        r#"    by thm matrix_mul_zero(A,m,n,p) => matrix_mul(A,zero_matrix(n,p),m,n,p)=zero_matrix(m,p)
"#,
    ),
    (
        "NativeMatrixMulZeroLeft",
        r#"thm direct_mul_zero_left:
    ? forall m,n,p N,A matrix(C,m,n):
        matrix_mul(zero_matrix(p,m),A,p,m,n)=zero_matrix(p,n)
"#,
        r#"    by thm matrix_mul_zero(A,m,n,p) => matrix_mul(zero_matrix(p,m),A,p,m,n)=zero_matrix(p,n)
"#,
    ),
    (
        "NativeMatrixApplyIdentity",
        r#"thm direct_apply_identity:
    ? forall n N,v cart_n(C,n):
        matrix_apply(identity_matrix(n),v,n,n)=v
"#,
        r#"    by thm matrix_apply_identity(v,n) => matrix_apply(identity_matrix(n),v,n,n)=v
"#,
    ),
    (
        "NativeMatrixApplyCompose",
        r#"thm direct_apply_compose:
    ? forall m,k,n N,A matrix(C,m,k),B matrix(C,k,n),v cart_n(C,n):
        matrix_apply(matrix_mul(A,B,m,k,n),v,m,n)=matrix_apply(A,matrix_apply(B,v,k,n),m,k)
"#,
        r#"    by thm matrix_apply_compose(A,B,v,m,k,n) => matrix_apply(matrix_mul(A,B,m,k,n),v,m,n)=matrix_apply(A,matrix_apply(B,v,k,n),m,k)
"#,
    ),
    (
        "NativeMatrixMatrixTransposeMul",
        r#"thm direct_matrix_transpose_mul:
    ? forall m,k,n N,A matrix(C,m,k),B matrix(C,k,n):
        transpose(matrix_mul(A,B,m,k,n),m,n)=matrix_mul(transpose(B,k,n),transpose(A,m,k),n,k,m)
"#,
        r#"    by thm matrix_transpose_mul(A,B,m,k,n) => transpose(matrix_mul(A,B,m,k,n),m,n)=matrix_mul(transpose(B,k,n),transpose(A,m,k),n,k,m)
"#,
    ),
    (
        "NativeMatrixMatrixAdjointMul",
        r#"thm direct_matrix_adjoint_mul:
    ? forall m,k,n N,A matrix(C,m,k),B matrix(C,k,n):
        conjugate_transpose(matrix_mul(A,B,m,k,n),m,n)=matrix_mul(conjugate_transpose(B,k,n),conjugate_transpose(A,m,k),n,k,m)
"#,
        r#"    by thm matrix_adjoint_mul(A,B,m,k,n) => conjugate_transpose(matrix_mul(A,B,m,k,n),m,n)=matrix_mul(conjugate_transpose(B,k,n),conjugate_transpose(A,m,k),n,k,m)
"#,
    ),
    (
        "NativeMatrixTraceAdd",
        r#"thm direct_trace_add:
    ? forall n N,A,B matrix(C,n,n):
        trace(matrix_add(A,B,n,n),n)=trace(A,n)+trace(B,n)
"#,
        r#"    by thm matrix_trace_linearity(A,B,1,n) => trace(matrix_add(A,B,n,n),n)=trace(A,n)+trace(B,n)
"#,
    ),
    (
        "NativeMatrixTraceScale",
        r#"thm direct_trace_scale:
    ? forall n N,A matrix(C,n,n),z C:
        trace(matrix_scale(z,A,n,n),n)=z*trace(A,n)
"#,
        r#"    by thm matrix_trace_linearity(A,A,z,n) => trace(matrix_scale(z,A,n,n),n)=z*trace(A,n)
"#,
    ),
    (
        "NativeMatrixTraceCyclic",
        r#"thm direct_trace_cyclic:
    ? forall m,n N,A matrix(C,m,n),B matrix(C,n,m):
        trace(matrix_mul(A,B,m,n,m),m)=trace(matrix_mul(B,A,n,m,n),n)
"#,
        r#"    by thm matrix_trace_cyclic(A,B,m,n) => trace(matrix_mul(A,B,m,n,m),m)=trace(matrix_mul(B,A,n,m,n),n)
"#,
    ),
    (
        "NativeMatrixPowerZero",
        r#"thm direct_power_zero:
    ? forall n N,A matrix(C,n,n):
        matrix_power(A,n,0)=identity_matrix(n)
"#,
        r#"    by thm matrix_power_zero(A,n) => matrix_power(A,n,0)=identity_matrix(n)
"#,
    ),
    (
        "NativeMatrixPowerSuccessor",
        r#"thm direct_power_successor:
    ? forall n,p N,A matrix(C,n,n):
        matrix_power(A,n,p+1)=matrix_mul(matrix_power(A,n,p),A,n,n,n)
"#,
        r#"    by thm matrix_power_successor(A,n,p) => matrix_power(A,n,p+1)=matrix_mul(matrix_power(A,n,p),A,n,n,n)
"#,
    ),
    (
        "NativeMatrixPowerAdd",
        r#"thm direct_power_add:
    ? forall n,p,q N,A matrix(C,n,n):
        matrix_power(A,n,p+q)=matrix_mul(matrix_power(A,n,p),matrix_power(A,n,q),n,n,n)
"#,
        r#"    by thm matrix_power_add(A,n,p,q) => matrix_power(A,n,p+q)=matrix_mul(matrix_power(A,n,p),matrix_power(A,n,q),n,n,n)
"#,
    ),
    (
        "NativeMatrixDetIdentity",
        r#"thm direct_det_identity:
    ? forall n N:
        det(identity_matrix(n),n)=1
"#,
        r#"    by thm matrix_det_identity(n) => det(identity_matrix(n),n)=1
"#,
    ),
    (
        "NativeMatrixDetTranspose",
        r#"thm direct_det_transpose:
    ? forall n N,A matrix(C,n,n):
        det(transpose(A,n,n),n)=det(A,n)
"#,
        r#"    by thm matrix_det_transpose(A,n) => det(transpose(A,n,n),n)=det(A,n)
"#,
    ),
    (
        "NativeMatrixDetAdjoint",
        r#"thm direct_det_adjoint:
    ? forall n N,A matrix(C,n,n):
        det(conjugate_transpose(A,n,n),n)=conj(det(A,n))
"#,
        r#"    by thm matrix_det_adjoint(A,n) => det(conjugate_transpose(A,n,n),n)=conj(det(A,n))
"#,
    ),
    (
        "NativeMatrixDetMul",
        r#"thm direct_det_mul:
    ? forall n N,A,B matrix(C,n,n):
        det(matrix_mul(A,B,n,n,n),n)=det(A,n)*det(B,n)
"#,
        r#"    by thm matrix_det_mul(A,B,n) => det(matrix_mul(A,B,n,n,n),n)=det(A,n)*det(B,n)
"#,
    ),
    (
        "NativeMatrixAdjugateLeft",
        r#"thm direct_adjugate_left:
    ? forall n N,A matrix(C,n,n):
        matrix_mul(matrix_adjugate(A,n),A,n,n,n)=matrix_scale(det(A,n),identity_matrix(n),n,n)
"#,
        r#"    by thm matrix_adjugate_identity(A,n) => matrix_mul(matrix_adjugate(A,n),A,n,n,n)=matrix_scale(det(A,n),identity_matrix(n),n,n)
"#,
    ),
    (
        "NativeMatrixInverseLeft",
        r#"thm direct_inverse_left:
    ? forall n N,A matrix(C,n,n):
        det(A,n)!=0
        =>:
            matrix_mul(matrix_inverse(A,n),A,n,n,n)=identity_matrix(n)
"#,
        r#"    by thm matrix_inverse_laws(A,n) => matrix_mul(matrix_inverse(A,n),A,n,n,n)=identity_matrix(n)
"#,
    ),
    (
        "NativeMatrixAdjugateRight",
        r#"thm direct_adjugate_right:
    ? forall n N,A matrix(C,n,n):
        matrix_mul(A,matrix_adjugate(A,n),n,n,n)=matrix_scale(det(A,n),identity_matrix(n),n,n)
"#,
        r#"    by thm matrix_adjugate_identity(A,n) => matrix_mul(A,matrix_adjugate(A,n),n,n,n)=matrix_scale(det(A,n),identity_matrix(n),n,n)
"#,
    ),
    (
        "NativeMatrixInverseRight",
        r#"thm direct_inverse_right:
    ? forall n N,A matrix(C,n,n):
        det(A,n)!=0
        =>:
            matrix_mul(A,matrix_inverse(A,n),n,n,n)=identity_matrix(n)
"#,
        r#"    by thm matrix_inverse_laws(A,n) => matrix_mul(A,matrix_inverse(A,n),n,n,n)=identity_matrix(n)
"#,
    ),
    (
        "NativeMatrixRankZero",
        r#"thm direct_rank_zero:
    ? forall m,n N:
        matrix_rank(zero_matrix(m,n),m,n)=0
"#,
        r#"    by thm matrix_rank_zero(m,n) => matrix_rank(zero_matrix(m,n),m,n)=0
"#,
    ),
    (
        "NativeMatrixRankIdentity",
        r#"thm direct_rank_identity:
    ? forall n N:
        matrix_rank(identity_matrix(n),n,n)=n
"#,
        r#"    by thm matrix_rank_identity(n) => matrix_rank(identity_matrix(n),n,n)=n
"#,
    ),
    (
        "NativeMatrixMatrixRankTranspose",
        r#"thm direct_matrix_rank_transpose:
    ? forall m,n N,A matrix(C,m,n):
        matrix_rank(transpose(A,m,n),n,m)=matrix_rank(A,m,n)
"#,
        r#"    by thm matrix_rank_transpose(A,m,n) => matrix_rank(transpose(A,m,n),n,m)=matrix_rank(A,m,n)
"#,
    ),
    (
        "NativeMatrixMatrixRankAdjoint",
        r#"thm direct_matrix_rank_adjoint:
    ? forall m,n N,A matrix(C,m,n):
        matrix_rank(conjugate_transpose(A,m,n),n,m)=matrix_rank(A,m,n)
"#,
        r#"    by thm matrix_rank_adjoint(A,m,n) => matrix_rank(conjugate_transpose(A,m,n),n,m)=matrix_rank(A,m,n)
"#,
    ),
    (
        "NativeMatrixRankInvertible",
        r#"thm direct_rank_invertible:
    ? forall n N,A matrix(C,n,n):
        det(A,n)!=0
        =>:
            matrix_rank(A,n,n)=n
"#,
        r#"    by thm matrix_rank_invertible(A,n) => matrix_rank(A,n,n)=n
"#,
    ),
    (
        "NativeMatrixInnerConjugateSymmetry",
        r#"thm direct_inner_conjugate_symmetry:
    ? forall n N,u,v cart_n(C,n):
        inner_product(u,v,n)=conj(inner_product(v,u,n))
"#,
        r#"    by thm inner_product_conjugate_symmetry(u,v,n) => inner_product(u,v,n)=conj(inner_product(v,u,n))
"#,
    ),
    (
        "NativeMatrixEuclideanNormSquare",
        r#"thm direct_euclidean_norm_square:
    ? forall n N,v cart_n(C,n):
        euclidean_norm(v,n)^2=inner_product(v,v,n)
"#,
        r#"    by thm euclidean_norm_square(v,n) => euclidean_norm(v,n)^2=inner_product(v,v,n)
"#,
    ),
    (
        "NativeMatrixFrobeniusNormScale",
        r#"thm direct_frobenius_norm_scale:
    ? forall m,n N,z C,A matrix(C,m,n):
        frobenius_norm(matrix_scale(z,A,m,n),m,n)=C_abs(z)*frobenius_norm(A,m,n)
"#,
        r#"    by thm frobenius_norm_scale(z,A,m,n) => frobenius_norm(matrix_scale(z,A,m,n),m,n)=C_abs(z)*frobenius_norm(A,m,n)
"#,
    ),
];
#[test]
fn native_matrix_laws_all_33_direct_and_original_explicit() {
    assert_eq!(CASES.len(), 33);
    for (name, direct, explicit) in CASES {
        let mut rt = runtime();
        let run = rt.run_litex_code(direct).unwrap();
        let output = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(
            run.success && run.session_error.is_none(),
            "{name}: {direct}\n{output}"
        );
        assert!(
            output.contains(name),
            "Wrong provenance for {name}: {output}"
        );
        assert!(
            output.contains("left_equal")
                && output.contains("right_equal")
                && output.contains("requirement_proofs")
        );
        check(&mut runtime(), &format!("{direct}{explicit}"), true);
        // Symmetry consumes the same fixed schema, independently of the first run.
        let (before, goal) = direct.rsplit_once("        ").unwrap();
        let (left, right) = goal.trim().split_once('=').unwrap();
        check(
            &mut runtime(),
            &format!("{before}        {right}={left}"),
            true,
        );
    }
}
#[test]
fn native_matrix_laws_false_values_missing_premises_and_domains() {
    for source in [
        "forall m,n N,A matrix(C,m,n):\n    matrix_mul(identity_matrix(m),A,m,m,n)=zero_matrix(m,n)",
        "forall n N,A,B matrix(C,n,n):\n    matrix_mul(A,B,n,n,n)=matrix_mul(B,A,n,n,n)",
        "forall n N,A,B matrix(C,n,n):\n    trace(matrix_add(A,B,n,n),n)=trace(A,n)-trace(B,n)",
        "forall n N,A matrix(C,n,n):\n    det(conjugate_transpose(A,n,n),n)=det(A,n)",
        "forall n,p N,A matrix(C,n,n):\n    matrix_power(A,n,p+2)=matrix_mul(matrix_power(A,n,p),A,n,n,n)",
        "forall n N,A matrix(C,n,n):\n    matrix_rank(A,n,n)=n",
        "forall n N,A matrix(C,n,n):\n    matrix_mul(A,matrix_inverse(A,n),n,n,n)=identity_matrix(n)",
        "forall n N,A,B matrix(C,n,n):\n    det(A,n)!=0\n    =>:\n        matrix_mul(A,matrix_inverse(B,n),n,n,n)=identity_matrix(n)",
        "forall n N,A,B matrix(C,n,n):\n    matrix_mul(A,matrix_adjugate(B,n),n,n,n)=matrix_scale(det(A,n),identity_matrix(n),n,n)",
        "forall n N,u,v cart_n(C,n):\n    inner_product(u,v,n)=inner_product(v,u,n)",
        "forall n N,v cart_n(C,n):\n    euclidean_norm(v,n)^2=inner_product(v,v,n)+1",
        "forall m,n N,z C,A matrix(C,m,n):\n    frobenius_norm(matrix_scale(z,A,m,n),m,n)=z*frobenius_norm(A,m,n)",
        "forall n N,A,B matrix(C,n,n):\n    conjugate_transpose(matrix_mul(A,B,n,n,n),n,n)=matrix_mul(conjugate_transpose(A,n,n),conjugate_transpose(B,n,n),n,n,n)",
        "have A matrix(C,2,3)\nmatrix_mul(identity_matrix(3),A,3,3,3)=A",
        "have A matrix(C,2,3)\nmatrix_rank(A,2,3)=3",
        "matrix_mul(zero_matrix(2,2),matrix_inverse(zero_matrix(2,2),2),2,2,2)=zero_matrix(2,2)",
        "matrix_power(identity_matrix(2),2,-1)=identity_matrix(2)",
        "det(identity_matrix(-1),-1)=1",
    ] { check(&mut runtime(),source,false); }
}
#[test]
fn native_matrix_laws_ceiling_scope_and_failed_publication() {
    let mut rt = runtime();
    check(&mut rt, "have m,n N\nhave A matrix(C,m,n)", true);
    let source = "matrix_mul(identity_matrix(m),A,m,m,n)=A";
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    for level in [
        VerifyStateLevel::Direct,
        VerifyStateLevel::KnownSpecialProperty,
    ] {
        assert!(rt
            .verify_fact(&goal, VerifyState::new(level))
            .unwrap()
            .is_failed());
    }
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    let count = rt.top_exec_env().facts.facts_by_id.len();
    let bad = "forall q N,B matrix(C,q,q):\n    matrix_rank(B,q,q)=q";
    check(&mut rt, bad, false);
    assert_eq!(count, rt.top_exec_env().facts.facts_by_id.len());
    check(&mut rt, bad, false);
    check(&mut rt, source, true);
    check(&mut rt, "have B matrix(C,2,2)", true);
    check(&mut rt, "matrix_rank(B,2,2)=2", false);
    check(&mut rt, "0=1", false);
}
#[test]
fn native_matrix_laws_keep_inverse_conditions_and_empty_domains() {
    check(&mut runtime(),"forall A matrix(C,0,0):\n    det(A,0)!=0\n    =>:\n        matrix_mul(A,matrix_inverse(A,0),0,0,0)=identity_matrix(0)",true);
    check(
        &mut runtime(),
        "forall A matrix(C,0,3):\n    matrix_mul(identity_matrix(0),A,0,0,3)=A",
        true,
    );
    check(&mut runtime(),"forall z C,A matrix(C,0,0):\n    frobenius_norm(matrix_scale(z,A,0,0),0,0)=C_abs(z)*frobenius_norm(A,0,0)",true);
}
#[test]
fn native_matrix_laws_output_and_lean_rejection() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code("have A matrix(C,2,2)\nmatrix_mul(identity_matrix(2),A,2,2,2)=A")
        .unwrap();
    assert!(run.success);
    let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    assert!(json.contains("NativeMatrixMulIdentityLeft"));
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "native_matrix_laws")
        .unwrap_err();
    // Matrix objects have no Lean object replay yet; no arbitrary axiom fallback.
    assert!(
        error.route.contains("Object") || error.route == "Equality/BuiltinRule",
        "{}: {}",
        error.route,
        error.message
    );
}
#[test]
fn run_examples_native_matrix_laws() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/proof_nodes/equal/by_builtin_rule/native_matrix_laws.lit");
    check(
        &mut runtime(),
        &std::fs::read_to_string(path).unwrap(),
        true,
    );
}
