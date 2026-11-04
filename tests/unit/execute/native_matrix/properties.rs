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

fn check(rt: &mut Runtime, source: &str, expected: bool) -> String {
    let result = rt.run_litex_code(source).unwrap();
    let json = crate::json_output::project_run_detailed(&result, rt, "matrix-properties", None)
        .stringify();
    assert_eq!(result.success, expected, "{source}\n{json}");
    assert!(result.session_error.is_none(), "{source}\n{json}");
    json
}

#[test]
fn native_matrix_properties_direct_acceptance_and_provenance() {
    let mut rt = runtime();
    let source = include_str!("../../../../examples/test_objs/native_matrix_properties.lit");
    let json = check(&mut rt, source, true);
    for name in [
        "RankRows",
        "RankCols",
        "RankProductLeft",
        "RankProductRight",
        "InnerSelfReal",
        "InnerSelfNonnegative",
        "InnerSelfImaginary",
        "EuclideanNonnegative",
        "FrobeniusNonnegative",
        "CauchySchwarz",
        "EuclideanScale",
        "EuclideanTriangle",
        "InnerLinearRight",
        "FrobeniusTriangle",
        "EuclideanZeroElim",
        "EuclideanZeroIntro",
        "FrobeniusZeroElim",
        "FrobeniusZeroIntro",
        "EuclideanSquareSum",
        "FrobeniusSquareSum",
        "ApplyAdjoint",
        "InverseFromCandidate",
    ] {
        assert!(
            json.contains(&format!("NativeMatrix{name}")),
            "Missing {name}: {json}"
        );
    }
    assert!(json.contains("unit_coefficients"), "{json}");
    assert!(json.contains("zero_vector_alpha"), "{json}");
    assert!(json.contains("requirement_proofs"), "{json}");
}

#[test]
fn native_matrix_properties_reject_false_values_missing_guards_and_wrong_shapes() {
    let cases=[
        "forall m,n N,A matrix(C,m,n):\n    matrix_rank(A,m,n)<=m-1",
        "forall m,n N,A matrix(C,m,n):\n    matrix_rank(A,m,n)<=n-1",
        "forall n N,u,v cart_n(C,n):\n    inner_product(u,v,n) $in R",
        "forall n N,v cart_n(C,n):\n    inner_product(v,v,n) $in N",
        "forall n N,v cart_n(C,n):\n    img(inner_product(v,v,n))=1",
        "forall n N,v cart_n(C,n):\n    euclidean_norm(v,n)=0",
        "forall m,n N,A matrix(C,m,n):\n    frobenius_norm(A,m,n)=0",
        "forall n N,u,v cart_n(C,n):\n    C_abs(inner_product(u,v,n))<=euclidean_norm(u,n)",
        "forall n N,z C,v cart_n(C,n):\n    euclidean_norm(fn(k closed_range(1,n)) C {z*v(k)},n)=euclidean_norm(v,n)",
        "forall n N,u,v cart_n(C,n):\n    euclidean_norm(fn(k closed_range(1,n)) C {2*u(k)+v(k)},n)<=euclidean_norm(u,n)+euclidean_norm(v,n)",
        "forall n N,A,B matrix(C,n,n):\n    det(A,n)!=0\n    =>:\n        matrix_inv(A,n)=B",
        "forall n N,v cart_n(C,n):\n    v=fn(k closed_range(1,n)) C {1}\n    =>:\n        euclidean_norm(v,n)=0",
        "forall n N,v cart_n(C,n):\n    v=fn(k closed_range(1,n+1)) C {0}\n    =>:\n        euclidean_norm(v,n)=0",
    ];
    for source in cases {
        let mut rt = runtime();
        check(&mut rt, "have retained R=3", true);
        check(&mut rt, source, false);
        check(&mut rt, "retained+1=4", true);
    }
}

#[test]
fn native_matrix_properties_zero_dimensions_and_zero_function_alpha() {
    let mut rt = runtime();
    for source in [
        "forall m N,A matrix(C,m,0):\n    matrix_rank(A,m,0)<=0",
        "forall n N,A matrix(C,0,n):\n    matrix_rank(A,0,n)<=0",
        "forall v cart_n(C,0):\n    0<=euclidean_norm(v,0)",
        "forall n N,v cart_n(C,n):\n    v=fn(other closed_range(1,n)) C {0}\n    =>:\n        euclidean_norm(v,n)=0",
    ] { check(&mut rt,source,true); }
}

#[test]
fn native_matrix_properties_respect_builtin_ceiling_and_failed_publication() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have m,n N\nhave A matrix(C,m,n)=zero_matrix(m,n)",
        true,
    );
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("matrix_rank(A,m,n)<=m", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("atomic fact");
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
    let before = rt.top_exec_env().facts.facts_by_id.len();
    check(
        &mut rt,
        "forall n N,v cart_n(C,n):\n    euclidean_norm(v,n)=0",
        false,
    );
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    check(&mut rt, "matrix_rank(A,m,n)<=m", true);
}

#[test]
fn native_matrix_properties_all_output_languages_retain_rule_identity() {
    for language in OutputLanguage::ALL {
        let mut rt = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let source = "forall m,n N,A matrix(C,m,n):\n    matrix_rank(A,m,n)<=m";
        let json = check(&mut rt, source, true);
        assert!(
            json.contains("NativeMatrixRankRows"),
            "{language:?}: {json}"
        );
    }
}
