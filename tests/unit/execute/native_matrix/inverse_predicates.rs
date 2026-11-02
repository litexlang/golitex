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
    let result = rt.run_litex_code(source).unwrap();
    assert_eq!(
        result.success,
        expected,
        "{source}\n{}",
        crate::json_output::project_run_detailed(&result, rt, "matrix_inverse", None).stringify()
    );
    assert!(result.session_error.is_none(), "{source}");
}

#[test]
fn native_matrix_inverse_predicates_both_determinant_directions() {
    let mut rt = runtime();
    check(&mut rt, "forall n N,A matrix(C,n,n):\n    det(A,n)!=0\n    =>:\n        $matrix_inversible(A,n)\n        $is_matrix_inv(A,matrix_inv(A,n),n)", true);
    check(&mut rt, "forall n N,A matrix(C,n,n):\n    $matrix_inversible(A,n)\n    =>:\n        det(A,n)!=0\n        matrix_mul(A,matrix_inv(A,n),n,n,n)=identity_matrix(n)\n        matrix_mul(matrix_inv(A,n),A,n,n,n)=identity_matrix(n)", true);
    check(&mut rt, "forall n N,A,B matrix(C,n,n):\n    $is_matrix_inv(A,B,n)\n    =>:\n        $matrix_inversible(A,n)\n        det(A,n)!=0\n        matrix_mul(A,B,n,n,n)=identity_matrix(n)\n        matrix_mul(B,A,n,n,n)=identity_matrix(n)", true);
}

#[test]
fn native_matrix_inverse_predicates_definition_existence_and_selection() {
    let mut rt = runtime();
    check(&mut rt, "thm candidate_definition:\n    ? forall n N,A,B matrix(C,n,n):\n        matrix_mul(A,B,n,n,n)=identity_matrix(n)\n        matrix_mul(B,A,n,n,n)=identity_matrix(n)\n        =>:\n            $is_matrix_inv(A,B,n)\n    by def $is_matrix_inv(A,B,n)", true);
    check(&mut rt, "thm select_candidate:\n    ? forall n N,A,B matrix(C,n,n):\n        $is_matrix_inv(A,B,n)\n        =>:\n            matrix_inv(A,n)=B\n    by thm matrix_inverse_from_candidate(A,B,n) => matrix_inv(A,n)=B", true);
    check(&mut rt, "forall n N,A matrix(C,n,n):\n    $matrix_inversible(A,n)\n    =>:\n        exist B matrix(C,n,n) st {$is_matrix_inv(A,B,n)}", true);
    check(&mut rt, "thm existence_definition:\n    ? forall n N,A matrix(C,n,n):\n        exist B matrix(C,n,n) st {$is_matrix_inv(A,B,n)}\n        =>:\n            $matrix_inversible(A,n)\n    by def $matrix_inversible(A,n)", true);
}

#[test]
fn native_matrix_inverse_predicates_real_complex_zero_and_rejections() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have fn A(r closed_range(1,2),c closed_range(1,2)) R=r+c",
        true,
    );
    check(&mut rt, "det(A,2)=-1", true);
    check(&mut rt, "det(A,2)!=0", true);
    check(&mut rt, "$matrix_inversible(A,2)", true);
    check(&mut rt, "matrix_inv(A,2) $in matrix(R,2,2)", true);
    check(&mut rt, "matrix_inv(A,2)(1,1)=-4", true);
    check(&mut rt, "$is_matrix_inv(A,matrix_inv(A,2),2)", true);
    check(&mut rt, "det(diagonal_matrix((i,1),2),2)=i", true);
    check(&mut rt, "det(diagonal_matrix((i,1),2),2)!=0", true);
    check(
        &mut rt,
        "$matrix_inversible(diagonal_matrix((i,1),2),2)",
        true,
    );
    check(&mut rt, "det(identity_matrix(0),0)=1", true);
    check(&mut rt, "det(identity_matrix(0),0)!=0", true);
    check(&mut rt, "$matrix_inversible(identity_matrix(0),0)", true);
    check(
        &mut rt,
        "$is_matrix_inv(identity_matrix(0),matrix_inv(identity_matrix(0),0),0)",
        true,
    );
    for source in [
        "$matrix_inversible(zero_matrix(2,2),2)",
        "$is_matrix_inv(identity_matrix(2),zero_matrix(2,2),2)",
        "$is_matrix_inv(identity_matrix(2),identity_matrix(3),2)",
        "$matrix_inversible(zero_matrix(2,3),2)",
        "$matrix_inversible(identity_matrix(2),-1)",
        "$matrix_inversible(identity_matrix(2))",
        "matrix_inv(zero_matrix(2,2),2) $in matrix(C,2,2)",
        "forall n N,B matrix(C,n,n):\n    matrix_inv(B,n) $in matrix(C,n,n)",
        "matrix_inverse(A,2)(1,1)=-4",
        "prop matrix_inversible(x C):\n    x=x",
        "have fn matrix_inversible(x C) C=x",
        "have fn is_matrix_inv(x C) C=x",
        "have fn matrix_inv(x C) C=x",
    ] {
        check(&mut rt, source, false);
        check(&mut rt, "matrix_inv(A,2)(1,1)=-4", true);
    }
    check(&mut rt, "det(zero_matrix(2,2),2)=0", true);
    check(&mut rt, "not $matrix_inversible(zero_matrix(2,2),2)", true);
}

#[test]
fn native_matrix_inverse_predicates_respect_ceiling_and_failed_publication() {
    let mut rt = runtime();
    check(&mut rt, "have A matrix(C,2,2)=identity_matrix(2)", true);
    check(&mut rt, "det(A,2)=1", true);
    check(&mut rt, "det(A,2)!=0", true);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$matrix_inversible(A,2)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("predicate goal")
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
    check(
        &mut rt,
        "forall k N,B matrix(C,k,k):\n    $matrix_inversible(B,k)",
        false,
    );
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), count);
    check(&mut rt, "0=1", false);
    check(&mut rt, "$matrix_inversible(A,2)", true);
}
