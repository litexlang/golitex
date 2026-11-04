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
    let json = crate::json_output::project_run_detailed(&result, rt, "determinant-formulas", None)
        .stringify();
    assert_eq!(result.success, expected, "{source}\n{json}");
    assert!(result.session_error.is_none(), "{source}\n{json}");
    json
}

#[test]
fn native_matrix_determinant_formulas_forward_reverse_and_boundaries() {
    for source in [
        include_str!("../../../../examples/test_objs/native_matrix_determinant_formulas.lit"),
        include_str!(
            "../../../../lean/examples/native_matrix_determinant_formulas_reverse/statement.lit"
        ),
    ] {
        let json = check(&mut runtime(), source, true);
        for rule in [
            "DetLaplaceRow",
            "DetLaplaceColumn",
            "DetUpperTriangular",
            "DetLowerTriangular",
        ] {
            assert!(
                json.contains(&format!("NativeMatrix{rule}")),
                "{rule}: {json}"
            );
        }
        assert!(json.contains("requirement_proofs"));
    }
    let boundaries = include_str!(
        "../../../../lean/examples/native_matrix_determinant_boundaries/statement.lit"
    );
    // Each profile must work independently of earlier exported generic theorems.
    for block in boundaries.split("thm ").skip(1) {
        let source = format!("thm {block}");
        let json = check(&mut runtime(), &source, true);
        assert!(json.contains("NativeMatrixDet"), "{source}\n{json}");
    }
}

#[test]
fn native_matrix_determinant_formulas_reject_missing_guards_and_malformed_formulas() {
    let cases=[
        "forall n N,A matrix(C,n,n):\n    det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C {A(k,k)})",
        "forall n N,A matrix(C,n,n):\n    forall r,c closed_range(1,n):\n        c+1<r\n        =>:\n            A(r,c)=0\n    =>:\n        det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C {A(k,k)})",
        "forall n N,A matrix(C,n,n):\n    forall r,c closed_range(1,n):\n        r+1<c\n        =>:\n            A(r,c)=0\n    =>:\n        det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C {A(k,k)})",
        "forall n N,A matrix(C,n,n):\n    forall r,c closed_range(1,n):\n        c<r\n        =>:\n            A(r,c)=1\n    =>:\n        det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C {A(k,k)})",
        "forall n N+,A matrix(C,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)*matrix_cofactor(A,n,k,row)})",
        "forall n N+,A matrix(C,n,n),col closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(k,col)*matrix_cofactor(A,n,col,k)})",
        "forall n N+,A matrix(C,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)+matrix_cofactor(A,n,row,k)})",
        "forall n N+,A,B matrix(C,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {B(row,k)*matrix_cofactor(A,n,row,k)})",
        "forall n N+,A matrix(C,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)*matrix_cofactor(A,n,row,row)})",
        "forall A matrix(C,0,0):\n    det(A,0)=finite_set_sum(closed_range(1,0),fn(k closed_range(1,0)) C {A(0,k)*matrix_cofactor(A,0,0,k)})",
        "forall n N+,A matrix(C,n,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(0,k)*matrix_cofactor(A,n,0,k)})",
    ];
    for source in cases {
        let mut rt = runtime();
        check(&mut rt, "have retained R=3", true);
        let before = rt.top_exec_env().facts.facts_by_id.len();
        check(&mut rt, source, false);
        assert_eq!(before, rt.top_exec_env().facts.facts_by_id.len());
        check(&mut rt, "retained+1=4", true);
    }
}

#[test]
fn native_matrix_determinant_formulas_respect_inherited_ceiling() {
    let mut rt = runtime();
    check(
        &mut rt,
        "have n N+\nhave A matrix(C,n,n)=zero_matrix(n,n)\nhave row closed_range(1,n)=1",
        true,
    );
    let tokens=crate::tokenize::Tokenizer::new().tokenize("det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)*matrix_cofactor(A,n,row,k)})",rt.current_file.clone()).unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!()
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
}

#[test]
fn native_matrix_determinant_formulas_all_languages_retain_rule_identity() {
    let source =
        include_str!("../../../../examples/test_objs/native_matrix_determinant_formulas.lit");
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
        let json = check(&mut rt, source, true);
        for rule in [
            "DetLaplaceRow",
            "DetLaplaceColumn",
            "DetUpperTriangular",
            "DetLowerTriangular",
        ] {
            assert!(
                json.contains(&format!("NativeMatrix{rule}")),
                "{language:?}: {rule}"
            );
        }
    }
}

// A true constructor theorem still needs its quantified guard at this ceiling.
#[test]
fn native_matrix_determinant_formulas_constructor_guard_stays_explicit() {
    let mut rt = runtime();
    check(&mut rt,"forall n N:\n    det(zero_matrix(n,n),n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C {(zero_matrix(n,n))(k,k)})",false);
    check(&mut rt, "have retained R=3", true);
}

#[test]
fn native_matrix_determinant_formulas_real_carrier_needs_shared_membership_bridge() {
    let source="forall n N+,A matrix(R,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)*matrix_cofactor(A,n,row,k)})";
    check(&mut runtime(), source, false);
}
