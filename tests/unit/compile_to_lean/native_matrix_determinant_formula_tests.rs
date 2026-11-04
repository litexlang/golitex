use crate::execute::execute_fact_stmt::verify_atomic_fact::search_native_matrix_property::{
    MatrixPropertyApplicationProof, NativeMatrixPropertyProof,
};
use crate::prelude::*;

#[test]
fn native_matrix_determinant_formulas_compile_forward_reverse_and_boundaries() {
    for source in [
        include_str!("../../../examples/test_objs/native_matrix_determinant_formulas.lit"),
        include_str!(
            "../../../lean/examples/native_matrix_determinant_formulas_reverse/statement.lit"
        ),
        include_str!("../../../lean/examples/native_matrix_determinant_boundaries/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler
            .compile_run(&run, "native_determinant_formulas")
            .unwrap();
        assert_eq!(
            out,
            compiler
                .compile_run(&run, "native_determinant_formulas")
                .unwrap()
        );
        for name in [
            "matrixDeterminantUpperTriangularFormula",
            "matrixDeterminantLowerTriangularFormula",
            "matrixDeterminantLaplaceRowFormula",
            "matrixDeterminantLaplaceColumnFormula",
        ] {
            assert!(out.contains(name), "{name}");
        }
    }
}

fn application(statement: &mut ExecStmtResult) -> &mut MatrixPropertyApplicationProof {
    let all = super::forall_proof_mut(statement);
    let selected =
        &mut super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result).searched_proof;
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::NativeMatrixProperty(p),
    ) = selected
    else {
        panic!("native determinant formula")
    };
    match p {
        NativeMatrixPropertyProof::DetLaplaceRow(p) => &mut p.application,
        NativeMatrixPropertyProof::DetLaplaceColumn(p) => &mut p.application,
        NativeMatrixPropertyProof::DetUpperTriangular(p) => &mut p.application,
        NativeMatrixPropertyProof::DetLowerTriangular(p) => &mut p.application,
        _ => panic!("wrong selected formula"),
    }
}

#[test]
fn native_matrix_determinant_formulas_reject_corrupted_replay() {
    let source="forall n N+,A matrix(C,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)*matrix_cofactor(A,n,row,k)})";
    for change in [
        "count",
        "order",
        "arguments",
        "schema",
        "conclusion",
        "matches",
        "orientation",
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = application(&mut run.statement_results[0]);
        match change {
            "count" => {
                p.requirement_proofs.pop();
            }
            "order" => p.requirement_proofs.swap(0, 2),
            "arguments" => p.arguments.swap(1, 2),
            "schema" => p.schema = p.requirements[0].clone(),
            "conclusion" => {
                let AtomicFact::EqualFact(e) = &mut p.conclusion else {
                    panic!()
                };
                e.right = e.left.clone();
            }
            "matches" => {
                p.matching.comparisons.pop();
            }
            "orientation" => p.matching.reversed = true,
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn native_matrix_determinant_formula_validators_keep_exact_guards_and_callbacks() {
    let triangular="forall n N,A matrix(C,n,n):\n    forall r,c closed_range(1,n):\n        c<r\n        =>:\n            A(r,c)=0\n    =>:\n        det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C {A(k,k)})";
    let (mut run, _) = super::execute(triangular);
    let p = application(&mut run.statement_results[0]);
    let AtomicFact::EqualFact(goal) = &p.conclusion else {
        panic!()
    };
    use super::super::compile_builtin_triangular_determinant::validate_triangular_determinant_law;
    validate_triangular_determinant_law(true, &p.arguments, &p.requirements, goal).unwrap();
    assert!(
        validate_triangular_determinant_law(false, &p.arguments, &p.requirements, goal).is_err()
    );
    let mut requirements = p.requirements.clone();
    let Fact::ForallFact(all) = &mut requirements[3] else {
        panic!()
    };
    all.dom_facts.clear();
    assert!(validate_triangular_determinant_law(true, &p.arguments, &requirements, goal).is_err());
    let mut wrong_goal = goal.clone();
    wrong_goal.right = wrong_goal.left.clone();
    assert!(
        validate_triangular_determinant_law(true, &p.arguments, &p.requirements, &wrong_goal)
            .is_err()
    );
    let source="forall n N+,A matrix(C,n,n),row closed_range(1,n):\n    det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C {A(row,k)*matrix_cofactor(A,n,row,k)})";
    let (mut run, _) = super::execute(source);
    let p = application(&mut run.statement_results[0]);
    let AtomicFact::EqualFact(goal) = &p.conclusion else {
        panic!()
    };
    use super::super::compile_builtin_laplace_determinant::validate_laplace_determinant_law;
    validate_laplace_determinant_law(true, &p.arguments, &p.requirements, goal).unwrap();
    assert!(validate_laplace_determinant_law(false, &p.arguments, &p.requirements, goal).is_err());
    assert!(
        validate_laplace_determinant_law(true, &p.arguments, &p.requirements[..4], goal).is_err()
    );
    let mut wrong = goal.clone();
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &mut wrong.right else {
        panic!()
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_mut() else {
        panic!()
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(term)) = f.equal_to.as_mut() else {
        panic!()
    };
    term.left = term.right.clone();
    assert!(validate_laplace_determinant_law(true, &p.arguments, &p.requirements, &wrong).is_err());
}
