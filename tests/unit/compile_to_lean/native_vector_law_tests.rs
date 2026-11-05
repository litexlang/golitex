use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{
    MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof,
};
use crate::prelude::*;
use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::execute::ExecReleaseAndExpandStmtResult;

const SYMMETRY: &str = r#"forall replay_dimension N, replay_left, replay_right cart_n(C, replay_dimension):
    conj(inner_product(replay_right, replay_left, replay_dimension)) = inner_product(replay_left, replay_right, replay_dimension)
"#;
const NORM: &str = r#"forall replay_dimension N, replay_vector cart_n(C, replay_dimension):
    euclidean_norm(replay_vector, replay_dimension)^2 = inner_product(replay_vector, replay_vector, replay_dimension)
"#;
const REAL: &str = r#"forall replay_dimension N, replay_vector cart_n(R, replay_dimension):
    replay_vector $in cart_n(C, replay_dimension)
    euclidean_norm(replay_vector, replay_dimension)^2 = inner_product(replay_vector, replay_vector, replay_dimension)
"#;
const EXPLICIT_S: &str = r#"thm replay_inner_symmetry:
    ? forall replay_dimension N, replay_left, replay_right cart_n(C, replay_dimension):
        inner_product(replay_left, replay_right, replay_dimension) = conj(inner_product(replay_right, replay_left, replay_dimension))
    release thm inner_product_conjugate_symmetry(replay_left, replay_right, replay_dimension)
"#;
const EXPLICIT_N: &str = r#"thm replay_euclidean_square:
    ? forall replay_dimension N, replay_vector cart_n(C, replay_dimension):
        euclidean_norm(replay_vector, replay_dimension)^2 = inner_product(replay_vector, replay_vector, replay_dimension)
    release thm euclidean_norm_square(replay_vector, replay_dimension)
"#;

fn selected(statement: &mut ExecStmtResult) -> &mut MatrixLawApplicationProof {
    selected_at(statement, 0)
}

fn selected_at(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let all = super::forall_proof_mut(statement);
    let p = super::equality_proof_mut(&mut all.proved_then_facts[index].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut p.searched_proof
    else {
        panic!("actual native vector law")
    };
    match law {
        NativeMatrixLawProof::InnerConjugateSymmetry(p) => &mut p.application,
        NativeMatrixLawProof::EuclideanNormSquare(p) => &mut p.application,
        _ => panic!("actual symmetry or norm-square law"),
    }
}

#[test]
fn native_vector_laws_replay_reverse_symmetry_and_selected_inner_conclusion() {
    for source in [SYMMETRY, NORM, REAL] {
        let (mut run, compiler) = super::execute(source);
        let p = selected_at(&mut run.statement_results[0], usize::from(source == REAL));
        if source == SYMMETRY {
            assert!(matches!(p.orientation, MatrixLawOrientation::Reverse));
        } else {
            assert!(matches!(
                p.conclusion.right,
                Obj::MatrixOperator(MatrixOperator::InnerProduct(_))
            ));
        }
        super::compile_run(&run, &compiler, "native_vector_law").unwrap();
    }
    for source in [EXPLICIT_S, EXPLICIT_N] {
        let (run, compiler) = super::execute(source);
        super::compile_run(&run, &compiler, "explicit_vector_law").unwrap();
    }
}

#[test]
fn native_vector_laws_reject_changed_counts_ids_order_and_source_carriers() {
    for source in [SYMMETRY, NORM] {
        for change in [
            "count",
            "order",
            "id",
            "carrier",
            "arguments",
            "orientation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0]);
            match change {
                "count" => {
                    p.requirement_proofs.pop();
                }
                "order" => p.requirement_proofs.swap(0, 1),
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[0] else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "carrier" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[1] else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
                "arguments" => p.arguments.swap(0, 1),
                "orientation" => {
                    p.orientation = match p.orientation {
                        MatrixLawOrientation::Forward => MatrixLawOrientation::Reverse,
                        MatrixLawOrientation::Reverse => MatrixLawOrientation::Forward,
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_euclidean_square_rejects_a_changed_exponent_or_self_inner_vector() {
    for change in ["exponent", "vector"] {
        let (mut run, compiler) = super::execute(NORM);
        let p = selected(&mut run.statement_results[0]);
        if change == "exponent" {
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(square)) = &mut p.conclusion.left
            else {
                panic!()
            };
            square.exponent = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
        } else {
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = &mut p.conclusion.right
            else {
                panic!()
            };
            inner.right = Box::new(Obj::StandardSet(StandardSet::C));
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn explicit_inner_symmetry_keeps_its_original_stores_and_conclusion_formation() {
    for change in ["stores", "order", "conclusion_wd"] {
        let (mut run, compiler) = super::execute(EXPLICIT_S);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!("actual named proof")
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(p),
        )) = &mut body.proof_steps[0]
        else {
            panic!("actual theorem release")
        };
        match change {
            "stores" => {
                p.dom_stores.pop();
            }
            "order" => p.dom_stores.swap(0, 1),
            "conclusion_wd" => p.conclusions_wd.clear(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}
