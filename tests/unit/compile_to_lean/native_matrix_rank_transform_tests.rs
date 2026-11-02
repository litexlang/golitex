use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{
    MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof,
};
use crate::prelude::*;

const TRANSPOSE: &str =
    include_str!("../../../lean/examples/native_matrix_rank_transpose/statement.lit");
const ADJOINT: &str =
    include_str!("../../../lean/examples/native_matrix_rank_adjoint/statement.lit");
const EXPLICIT_T: &str = include_str!("../../../lean/examples/matrix_rank_transpose/statement.lit");
const EXPLICIT_A: &str = include_str!("../../../lean/examples/matrix_rank_adjoint/statement.lit");

fn selected(statement: &mut ExecStmtResult) -> &mut MatrixLawApplicationProof {
    let all = super::forall_proof_mut(statement);
    let p = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut p.searched_proof
    else {
        panic!("actual selected native matrix law")
    };
    match law {
        NativeMatrixLawProof::MatrixRankTranspose(p) => &mut p.application,
        NativeMatrixLawProof::MatrixRankAdjoint(p) => &mut p.application,
        _ => panic!("actual rank transform law"),
    }
}

#[test]
fn native_rank_transform_replays_rectangular_carriers_and_reverse_orientation() {
    for source in [TRANSPOSE, ADJOINT] {
        let (mut run, compiler) = super::execute(source);
        if source == ADJOINT {
            assert!(matches!(
                selected(&mut run.statement_results[0]).orientation,
                MatrixLawOrientation::Reverse
            ));
        } else {
            selected(&mut run.statement_results[0]);
        }
        super::compile_run(&run, &compiler, "rank_transform").unwrap();
    }
    for source in [EXPLICIT_T, EXPLICIT_A] {
        let (run, compiler) = super::execute(source);
        super::compile_run(&run, &compiler, "explicit_rank_transform").unwrap();
    }
}

#[test]
fn native_rank_transform_rejects_original_dimension_premise_and_match_corruption() {
    for source in [TRANSPOSE, ADJOINT] {
        for change in [
            "dimensions",
            "argument",
            "count",
            "order",
            "id",
            "orientation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0]);
            match change {
                "dimensions" => {
                    let Obj::MatrixOperator(MatrixOperator::Rank(rank)) = &mut p.conclusion.left
                    else {
                        panic!()
                    };
                    std::mem::swap(&mut rank.rows, &mut rank.cols);
                }
                "argument" => p.arguments.swap(1, 2),
                "count" => {
                    p.requirement_proofs.pop();
                }
                "order" => p.requirement_proofs.swap(0, 1),
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2] else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
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
fn explicit_rank_transform_rejects_missing_stores_and_wrong_conclusion_carriers() {
    for source in [EXPLICIT_T, EXPLICIT_A] {
        for change in ["stores", "dimensions"] {
            let (mut run, compiler) = super::execute(source);
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
                panic!("actual explicit theorem")
            };
            if change == "stores" {
                p.dom_stores.pop();
            } else {
                let Fact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                let Obj::MatrixOperator(MatrixOperator::Rank(rank)) = &mut eq.left else {
                    panic!()
                };
                std::mem::swap(&mut rank.rows, &mut rank.cols);
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}
