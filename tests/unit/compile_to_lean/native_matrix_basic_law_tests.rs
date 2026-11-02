use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{
    MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof,
};
use crate::prelude::*;

const POWER_ZERO: &str =
    include_str!("../../../lean/examples/native_matrix_power_zero/statement.lit");
const POWER_NEXT: &str =
    include_str!("../../../lean/examples/native_matrix_power_successor/statement.lit");
const RANK_ZERO: &str =
    include_str!("../../../lean/examples/native_matrix_rank_zero/statement.lit");
const RANK_ID: &str =
    include_str!("../../../lean/examples/native_matrix_rank_identity/statement.lit");

fn selected(statement: &mut ExecStmtResult) -> &mut MatrixLawApplicationProof {
    let all = super::forall_proof_mut(statement);
    let proof = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut proof.searched_proof
    else {
        panic!("actual native matrix law")
    };
    match law {
        NativeMatrixLawProof::PowerZero(p) => &mut p.application,
        NativeMatrixLawProof::PowerSuccessor(p) => &mut p.application,
        NativeMatrixLawProof::RankZero(p) => &mut p.application,
        NativeMatrixLawProof::RankIdentity(p) => &mut p.application,
        _ => panic!("actual power/rank law"),
    }
}

#[test]
fn native_matrix_powers_and_ranks_replay_actual_selected_laws() {
    for source in [POWER_ZERO, POWER_NEXT, RANK_ZERO, RANK_ID] {
        let (mut run, compiler) = super::execute(source);
        let p = selected(&mut run.statement_results[0]);
        if source == RANK_ID {
            assert!(matches!(p.orientation, MatrixLawOrientation::Reverse));
        }
        super::compile_run(&run, &compiler, "native_power_rank").unwrap();
    }
}

#[test]
fn native_matrix_power_rank_requirements_keep_counts_ids_and_order() {
    for source in [POWER_NEXT, RANK_ZERO] {
        for change in ["missing", "extra", "order", "id", "subject"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0]);
            match change {
                "missing" => {
                    p.requirement_proofs.pop();
                }
                "extra" => p.requirements.push(p.requirements[0].clone()),
                "order" => p.requirement_proofs.swap(0, 1),
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[0] else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "subject" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[0] else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::Z);
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_power_rank_reject_changed_arguments_conclusions_and_orientation() {
    for source in [POWER_ZERO, POWER_NEXT, RANK_ZERO, RANK_ID] {
        for change in ["argument", "conclusion", "orientation"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0]);
            match change {
                "argument" => {
                    p.arguments[0] = Obj::Literal(Literal::Number(Number::new("7".into())))
                }
                "conclusion" => {
                    p.conclusion.right = Obj::Literal(Literal::Number(Number::new("7".into())))
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
fn native_matrix_successor_cannot_borrow_missing_or_future_exponent_membership() {
    for future in [false, true] {
        let source = format!("{POWER_NEXT}    replay_exponent $in N\n");
        let (mut run, compiler) = super::execute(&source);
        super::compile_run(&run, &compiler, "original_power_exponent_guard").unwrap();
        let unavailable = if future {
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            super::atomic_proof_mut(&mut all.proved_then_facts[1].verify_result)
                .fact
                .fact_id()
        } else {
            FactId::new(u64::MAX)
        };
        let p = selected(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut p.requirement_proofs[3]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            &mut atom.searched_proof
        else {
            panic!("original exponent membership citation")
        };
        citation.cite_fact_id = unavailable;
        assert!(super::compile_run(&run, &compiler, "unavailable_exponent_guard").is_err());
    }
}

#[test]
fn native_matrix_power_rank_keep_invalid_exponent_and_dimension_controls() {
    for source in [
        "matrix_power(identity_matrix(2),2,-1)=identity_matrix(2)",
        "matrix_rank(zero_matrix(2,3),3,2)=0",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}
