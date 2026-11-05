use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{
    MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof,
};
use crate::prelude::*;

const IDENTITY: &str = r#"det(identity_matrix(2), 2) = 1
forall replay_order N:
    1 = det(identity_matrix(replay_order), replay_order)
"#;
const TRANSPOSE: &str = r#"forall replay_order N, replay_matrix matrix(C, replay_order, replay_order):
    det(transpose(replay_matrix, replay_order, replay_order), replay_order) = det(replay_matrix, replay_order)
"#;
const ADJOINT: &str = r#"forall replay_order N, replay_matrix matrix(C, replay_order, replay_order):
    det(conjugate_transpose(replay_matrix, replay_order, replay_order), replay_order) = conj(det(replay_matrix, replay_order))
"#;
const TRANSPORT: &str = r#"have replay_one R = 1
forall replay_order N:
    det(identity_matrix(replay_order), replay_order) = replay_one
"#;

fn selected(statement: &mut ExecStmtResult, universal: bool) -> &mut MatrixLawApplicationProof {
    let result = if universal {
        &mut super::forall_proof_mut(statement).proved_then_facts[0].verify_result
    } else {
        &mut super::fact_statement_mut(statement).verify_result
    };
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut super::equality_proof_mut(result).searched_proof
    else {
        panic!("actual native matrix law")
    };
    match law {
        NativeMatrixLawProof::DetIdentity(p) => &mut p.application,
        NativeMatrixLawProof::DetTranspose(p) => &mut p.application,
        NativeMatrixLawProof::DetAdjoint(p) => &mut p.application,
        _ => panic!("actual determinant law"),
    }
}

#[test]
fn native_determinants_replay_original_laws_orientations_and_transport() {
    for (source, index, universal) in [
        (IDENTITY, 0, false),
        (IDENTITY, 1, true),
        (TRANSPOSE, 0, true),
        (ADJOINT, 0, true),
        (TRANSPORT, 1, true),
    ] {
        let (mut run, compiler) = super::execute(source);
        let application = selected(&mut run.statement_results[index], universal);
        if source == IDENTITY && universal {
            assert!(matches!(
                application.orientation,
                MatrixLawOrientation::Reverse
            ));
        }
        if source == TRANSPORT {
            assert!(matches!(
                *application.right_equal,
                EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(_)
                )
            ));
        }
        super::compile_run(&run, &compiler, "native_determinant").unwrap();
    }
}

#[test]
fn native_determinants_reject_missing_extra_reordered_and_mismatched_requirements() {
    for change in [
        "missing_proof",
        "missing_fact",
        "extra_fact",
        "order",
        "id",
        "subject",
    ] {
        let (mut run, compiler) = super::execute(TRANSPOSE);
        let application = selected(&mut run.statement_results[0], true);
        match change {
            "missing_proof" => {
                application.requirement_proofs.pop();
            }
            "missing_fact" => {
                application.requirements.pop();
            }
            "extra_fact" => {
                application
                    .requirements
                    .push(application.requirements[0].clone());
            }
            "order" => {
                application.requirement_proofs.swap(0, 1);
            }
            "id" => {
                let Fact::AtomicFact(AtomicFact::InFact(p)) = &mut application.requirements[0]
                else {
                    panic!()
                };
                p.fact_id = FactId::new(u64::MAX);
            }
            "subject" => {
                let Fact::AtomicFact(AtomicFact::InFact(p)) = &mut application.requirements[2]
                else {
                    panic!()
                };
                p.set = Obj::StandardSet(StandardSet::C);
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(&run, &compiler, change, &["MatrixLaw/", "Determinant/"]);
    }
}

#[test]
fn native_determinants_reject_changed_law_arguments_conclusions_and_orientation() {
    for change in ["argument", "conclusion", "orientation"] {
        let (mut run, compiler) = super::execute(IDENTITY);
        let p = selected(&mut run.statement_results[0], false);
        match change {
            "argument" => p.arguments[0] = Obj::Literal(Literal::Number(Number::new("3".into()))),
            "conclusion" => {
                p.conclusion.right = Obj::Literal(Literal::Number(Number::new("2".into())))
            }
            "orientation" => p.orientation = MatrixLawOrientation::Reverse,
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &run,
            &compiler,
            change,
            &["MatrixLaw/", "Determinant/", "SameIr"],
        );
    }
}

#[test]
fn native_determinants_reject_endpoint_proof_from_the_other_side() {
    let (mut donor, _) = super::execute(TRANSPORT);
    let (mut run, compiler) = super::execute(IDENTITY);
    std::mem::swap(
        &mut selected(&mut donor.statement_results[1], true).right_equal,
        &mut selected(&mut run.statement_results[0], false).left_equal,
    );
    assert!(super::compile_run(&run, &compiler, "wrong_matrix_endpoint").is_err());
}

#[test]
fn native_determinants_cannot_borrow_a_future_or_missing_transport_citation() {
    for future in [false, true] {
        let source = format!("{TRANSPORT}1 = replay_one\n");
        let (mut run, compiler) = super::execute(&source);
        let unavailable = if future {
            super::equality_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[2]).verify_result,
            )
            .fact
            .fact_id
        } else {
            FactId::new(u64::MAX)
        };
        let p = selected(&mut run.statement_results[1], true);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = p.right_equal.as_mut()
        else {
            panic!("actual endpoint transport path")
        };
        assert_eq!(path.path.len(), 1);
        path.path[0].2 = unavailable;
        let error =
            super::compile_run(&run, &compiler, "unavailable_matrix_transport").unwrap_err();
        assert_eq!(
            error.route,
            if future {
                "FactId/Producer"
            } else {
                "FactId/Resolution"
            }
        );
    }
}

#[test]
fn native_determinants_keep_false_equality_and_missing_domain_controls() {
    for source in [
        "det(identity_matrix(2),2) = 2\n",
        "forall n N, A set:\n    det(transpose(A,n,n),n)=det(A,n)\n",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}
