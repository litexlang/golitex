use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_matrix_inverse_laws::{validate_matrix_inverse_law, MatrixInverseLaw};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const LEFT: &str = r#"# Original InverseLeft means inverse(A) times A.
forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    =>:
        matrix_mul(matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_A,replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
"#;
const RIGHT: &str = r#"# Original InverseRight means A times inverse(A).
forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    =>:
        matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
"#;
const EXPLICIT: &str = r#"# Preserve the actual guarded combined theorem and both conclusions.
thm replay_matrix_inverse_laws:
    ? forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n):
        det(replay_inverse_A,replay_inverse_n) != 0
        =>:
            matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
            matrix_mul(matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_A,replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
    release thm matrix_inverse_laws(replay_inverse_A,replay_inverse_n)
det(identity_matrix(2),2) = 1
det(identity_matrix(2),2) != 0
release thm replay_matrix_inverse_laws(2,identity_matrix(2))
"#;
const REVERSE: &str = r#"# Reverse both original guarded inverse product clauses.
forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    =>:
        identity_matrix(replay_inverse_n) = matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_n,replay_inverse_n,replay_inverse_n)
forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    =>:
        identity_matrix(replay_inverse_n) = matrix_mul(matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_A,replay_inverse_n,replay_inverse_n,replay_inverse_n)
"#;
const ZERO: &str = r#"# Retain the original determinant guard at natural order zero.
forall replay_inverse_A matrix(C,0,0):
    det(replay_inverse_A,0) != 0
    =>:
        matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,0),0,0,0) = identity_matrix(0)
forall replay_inverse_A matrix(C,0,0):
    det(replay_inverse_A,0) != 0
    =>:
        matrix_mul(matrix_inv(replay_inverse_A,0),replay_inverse_A,0,0,0) = identity_matrix(0)
"#;
const REAL: &str = r#"# Retain the proved complex carrier and original determinant guard.
forall replay_inverse_n N, replay_inverse_A matrix(R,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    =>:
        replay_inverse_A $in matrix(C,replay_inverse_n,replay_inverse_n)
        matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
forall replay_inverse_n N, replay_inverse_A matrix(R,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    =>:
        replay_inverse_A $in matrix(C,replay_inverse_n,replay_inverse_n)
        matrix_mul(matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_A,replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
"#;
const TRANSPORT: &str = r#"# Transport each original identity endpoint using its given equality.
forall replay_inverse_n N, replay_inverse_A, replay_inverse_D matrix(C,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    identity_matrix(replay_inverse_n) = replay_inverse_D
    =>:
        matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_n,replay_inverse_n,replay_inverse_n) = replay_inverse_D
forall replay_inverse_n N, replay_inverse_A, replay_inverse_D matrix(C,replay_inverse_n,replay_inverse_n):
    det(replay_inverse_A,replay_inverse_n) != 0
    identity_matrix(replay_inverse_n) = replay_inverse_D
    =>:
        matrix_mul(matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_A,replay_inverse_n,replay_inverse_n,replay_inverse_n) = replay_inverse_D
"#;
const GUARD_TRANSPORT: &str = r#"# Obtain the exact determinant guard from its original scalar equality.
forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n), replay_inverse_det_value C:
    det(replay_inverse_A,replay_inverse_n) = replay_inverse_det_value
    replay_inverse_det_value != 0
    =>:
        matrix_mul(replay_inverse_A,matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
forall replay_inverse_n N, replay_inverse_A matrix(C,replay_inverse_n,replay_inverse_n), replay_inverse_det_value C:
    det(replay_inverse_A,replay_inverse_n) = replay_inverse_det_value
    replay_inverse_det_value != 0
    =>:
        matrix_mul(matrix_inv(replay_inverse_A,replay_inverse_n),replay_inverse_A,replay_inverse_n,replay_inverse_n,replay_inverse_n) = identity_matrix(replay_inverse_n)
"#;

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("original inverse law")
    };
    match law {
        NativeMatrixLawProof::InverseLeft(p) => &mut p.application,
        NativeMatrixLawProof::InverseRight(p) => &mut p.application,
        _ => panic!("original Left/Right variant"),
    }
}
fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("original named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall body")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original combined invocation")
    };
    p
}

#[test]
fn inverse_replays_distinct_native_clauses_reverse_zero_and_real_profiles() {
    for source in [LEFT, RIGHT, REVERSE, ZERO] {
        let (mut run, compiler) = super::execute(source);
        for statement in &mut run.statement_results {
            let p = selected(statement, 0);
            assert_eq!(p.arguments.len(), 2);
            assert_eq!(p.requirements.len(), 4);
            assert_eq!(p.requirement_proofs.len(), 4);
            assert_eq!(
                matches!(p.orientation, MatrixLawOrientation::Reverse),
                source == REVERSE
            );
        }
        super::compile_run(&run, &compiler, "native_inverse").unwrap();
    }
    let (mut run, compiler) = super::execute(REAL);
    for statement in &mut run.statement_results {
        selected(statement, 1);
    }
    super::compile_run(&run, &compiler, "real_inverse").unwrap();
}

#[test]
fn inverse_requires_original_matrix_premises_ids_carriers_and_domains() {
    for source in [LEFT, RIGHT] {
        for change in [
            "missing",
            "extra",
            "order",
            "duplicate_id",
            "wrong_id",
            "carrier",
            "domain",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "missing" => {
                    p.requirement_proofs.pop();
                }
                "extra" => p.requirements.push(p.requirements[0].clone()),
                "order" => p.requirement_proofs.swap(0, 1),
                "duplicate_id" | "wrong_id" => {
                    let id = if change == "duplicate_id" {
                        p.requirements[0].fact_id()
                    } else {
                        FactId::new(u64::MAX)
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[1] else {
                        panic!()
                    };
                    f.fact_id = id;
                }
                "carrier" | "domain" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2] else {
                        panic!()
                    };
                    let Obj::SetFormer(SetFormer::MatrixSet(m)) = &mut f.set else {
                        panic!()
                    };
                    if change == "carrier" {
                        m.set = Box::new(Obj::StandardSet(StandardSet::R));
                    } else {
                        m.rows = Box::new(super::number_object("7"));
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn inverse_preserves_original_factor_order_square_dimensions_and_identity() {
    for source in [LEFT, RIGHT] {
        for change in [
            "argument",
            "product_dimension",
            "factor_order",
            "inverse_matrix",
            "inverse_order",
            "identity_order",
            "orientation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "product_dimension" | "factor_order" | "inverse_matrix" | "inverse_order" => {
                    let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = &mut p.conclusion.left
                    else {
                        panic!()
                    };
                    match change {
                        "product_dimension" => m.inner = Box::new(super::number_object("7")),
                        "factor_order" => std::mem::swap(&mut m.left, &mut m.right),
                        _ => {
                            let object = if source == LEFT {
                                &mut m.left
                            } else {
                                &mut m.right
                            };
                            let Obj::MatrixOperator(MatrixOperator::Inverse(inv)) = object.as_mut()
                            else {
                                panic!()
                            };
                            if change == "inverse_matrix" {
                                inv.matrix = Box::new(super::number_object("7"));
                            } else {
                                inv.order = Box::new(super::number_object("7"));
                            }
                        }
                    }
                }
                "identity_order" => {
                    let Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i)) =
                        &mut p.conclusion.right
                    else {
                        panic!()
                    };
                    i.order = Box::new(super::number_object("7"));
                }
                "orientation" => p.orientation = MatrixLawOrientation::Reverse,
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn inverse_does_not_exchange_equal_arity_left_and_right_contracts() {
    for (source, wrong) in [
        (LEFT, MatrixInverseLaw::Right),
        (RIGHT, MatrixInverseLaw::Left),
    ] {
        let (mut run, _) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert!(
            validate_matrix_inverse_law(wrong, &p.arguments, &p.requirements, &p.conclusion)
                .is_err()
        );
    }
}

#[test]
fn explicit_inverse_replays_four_stages_both_conclusions_and_guarded_named_call() {
    let (mut run, compiler) = super::execute(EXPLICIT);
    let p = release(&mut run.statement_results[0]);
    assert_eq!(p.dom_proofs.len(), 4);
    assert_eq!(p.dom_stores.len(), 4);
    assert_eq!(p.builtin.as_ref().unwrap().requirements.len(), 4);
    assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 2);
    assert_eq!(p.conclusions_wd.len(), 2);
    assert_eq!(p.stored_wd.len(), 2);
    assert_eq!(p.stored.len(), 2);
    super::compile_run(&run, &compiler, "combined_inverse").unwrap();
}

#[test]
fn explicit_inverse_requires_original_order_stores_wd_ids_arguments_and_theorem() {
    for change in [
        "proof",
        "proof_order",
        "store",
        "first_wd",
        "second_wd",
        "clause",
        "clause_order",
        "id",
        "argument",
        "theorem",
    ] {
        let (mut run, compiler) = super::execute(EXPLICIT);
        let p = release(&mut run.statement_results[0]);
        match change {
            "proof" => {
                p.dom_proofs.pop();
            }
            "proof_order" => p.dom_proofs.swap(0, 1),
            "store" => {
                p.dom_stores.pop();
            }
            "first_wd" => {
                p.conclusions_wd.remove(0);
            }
            "second_wd" => {
                p.conclusions_wd.pop();
            }
            "clause" => {
                p.builtin.as_mut().unwrap().conclusions.pop();
            }
            "clause_order" => p.builtin.as_mut().unwrap().conclusions.swap(0, 1),
            "id" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[1]
                else {
                    panic!()
                };
                f.fact_id = FactId::new(u64::MAX);
            }
            "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "theorem" => {
                p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::MatrixAdjugateIdentity
            }
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn explicit_inverse_retains_each_original_conclusion_publication_and_formation() {
    for change in [
        "first_store",
        "second_store",
        "store_order",
        "first_formation",
        "second_formation",
        "formation_order",
    ] {
        let (mut run, compiler) = super::execute(EXPLICIT);
        let p = release(&mut run.statement_results[0]);
        match change {
            "first_store" => {
                p.stored.remove(0);
            }
            "second_store" => {
                p.stored.pop();
            }
            "store_order" => p.stored.swap(0, 1),
            "first_formation" => {
                p.stored_wd.remove(0);
            }
            "second_formation" => {
                p.stored_wd.pop();
            }
            "formation_order" => p.stored_wd.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn inverse_requires_parent_product_nested_inverse_and_identity_wd() {
    for source in [LEFT, RIGHT] {
        for change in [
            "outer_child",
            "outer_premise",
            "adj_child",
            "adj_premise",
            "identity_child",
            "identity_premise",
        ] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            if matches!(change, "identity_child" | "identity_premise") {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::MatrixOperator(
                            MatrixOperatorObjWellDefinedProofByDef::IdentityMatrix(identity),
                        ),
                    ..
                } = eq
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .right
                    .as_detailed_mut()
                    .unwrap()
                else {
                    panic!("original identity WD")
                };
                if change == "identity_child" {
                    identity.child_obj_well_defined.pop();
                } else {
                    identity.requirement_fact_verified.pop();
                }
                assert!(super::compile_run(&run, &compiler, change).is_err());
                continue;
            }
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::MatrixOperator(
                        MatrixOperatorObjWellDefinedProofByDef::Multiply(m),
                    ),
                ..
            } = eq
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .left
                .as_detailed_mut()
                .unwrap()
            else {
                panic!("original product WD")
            };
            match change {
                "outer_child" => {
                    m.child_obj_well_defined.pop();
                }
                "outer_premise" => {
                    m.requirement_fact_verified.pop();
                }
                _ => {
                    let index = if source == LEFT { 0 } else { 1 };
                    let DetailedObjWellDefinedProof::ByDef {
                        proof:
                            ObjWellDefinedProofByDef::MatrixOperator(
                                MatrixOperatorObjWellDefinedProofByDef::Inverse(adj),
                            ),
                        ..
                    } = m.child_obj_well_defined[index].as_detailed_mut().unwrap()
                    else {
                        panic!("nested original inverse WD")
                    };
                    if change == "adj_child" {
                        adj.child_obj_well_defined.pop();
                    } else {
                        adj.requirement_fact_verified.pop();
                    }
                }
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn inverse_endpoint_transport_retains_both_original_assumption_citations() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(TRANSPORT);
        let p = selected(&mut run.statement_results[index], 0);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = p.right_equal.as_ref()
        else {
            panic!("original endpoint path")
        };
        assert!(!path.path.is_empty());
        assert_eq!(path.path[0].0.ir(), p.conclusion.right.ir());
        super::compile_run(&run, &compiler, "original_inverse_endpoint").unwrap();
        let p = selected(&mut run.statement_results[index], 0);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = p.right_equal.as_mut()
        else {
            panic!()
        };
        path.path[0].2 = FactId::new(u64::MAX);
        assert!(super::compile_run(&run, &compiler, "missing_inverse_endpoint").is_err());
    }
}

#[test]
fn inverse_does_not_skip_executed_real_carrier_intermediates() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(REAL);
        super::compile_run(&run, &compiler, "original_inverse_carriers").unwrap();
        super::forall_proof_mut(&mut run.statement_results[index])
            .proved_then_facts
            .remove(0);
        assert!(super::compile_run(&run, &compiler, "skipped_inverse_carrier").is_err());
    }
}

#[test]
fn inverse_requires_its_original_fourth_nonzero_guard_even_with_complete_parent_wd() {
    for source in [LEFT, RIGHT] {
        for change in [
            "guard_missing",
            "guard_id",
            "guard_matrix",
            "guard_order",
            "guard_zero",
            "guard_citation",
        ] {
            let (mut run, compiler) = super::execute(source);
            super::compile_run(&run, &compiler, "original_inverse_guard").unwrap();
            let p = selected(&mut run.statement_results[0], 0);
            assert_eq!(p.requirements.len(), 4);
            assert!(matches!(
                &p.requirements[3],
                Fact::AtomicFact(AtomicFact::NotEqualFact(_))
            ));
            match change {
                "guard_missing" => {
                    p.requirement_proofs.pop();
                }
                "guard_citation" => {
                    let atom = super::atomic_proof_mut(&mut p.requirement_proofs[3]);
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut atom.searched_proof
                    else {
                        panic!("original nonzero assumption citation")
                    };
                    cite.cite_fact_id = FactId::new(u64::MAX);
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) =
                        &mut p.requirements[3]
                    else {
                        panic!("original fourth guard")
                    };
                    if change == "guard_id" {
                        nonzero.fact_id = FactId::new(u64::MAX);
                    } else if change == "guard_zero" {
                        nonzero.right = super::number_object("1");
                    } else {
                        let Obj::MatrixOperator(MatrixOperator::Determinant(det)) =
                            &mut nonzero.left
                        else {
                            panic!("original guarded determinant")
                        };
                        if change == "guard_matrix" {
                            det.matrix = Box::new(super::number_object("7"));
                        } else {
                            det.order = Box::new(super::number_object("7"));
                        }
                    }
                }
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn inverse_guard_transport_requires_original_scalar_nonzero_and_equality_citations() {
    for statement in 0..2 {
        for change in ["nonzero", "equality"] {
            let (mut run, compiler) = super::execute(GUARD_TRANSPORT);
            super::compile_run(&run, &compiler, "original_transported_inverse_guard").unwrap();
            let p = selected(&mut run.statement_results[statement], 0);
            let atom = super::atomic_proof_mut(&mut p.requirement_proofs[3]);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut atom.searched_proof
            else {
                panic!("original transported scalar nonzero citation")
            };
            if change == "nonzero" {
                cite.cite_fact_id = FactId::new(u64::MAX);
            } else {
                let path = cite
                    .why_parameters_of_known_fact_are_equal_to_givens
                    .iter_mut()
                    .find_map(|proof| match proof {
                        EqualFactSearchedProof::ByEquivalenceClass(
                            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                        ) => Some(path),
                        _ => None,
                    })
                    .expect("original determinant-to-scalar equality path");
                assert!(!path.path.is_empty());
                path.path[0].2 = FactId::new(u64::MAX);
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}
