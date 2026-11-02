use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const ID: &str = include_str!("../../../lean/examples/native_matrix_apply_identity/statement.lit");
const COMPOSE: &str =
    include_str!("../../../lean/examples/native_matrix_apply_compose/statement.lit");
const REVERSE: &str =
    include_str!("../../../lean/examples/native_matrix_apply_reverse/statement.lit");
const ZERO: &str =
    include_str!("../../../lean/examples/native_matrix_apply_zero_dimensions/statement.lit");
const REAL: &str = include_str!("../../../lean/examples/native_matrix_apply_real/statement.lit");
const TRANSPORT: &str =
    include_str!("../../../lean/examples/native_matrix_apply_transport/statement.lit");
const EXPLICIT_ID: &str =
    include_str!("../../../lean/examples/matrix_apply_identity/statement.lit");
const EXPLICIT_COMPOSE: &str =
    include_str!("../../../lean/examples/matrix_apply_compose/statement.lit");

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("actual selected action law")
    };
    match law {
        NativeMatrixLawProof::ApplyIdentity(p) => &mut p.application,
        NativeMatrixLawProof::ApplyCompose(p) => &mut p.application,
        _ => panic!("actual identity/compose variant"),
    }
}
fn named_body(statement: &mut ExecStmtResult) -> &mut ExecDefThmForallProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("actual named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall body")
    };
    body
}
fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut named_body(statement).proof_steps[0]
    else {
        panic!("actual release")
    };
    p
}

#[test]
fn native_matrix_apply_replays_actual_identity_compose_reverse_zero_and_real_profiles() {
    for source in [ID, COMPOSE, REVERSE, ZERO] {
        let (mut run, compiler) = super::execute(source);
        for statement in &mut run.statement_results {
            let p = selected(statement, 0);
            assert_eq!(
                p.requirements.len(),
                if p.arguments.len() == 2 { 2 } else { 8 }
            );
            assert_eq!(p.requirement_proofs.len(), p.requirements.len());
            assert_eq!(
                matches!(p.orientation, MatrixLawOrientation::Reverse),
                source == REVERSE
            );
        }
        super::compile_run(&run, &compiler, "matrix_action").unwrap();
    }
    let (mut run, compiler) = super::execute(REAL);
    selected(&mut run.statement_results[0], 3);
    super::compile_run(&run, &compiler, "real_matrix_action").unwrap();
}

#[test]
fn native_matrix_apply_preserves_two_or_eight_original_ordered_requirements_and_domains() {
    for source in [ID, COMPOSE] {
        for change in ["count", "extra", "order", "id", "carrier", "vector_domain"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "count" => {
                    p.requirement_proofs.pop();
                }
                "extra" => p.requirements.push(p.requirements[0].clone()),
                "order" => p.requirement_proofs.swap(0, 1),
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.requirements[if source == ID { 0 } else { 6 }]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "carrier" | "vector_domain" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        p.requirements.last_mut().unwrap()
                    else {
                        panic!()
                    };
                    let Obj::SetFormer(SetFormer::FiniteSeqSet(v)) = &mut f.set else {
                        panic!("original finite vector carrier")
                    };
                    if change == "carrier" {
                        v.set = Box::new(Obj::StandardSet(StandardSet::R));
                    } else {
                        v.n = Box::new(super::number_object("7"));
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_apply_preserves_arguments_complete_nested_dimensions_and_orientation() {
    for source in [ID, COMPOSE] {
        for change in [
            "argument",
            "conclusion",
            "rows",
            "cols",
            "orientation",
            "nested",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "conclusion" => p.conclusion.right = super::number_object("7"),
                "rows" | "cols" => {
                    let Obj::MatrixOperator(MatrixOperator::Apply(a)) = &mut p.conclusion.left
                    else {
                        panic!()
                    };
                    if change == "rows" {
                        a.rows = Box::new(super::number_object("7"));
                    } else {
                        a.cols = Box::new(super::number_object("7"));
                    }
                }
                "orientation" => p.orientation = MatrixLawOrientation::Reverse,
                "nested" => {
                    let Obj::MatrixOperator(MatrixOperator::Apply(a)) = &mut p.conclusion.left
                    else {
                        panic!()
                    };
                    match a.matrix.as_mut() {
                        Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i)) => {
                            i.order = Box::new(super::number_object("7"))
                        }
                        Obj::MatrixOperator(MatrixOperator::Multiply(m)) => {
                            m.inner = Box::new(super::number_object("7"))
                        }
                        _ => panic!("actual nested matrix"),
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
    let (mut run, compiler) = super::execute(COMPOSE);
    let p = selected(&mut run.statement_results[0], 0);
    let Obj::MatrixOperator(MatrixOperator::Apply(outer)) = &mut p.conclusion.right else {
        panic!()
    };
    let Obj::MatrixOperator(MatrixOperator::Apply(inner)) = outer.vector.as_mut() else {
        panic!()
    };
    inner.rows = Box::new(super::number_object("7"));
    assert!(super::compile_run(&run, &compiler, "nested_action_domain").is_err());
}

#[test]
fn explicit_matrix_apply_replays_original_stages_and_rectangular_anonymous_vector_call() {
    for source in [EXPLICIT_ID, EXPLICIT_COMPOSE] {
        let (mut run, compiler) = super::execute(source);
        let p = release(&mut run.statement_results[0]);
        assert_eq!(
            p.dom_proofs.len(),
            if source == EXPLICIT_ID { 2 } else { 8 }
        );
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 1);
        assert_eq!(p.conclusions_wd.len(), 1);
        super::compile_run(&run, &compiler, "explicit_matrix_action").unwrap();
    }
}

#[test]
fn explicit_matrix_apply_requires_original_proof_store_wd_ids_and_selected_theorem() {
    for source in [EXPLICIT_ID, EXPLICIT_COMPOSE] {
        for change in [
            "stores",
            "proof_order",
            "clause",
            "wd",
            "id",
            "argument",
            "theorem",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = release(&mut run.statement_results[0]);
            match change {
                "stores" => {
                    p.dom_stores.pop();
                }
                "proof_order" => p.dom_proofs.swap(0, 1),
                "clause" => {
                    p.builtin.as_mut().unwrap().conclusions.pop();
                }
                "wd" => {
                    p.conclusions_wd.pop();
                }
                "id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.builtin.as_mut().unwrap().requirements
                            [if source == EXPLICIT_ID { 0 } else { 6 }]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                "theorem" => {
                    p.builtin.as_mut().unwrap().theorem =
                        crate::builtin_theorem::BuiltinTheoremId::MatrixMulIdentity
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_apply_requires_original_outer_and_nested_constructor_evidence() {
    for source in [ID, COMPOSE] {
        for change in ["child", "premise", "nested"] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::MatrixOperator(
                        MatrixOperatorObjWellDefinedProofByDef::Apply(p),
                    ),
                ..
            } = wd.left.as_detailed_mut().unwrap()
            else {
                panic!("original matrix action WD")
            };
            match change {
                "child" => {
                    p.child_obj_well_defined.pop();
                }
                "premise" => {
                    p.requirement_fact_verified.pop();
                }
                "nested" => {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof: ObjWellDefinedProofByDef::MatrixOperator(nested),
                        ..
                    } = p.child_obj_well_defined[0].as_detailed_mut().unwrap()
                    else {
                        panic!("original nested matrix WD")
                    };
                    match nested {
                        MatrixOperatorObjWellDefinedProofByDef::IdentityMatrix(m) => {
                            m.requirement_fact_verified.pop();
                        }
                        MatrixOperatorObjWellDefinedProofByDef::Multiply(m) => {
                            m.child_obj_well_defined.pop();
                        }
                        _ => panic!("original identity/product evidence"),
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_apply_endpoint_transport_retains_original_assumption_citation() {
    let (mut run, compiler) = super::execute(TRANSPORT);
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_ref()
    else {
        panic!("actual endpoint assumption path")
    };
    assert!(!path.path.is_empty());
    assert_eq!(path.path[0].0.ir(), p.conclusion.right.ir());
    super::compile_run(&run, &compiler, "matrix_action_endpoint").unwrap();
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_mut()
    else {
        panic!()
    };
    path.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_action_endpoint").is_err());
}

#[test]
fn native_matrix_apply_does_not_skip_any_executed_real_matrix_or_vector_carrier() {
    for index in 0..3 {
        let (mut run, compiler) = super::execute(REAL);
        super::compile_run(&run, &compiler, "original_action_intermediates").unwrap();
        super::forall_proof_mut(&mut run.statement_results[0])
            .proved_then_facts
            .remove(index);
        assert!(super::compile_run(&run, &compiler, "skipped_action_intermediate").is_err());
    }
}
