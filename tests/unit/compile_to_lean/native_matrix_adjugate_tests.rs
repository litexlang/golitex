use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_matrix_adjugate_laws::{validate_matrix_adjugate_law, MatrixAdjugateLaw};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const LEFT: &str = include_str!("../../../lean/examples/native_matrix_adjugate_left/statement.lit");
const RIGHT: &str =
    include_str!("../../../lean/examples/native_matrix_adjugate_right/statement.lit");
const EXPLICIT: &str =
    include_str!("../../../lean/examples/matrix_adjugate_identity/statement.lit");
const REVERSE: &str =
    include_str!("../../../lean/examples/native_matrix_adjugate_reverse/statement.lit");
const ZERO: &str = include_str!("../../../lean/examples/native_matrix_adjugate_zero/statement.lit");
const REAL: &str = include_str!("../../../lean/examples/native_matrix_adjugate_real/statement.lit");
const TRANSPORT: &str =
    include_str!("../../../lean/examples/native_matrix_adjugate_transport/statement.lit");

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("original adjugate law")
    };
    match law {
        NativeMatrixLawProof::AdjugateLeft(p) => &mut p.application,
        NativeMatrixLawProof::AdjugateRight(p) => &mut p.application,
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
fn adjugate_replays_distinct_native_clauses_reverse_zero_and_real_profiles() {
    for source in [LEFT, RIGHT, REVERSE, ZERO] {
        let (mut run, compiler) = super::execute(source);
        for statement in &mut run.statement_results {
            let p = selected(statement, 0);
            assert_eq!(p.arguments.len(), 2);
            assert_eq!(p.requirements.len(), 3);
            assert_eq!(p.requirement_proofs.len(), 3);
            assert_eq!(
                matches!(p.orientation, MatrixLawOrientation::Reverse),
                source == REVERSE
            );
        }
        super::compile_run(&run, &compiler, "native_adjugate").unwrap();
    }
    let (mut run, compiler) = super::execute(REAL);
    for statement in &mut run.statement_results {
        selected(statement, 1);
    }
    super::compile_run(&run, &compiler, "real_adjugate").unwrap();
}

#[test]
fn adjugate_requires_three_original_ordered_premises_ids_carriers_and_domains() {
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
fn adjugate_preserves_original_factor_order_square_dimensions_and_scaled_identity() {
    for source in [LEFT, RIGHT] {
        for change in [
            "argument",
            "product_dimension",
            "factor_order",
            "adjugate_matrix",
            "adjugate_order",
            "determinant_matrix",
            "determinant_order",
            "identity_order",
            "scale_dimension",
            "orientation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "product_dimension" | "factor_order" | "adjugate_matrix" | "adjugate_order" => {
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
                            let Obj::MatrixOperator(MatrixOperator::Adjugate(adj)) =
                                object.as_mut()
                            else {
                                panic!()
                            };
                            if change == "adjugate_matrix" {
                                adj.matrix = Box::new(super::number_object("7"));
                            } else {
                                adj.order = Box::new(super::number_object("7"));
                            }
                        }
                    }
                }
                "determinant_matrix" | "determinant_order" | "identity_order"
                | "scale_dimension" => {
                    let Obj::MatrixOperator(MatrixOperator::Scale(m)) = &mut p.conclusion.right
                    else {
                        panic!()
                    };
                    if change == "scale_dimension" {
                        m.cols = Box::new(super::number_object("7"));
                    } else if change == "identity_order" {
                        let Obj::MatrixOperator(MatrixOperator::IdentityMatrix(i)) =
                            m.matrix.as_mut()
                        else {
                            panic!()
                        };
                        i.order = Box::new(super::number_object("7"));
                    } else {
                        let Obj::MatrixOperator(MatrixOperator::Determinant(d)) = m.scalar.as_mut()
                        else {
                            panic!()
                        };
                        if change == "determinant_matrix" {
                            d.matrix = Box::new(super::number_object("7"));
                        } else {
                            d.order = Box::new(super::number_object("7"));
                        }
                    }
                }
                "orientation" => p.orientation = MatrixLawOrientation::Reverse,
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn adjugate_does_not_exchange_equal_arity_left_and_right_contracts() {
    for (source, wrong) in [
        (LEFT, MatrixAdjugateLaw::Right),
        (RIGHT, MatrixAdjugateLaw::Left),
    ] {
        let (mut run, _) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert!(
            validate_matrix_adjugate_law(wrong, &p.arguments, &p.requirements, &p.conclusion)
                .is_err()
        );
    }
}

#[test]
fn explicit_adjugate_replays_three_stages_both_conclusions_and_singular_named_call() {
    let (mut run, compiler) = super::execute(EXPLICIT);
    let p = release(&mut run.statement_results[0]);
    assert_eq!(p.dom_proofs.len(), 3);
    assert_eq!(p.dom_stores.len(), 3);
    assert_eq!(p.builtin.as_ref().unwrap().requirements.len(), 3);
    assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 2);
    assert_eq!(p.conclusions_wd.len(), 2);
    assert_eq!(p.stored_wd.len(), 2);
    assert_eq!(p.stored.len(), 2);
    super::compile_run(&run, &compiler, "combined_adjugate").unwrap();
}

#[test]
fn explicit_adjugate_requires_original_order_stores_wd_ids_arguments_and_theorem() {
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
            "theorem" => p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::MatrixInverseLaws,
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn explicit_adjugate_retains_each_original_conclusion_publication_and_formation() {
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
fn adjugate_requires_parent_product_nested_adjugate_and_scaled_identity_wd() {
    for source in [LEFT, RIGHT] {
        for change in [
            "outer_child",
            "outer_premise",
            "adj_child",
            "adj_premise",
            "scale_child",
            "scale_premise",
        ] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            if matches!(change, "scale_child" | "scale_premise") {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::MatrixOperator(
                            MatrixOperatorObjWellDefinedProofByDef::Scale(scale),
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
                    panic!("original scaled-identity WD")
                };
                if change == "scale_child" {
                    scale.child_obj_well_defined.pop();
                } else {
                    scale.requirement_fact_verified.pop();
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
                                MatrixOperatorObjWellDefinedProofByDef::Adjugate(adj),
                            ),
                        ..
                    } = m.child_obj_well_defined[index].as_detailed_mut().unwrap()
                    else {
                        panic!("nested original adjugate WD")
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
fn adjugate_endpoint_transport_retains_both_original_assumption_citations() {
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
        super::compile_run(&run, &compiler, "original_adjugate_endpoint").unwrap();
        let p = selected(&mut run.statement_results[index], 0);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = p.right_equal.as_mut()
        else {
            panic!()
        };
        path.path[0].2 = FactId::new(u64::MAX);
        assert!(super::compile_run(&run, &compiler, "missing_adjugate_endpoint").is_err());
    }
}

#[test]
fn adjugate_does_not_skip_executed_real_carrier_intermediates() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(REAL);
        super::compile_run(&run, &compiler, "original_adjugate_carriers").unwrap();
        super::forall_proof_mut(&mut run.statement_results[index])
            .proved_then_facts
            .remove(0);
        assert!(super::compile_run(&run, &compiler, "skipped_adjugate_carrier").is_err());
    }
}
