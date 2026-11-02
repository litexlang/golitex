use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_builtin_determinant_theorem::validate_determinant_law;
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const NATIVE: &str = include_str!("../../../lean/examples/native_matrix_det_mul/statement.lit");
const EXPLICIT: &str = include_str!("../../../lean/examples/matrix_det_mul/statement.lit");
const REVERSE: &str =
    include_str!("../../../lean/examples/native_matrix_det_mul_reverse/statement.lit");
const REPEATED: &str =
    include_str!("../../../lean/examples/native_matrix_det_mul_repeated_factor/statement.lit");
const ZERO: &str = include_str!("../../../lean/examples/native_matrix_det_mul_zero/statement.lit");
const REAL: &str = include_str!("../../../lean/examples/native_matrix_det_mul_real/statement.lit");
const TRANSPORT: &str =
    include_str!("../../../lean/examples/native_matrix_det_mul_transport/statement.lit");

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        NativeMatrixLawProof::DetMul(p),
    )) = &mut eq.searched_proof
    else {
        panic!("original selected determinant product")
    };
    &mut p.application
}
fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("named original theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall body")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original invocation")
    };
    p
}

#[test]
fn determinant_product_replays_native_explicit_reverse_zero_real_and_named_profiles() {
    for source in [NATIVE, REPEATED, REVERSE, ZERO] {
        let (mut run, compiler) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert_eq!(p.arguments.len(), 3);
        assert_eq!(p.requirements.len(), 6);
        assert_eq!(p.requirement_proofs.len(), 6);
        assert_eq!(
            matches!(p.orientation, MatrixLawOrientation::Reverse),
            source == REVERSE
        );
        super::compile_run(&run, &compiler, "determinant_product").unwrap();
    }
    let (mut run, compiler) = super::execute(REAL);
    selected(&mut run.statement_results[0], 2);
    super::compile_run(&run, &compiler, "real_determinant_product").unwrap();
    let (mut run, compiler) = super::execute(EXPLICIT);
    let p = release(&mut run.statement_results[0]);
    assert_eq!(p.dom_proofs.len(), 6);
    assert_eq!(p.dom_stores.len(), 6);
    assert_eq!(p.conclusions_wd.len(), 1);
    super::compile_run(&run, &compiler, "explicit_determinant_product").unwrap();
}

#[test]
fn determinant_product_retains_all_six_original_premises_ids_and_carriers() {
    for change in [
        "count",
        "extra",
        "order",
        "duplicate",
        "identity",
        "carrier",
        "domain",
    ] {
        let (mut run, compiler) = super::execute(NATIVE);
        let p = selected(&mut run.statement_results[0], 0);
        match change {
            "count" => {
                p.requirement_proofs.pop();
            }
            "extra" => p.requirements.push(p.requirements[0].clone()),
            "order" => p.requirement_proofs.swap(0, 1),
            "duplicate" => {
                let id = p.requirements[0].fact_id();
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[3] else {
                    panic!()
                };
                f.fact_id = id;
            }
            "identity" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[4] else {
                    panic!()
                };
                f.fact_id = FactId::new(u64::MAX);
            }
            "carrier" | "domain" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[5] else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::MatrixSet(m)) = &mut f.set else {
                    panic!()
                };
                if change == "carrier" {
                    m.set = Box::new(Obj::StandardSet(StandardSet::R));
                } else {
                    m.cols = Box::new(super::number_object("7"));
                }
            }
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn determinant_product_keeps_independent_matrix_proofs_for_a_repeated_factor() {
    let (mut run, compiler) = super::execute(REPEATED);
    let p = selected(&mut run.statement_results[0], 0);
    assert_eq!(p.requirements[2].ir(), p.requirements[5].ir());
    assert_ne!(p.requirements[2].fact_id(), p.requirements[5].fact_id());
    super::compile_run(&run, &compiler, "original_repeated_matrix").unwrap();
    for change in ["swapped_matrix_proofs", "duplicate_matrix_id"] {
        let (mut run, compiler) = super::execute(REPEATED);
        let p = selected(&mut run.statement_results[0], 0);
        if change == "swapped_matrix_proofs" {
            p.requirement_proofs.swap(2, 5);
        } else {
            let id = p.requirements[2].fact_id();
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[5] else {
                panic!()
            };
            f.fact_id = id;
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn determinant_product_preserves_factors_orders_nested_dimensions_and_orientation() {
    for change in [
        "argument",
        "outer_order",
        "inner_dimension",
        "left_factor",
        "right_factor",
        "right_order",
        "rhs_order",
        "orientation",
    ] {
        let (mut run, compiler) = super::execute(NATIVE);
        let p = selected(&mut run.statement_results[0], 0);
        match change {
            "argument" => p.arguments.swap(0, 1),
            "outer_order" | "inner_dimension" | "left_factor" => {
                let Obj::MatrixOperator(MatrixOperator::Determinant(det)) = &mut p.conclusion.left
                else {
                    panic!()
                };
                if change == "outer_order" {
                    det.order = Box::new(super::number_object("7"));
                } else {
                    let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = det.matrix.as_mut()
                    else {
                        panic!()
                    };
                    if change == "inner_dimension" {
                        m.inner = Box::new(super::number_object("7"));
                    } else {
                        std::mem::swap(&mut m.left, &mut m.right);
                    }
                }
            }
            "right_factor" | "right_order" | "rhs_order" => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) = &mut p.conclusion.right
                else {
                    panic!()
                };
                if change == "rhs_order" {
                    std::mem::swap(&mut m.left, &mut m.right);
                } else {
                    let Obj::MatrixOperator(MatrixOperator::Determinant(det)) = m.right.as_mut()
                    else {
                        panic!()
                    };
                    if change == "right_factor" {
                        det.matrix = Box::new(p.arguments[0].clone());
                    } else {
                        det.order = Box::new(super::number_object("7"));
                    }
                }
            }
            "orientation" => p.orientation = MatrixLawOrientation::Reverse,
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn determinant_product_never_selects_another_contract_by_arity() {
    let (mut run, _) = super::execute(NATIVE);
    let p = selected(&mut run.statement_results[0], 0);
    assert!(validate_determinant_law(
        BuiltinTheoremId::MatrixRankTranspose,
        &p.arguments,
        &p.requirements,
        &p.conclusion
    )
    .is_err());
    assert!(validate_determinant_law(
        BuiltinTheoremId::MatrixDetTranspose,
        &p.arguments,
        &p.requirements,
        &p.conclusion
    )
    .is_err());
}

#[test]
fn explicit_determinant_product_requires_original_stages_conclusion_and_contract() {
    for change in [
        "proof",
        "proof_order",
        "store",
        "wd",
        "conclusion",
        "identity",
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
            "wd" => {
                p.conclusions_wd.pop();
            }
            "conclusion" => {
                p.builtin.as_mut().unwrap().conclusions.pop();
            }
            "identity" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[3]
                else {
                    panic!()
                };
                f.fact_id = FactId::new(u64::MAX);
            }
            "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "theorem" => p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::MatrixDetTranspose,
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn determinant_product_requires_original_parent_and_nested_product_wd() {
    for change in [
        "outer_child",
        "outer_premise",
        "inner_child",
        "inner_premise",
    ] {
        let (mut run, compiler) = super::execute(NATIVE);
        let eq = super::equality_proof_mut(
            &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                .verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(
                    MatrixOperatorObjWellDefinedProofByDef::Determinant(p),
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
            panic!("outer determinant WD")
        };
        match change {
            "outer_child" => {
                p.child_obj_well_defined.pop();
            }
            "outer_premise" => {
                p.requirement_fact_verified.pop();
            }
            "inner_child" | "inner_premise" => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::MatrixOperator(
                            MatrixOperatorObjWellDefinedProofByDef::Multiply(m),
                        ),
                    ..
                } = p.child_obj_well_defined[0].as_detailed_mut().unwrap()
                else {
                    panic!("inner product WD")
                };
                if change == "inner_child" {
                    m.child_obj_well_defined.pop();
                } else {
                    m.requirement_fact_verified.pop();
                }
            }
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn determinant_product_endpoint_transport_retains_original_citation() {
    let (mut run, compiler) = super::execute(TRANSPORT);
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_ref()
    else {
        panic!("original endpoint citation")
    };
    assert!(!path.path.is_empty());
    assert_eq!(path.path[0].0.ir(), p.conclusion.right.ir());
    super::compile_run(&run, &compiler, "original_det_endpoint").unwrap();
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_mut()
    else {
        panic!()
    };
    path.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_det_endpoint").is_err());
}

#[test]
fn determinant_product_does_not_skip_original_real_carrier_statements() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(REAL);
        super::compile_run(&run, &compiler, "original_real_carriers").unwrap();
        super::forall_proof_mut(&mut run.statement_results[0])
            .proved_then_facts
            .remove(index);
        assert!(super::compile_run(&run, &compiler, "skipped_real_carrier").is_err());
    }
}
