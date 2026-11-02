use crate::compile_to_lean::compile_matrix_transform_laws::{validate_matrix_transform_law, MatrixTransformLaw};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const TRANSPOSE: &str =
    include_str!("../../../lean/examples/native_matrix_transpose_mul/statement.lit");
const ADJOINT: &str =
    include_str!("../../../lean/examples/native_matrix_adjoint_mul/statement.lit");
const REVERSE: &str =
    include_str!("../../../lean/examples/native_matrix_transform_reverse/statement.lit");
const ZERO: &str =
    include_str!("../../../lean/examples/native_matrix_transform_zero_dimensions/statement.lit");
const REAL: &str =
    include_str!("../../../lean/examples/native_matrix_transform_real/statement.lit");
const TRANSPORT: &str =
    include_str!("../../../lean/examples/native_matrix_transform_transport/statement.lit");
const EXPLICIT_TRANSPOSE: &str =
    include_str!("../../../lean/examples/matrix_transpose_mul/statement.lit");
const EXPLICIT_ADJOINT: &str =
    include_str!("../../../lean/examples/matrix_adjoint_mul/statement.lit");

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("actual selected transform law")
    };
    match law {
        NativeMatrixLawProof::MatrixTransposeMul(p) => &mut p.application,
        NativeMatrixLawProof::MatrixAdjointMul(p) => &mut p.application,
        _ => panic!("actual transpose/adjoint variant"),
    }
}
fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("actual named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("actual forall body")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body.proof_steps[0]
    else {
        panic!("actual release")
    };
    p
}
fn transformed_matrix(object: &mut Obj) -> &mut Obj {
    match object {
        Obj::MatrixOperator(MatrixOperator::Transpose(p)) => p.matrix.as_mut(),
        Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(p)) => p.matrix.as_mut(),
        _ => panic!("original transform object"),
    }
}

#[test]
fn native_matrix_transform_replays_selected_variants_reverse_zero_and_real_profiles() {
    for source in [TRANSPOSE, ADJOINT, REVERSE, ZERO] {
        let (mut run, compiler) = super::execute(source);
        for statement in &mut run.statement_results {
            let p = selected(statement, 0);
            assert_eq!(p.arguments.len(), 5);
            assert_eq!(p.requirements.len(), 6);
            assert_eq!(p.requirement_proofs.len(), 6);
            assert_eq!(
                matches!(p.orientation, MatrixLawOrientation::Reverse),
                source == REVERSE
            );
        }
        super::compile_run(&run, &compiler, "matrix_transform").unwrap();
    }
    let (mut run, compiler) = super::execute(REAL);
    for statement in &mut run.statement_results {
        selected(statement, 2);
    }
    super::compile_run(&run, &compiler, "real_matrix_transform").unwrap();
}

#[test]
fn native_matrix_transform_requires_all_six_ordered_premises_ids_carriers_and_dimensions() {
    for source in [TRANSPOSE, ADJOINT] {
        for change in [
            "count",
            "extra",
            "order",
            "repeated_id",
            "carrier",
            "domain",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "count" => {
                    p.requirement_proofs.pop();
                }
                "extra" => p.requirements.push(p.requirements[0].clone()),
                "order" => p.requirement_proofs.swap(0, 1),
                "repeated_id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[3] else {
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
fn native_matrix_transform_preserves_arguments_nested_products_reversed_dimensions_and_orientation()
{
    for source in [TRANSPOSE, ADJOINT] {
        for change in [
            "argument",
            "conclusion",
            "nested",
            "output_dimension",
            "factor_order",
            "orientation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "conclusion" => p.conclusion.right = super::number_object("7"),
                "nested" => {
                    let Obj::MatrixOperator(MatrixOperator::Multiply(m)) =
                        transformed_matrix(&mut p.conclusion.left)
                    else {
                        panic!()
                    };
                    m.inner = Box::new(super::number_object("7"));
                }
                "output_dimension" | "factor_order" => {
                    let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = &mut p.conclusion.right
                    else {
                        panic!()
                    };
                    if change == "output_dimension" {
                        m.rows = Box::new(p.arguments[2].clone());
                    } else {
                        std::mem::swap(&mut m.left, &mut m.right);
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
fn native_matrix_transform_does_not_exchange_equal_arity_transpose_and_adjoint_contracts() {
    for (source, wrong) in [
        (TRANSPOSE, MatrixTransformLaw::Adjoint),
        (ADJOINT, MatrixTransformLaw::Transpose),
    ] {
        let (mut run, _) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert!(
            validate_matrix_transform_law(wrong, &p.arguments, &p.requirements, &p.conclusion)
                .is_err()
        );
    }
}

#[test]
fn explicit_matrix_transform_replays_six_original_stages_and_rectangular_named_calls() {
    for source in [EXPLICIT_TRANSPOSE, EXPLICIT_ADJOINT] {
        let (mut run, compiler) = super::execute(source);
        let p = release(&mut run.statement_results[0]);
        assert_eq!(p.dom_proofs.len(), 6);
        assert_eq!(p.dom_stores.len(), 6);
        assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 1);
        assert_eq!(p.conclusions_wd.len(), 1);
        super::compile_run(&run, &compiler, "explicit_matrix_transform").unwrap();
    }
}

#[test]
fn explicit_matrix_transform_requires_original_stores_wd_ids_and_selected_contract() {
    for source in [EXPLICIT_TRANSPOSE, EXPLICIT_ADJOINT] {
        for change in [
            "stores",
            "proof_order",
            "clause",
            "wd",
            "repeated_id",
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
                "repeated_id" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.builtin.as_mut().unwrap().requirements[3]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                "theorem" => {
                    p.builtin.as_mut().unwrap().theorem = if source == EXPLICIT_TRANSPOSE {
                        crate::builtin_theorem::BuiltinTheoremId::MatrixAdjointMul
                    } else {
                        crate::builtin_theorem::BuiltinTheoremId::MatrixTransposeMul
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_transform_requires_original_outer_and_nested_constructor_wd() {
    for source in [TRANSPOSE, ADJOINT] {
        for change in ["child", "premise", "nested"] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::MatrixOperator(outer),
                ..
            } = wd.left.as_detailed_mut().unwrap()
            else {
                panic!("actual outer WD")
            };
            let (children, requirements) = match outer {
                MatrixOperatorObjWellDefinedProofByDef::Transpose(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                MatrixOperatorObjWellDefinedProofByDef::ConjugateTranspose(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("actual transform WD"),
            };
            match change {
                "child" => {
                    children.pop();
                }
                "premise" => {
                    requirements.pop();
                }
                "nested" => {
                    let DetailedObjWellDefinedProof::ByDef {
                        proof:
                            ObjWellDefinedProofByDef::MatrixOperator(
                                MatrixOperatorObjWellDefinedProofByDef::Multiply(p),
                            ),
                        ..
                    } = children[0].as_detailed_mut().unwrap()
                    else {
                        panic!("original product WD")
                    };
                    p.child_obj_well_defined.pop();
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_transform_endpoint_transport_retains_each_original_assumption_citation() {
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
        super::compile_run(&run, &compiler, "transform_endpoint").unwrap();
        let p = selected(&mut run.statement_results[index], 0);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = p.right_equal.as_mut()
        else {
            panic!()
        };
        path.path[0].2 = FactId::new(u64::MAX);
        assert!(super::compile_run(&run, &compiler, "missing_transform_endpoint").is_err());
    }
}

#[test]
fn native_matrix_transform_does_not_skip_any_executed_real_matrix_carrier() {
    for statement in 0..2 {
        for index in 0..2 {
            let (mut run, compiler) = super::execute(REAL);
            super::compile_run(&run, &compiler, "original_transform_carriers").unwrap();
            super::forall_proof_mut(&mut run.statement_results[statement])
                .proved_then_facts
                .remove(index);
            assert!(super::compile_run(&run, &compiler, "skipped_transform_carrier").is_err());
        }
    }
}
