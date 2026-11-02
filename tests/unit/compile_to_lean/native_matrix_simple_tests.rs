use crate::compile_to_lean::compile_matrix_simple_laws::{validate_simple_matrix_law, SimpleMatrixLaw};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const LEFT: &str =
    include_str!("../../../lean/examples/native_matrix_mul_identity_left/statement.lit");
const RIGHT: &str =
    include_str!("../../../lean/examples/native_matrix_mul_identity_right/statement.lit");
const ZERO_L: &str =
    include_str!("../../../lean/examples/native_matrix_mul_zero_left/statement.lit");
const ZERO_R: &str =
    include_str!("../../../lean/examples/native_matrix_mul_zero_right/statement.lit");
const REVERSE: &str =
    include_str!("../../../lean/examples/native_matrix_mul_reverse/statement.lit");
const ZERO_DIMS: &str =
    include_str!("../../../lean/examples/native_matrix_mul_zero_dimensions/statement.lit");
const REAL: &str = include_str!("../../../lean/examples/native_matrix_mul_real/statement.lit");
const TRANSPORT: &str =
    include_str!("../../../lean/examples/native_matrix_mul_transport/statement.lit");
const EXPLICIT_ID: &str = include_str!("../../../lean/examples/matrix_mul_identity/statement.lit");
const EXPLICIT_ZERO: &str = include_str!("../../../lean/examples/matrix_mul_zero/statement.lit");

fn application(result: &mut VerifyFactResult) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("actual native multiplication law")
    };
    match law {
        NativeMatrixLawProof::MulIdentityLeft(p) => &mut p.application,
        NativeMatrixLawProof::MulIdentityRight(p) => &mut p.application,
        NativeMatrixLawProof::MulZeroRight(p) => &mut p.application,
        NativeMatrixLawProof::MulZeroLeft(p) => &mut p.application,
        _ => panic!("actual identity/zero variant"),
    }
}
fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    application(&mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result)
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
fn native_matrix_simple_replays_four_actual_variants_and_reverse_zero_real_profiles() {
    for source in [LEFT, RIGHT, ZERO_L, ZERO_R, ZERO_DIMS] {
        let (mut run, compiler) = super::execute(source);
        for statement in &mut run.statement_results {
            let p = selected(statement, 0);
            assert_eq!(
                p.requirements.len(),
                if source == ZERO_L || source == ZERO_R {
                    4
                } else if source == ZERO_DIMS && p.arguments.len() == 4 {
                    4
                } else {
                    3
                }
            );
            assert_eq!(
                matches!(p.orientation, MatrixLawOrientation::Reverse),
                source == RIGHT
            );
        }
        super::compile_run(&run, &compiler, "native_matrix_simple").unwrap();
    }
    let (mut run, compiler) = super::execute(REVERSE);
    for (index, statement) in run.statement_results.iter_mut().enumerate() {
        assert_eq!(
            matches!(
                selected(statement, 0).orientation,
                MatrixLawOrientation::Reverse
            ),
            index != 1
        );
    }
    super::compile_run(&run, &compiler, "reverse_matrix_simple").unwrap();
    let (mut run, compiler) = super::execute(REAL);
    selected(&mut run.statement_results[0], 1);
    super::compile_run(&run, &compiler, "real_matrix_simple").unwrap();
}

#[test]
fn native_matrix_simple_preserves_requirement_counts_order_ids_and_exact_carriers() {
    for source in [LEFT, RIGHT, ZERO_L, ZERO_R] {
        for change in ["count", "extra", "order", "id", "carrier"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "count" => {
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
                "carrier" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2] else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_simple_preserves_argument_order_product_shape_and_orientation() {
    for source in [LEFT, RIGHT, ZERO_L, ZERO_R] {
        for change in ["argument", "conclusion", "dimension", "orientation"] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "conclusion" => p.conclusion.right = super::number_object("7"),
                "dimension" => {
                    let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = &mut p.conclusion.left
                    else {
                        panic!()
                    };
                    m.inner = Box::new(super::number_object("7"));
                }
                "orientation" => {
                    p.orientation = if matches!(p.orientation, MatrixLawOrientation::Forward) {
                        MatrixLawOrientation::Reverse
                    } else {
                        MatrixLawOrientation::Forward
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_matrix_simple_does_not_choose_a_different_clause_from_equal_arity() {
    for (source, wrong) in [
        (LEFT, SimpleMatrixLaw::IdentityRight),
        (RIGHT, SimpleMatrixLaw::IdentityLeft),
        (ZERO_L, SimpleMatrixLaw::ZeroRight),
        (ZERO_R, SimpleMatrixLaw::ZeroLeft),
    ] {
        let (mut run, _) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert!(
            validate_simple_matrix_law(wrong, &p.arguments, &p.requirements, &p.conclusion)
                .is_err()
        );
    }
}

#[test]
fn explicit_matrix_simple_replays_both_clauses_and_rectangular_named_instantiation() {
    for source in [EXPLICIT_ID, EXPLICIT_ZERO] {
        let (mut run, compiler) = super::execute(source);
        let p = release(&mut run.statement_results[0]);
        assert_eq!(
            p.dom_proofs.len(),
            if source == EXPLICIT_ID { 3 } else { 4 }
        );
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 2);
        assert_eq!(p.conclusions_wd.len(), 2);
        super::compile_run(&run, &compiler, "explicit_matrix_simple").unwrap();
    }
}

#[test]
fn explicit_matrix_simple_requires_all_original_proofs_stores_conclusions_and_wd() {
    for source in [EXPLICIT_ID, EXPLICIT_ZERO] {
        for change in ["stores", "proof_order", "clause", "wd", "id", "argument"] {
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
                        &mut p.builtin.as_mut().unwrap().requirements[0]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn explicit_matrix_simple_cannot_exchange_the_original_left_and_right_clauses() {
    for source in [EXPLICIT_ID, EXPLICIT_ZERO] {
        let (mut run, compiler) = super::execute(source);
        release(&mut run.statement_results[0])
            .builtin
            .as_mut()
            .unwrap()
            .conclusions
            .swap(0, 1);
        assert!(super::compile_run(&run, &compiler, "exchanged_matrix_clauses").is_err());
    }
}

#[test]
fn native_matrix_simple_cannot_replace_missing_original_parent_constructor_evidence() {
    for source in [LEFT, RIGHT, ZERO_L, ZERO_R] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            let left = matches!(
                eq.fact.left,
                Obj::MatrixOperator(MatrixOperator::Multiply(_))
            );
            let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
            let wd = if left { &mut wd.left } else { &mut wd.right };
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::MatrixOperator(
                        MatrixOperatorObjWellDefinedProofByDef::Multiply(p),
                    ),
                ..
            } = wd.as_detailed_mut().unwrap()
            else {
                panic!("original product WD")
            };
            if child {
                p.child_obj_well_defined.pop();
            } else {
                p.requirement_fact_verified.pop();
            }
            assert!(super::compile_run(&run, &compiler, "missing_matrix_parent").is_err());
        }
    }
}

#[test]
fn native_matrix_simple_endpoint_transport_retains_its_original_assumption_citation() {
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
    super::compile_run(&run, &compiler, "matrix_endpoint_transport").unwrap();
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_mut()
    else {
        panic!()
    };
    path.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_matrix_endpoint").is_err());
}

#[test]
fn native_matrix_simple_does_not_skip_the_executed_real_to_complex_intermediate() {
    let (mut run, compiler) = super::execute(REAL);
    super::compile_run(&run, &compiler, "original_matrix_intermediate").unwrap();
    super::forall_proof_mut(&mut run.statement_results[0])
        .proved_then_facts
        .remove(0);
    assert!(super::compile_run(&run, &compiler, "skipped_matrix_intermediate").is_err());
}
