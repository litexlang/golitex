use crate::compile_to_lean::compile_matrix_algebra_laws::{
    validate_matrix_algebra_law, MatrixAlgebraLaw,
};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const ASSOC: &str = r#"# Matrix multiplication is associative for rectangular complex matrices.
forall replay_mul_m, replay_mul_k, replay_mul_p, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B matrix(C,replay_mul_k,replay_mul_p), replay_mul_C matrix(C,replay_mul_p,replay_mul_n):
    matrix_mul(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_p),replay_mul_C,replay_mul_m,replay_mul_p,replay_mul_n) = matrix_mul(replay_mul_A,matrix_mul(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_p,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n)
"#;
const LEFT: &str = r#"# Left multiplication distributes over addition of rectangular complex matrices.
forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B, replay_mul_C matrix(C,replay_mul_k,replay_mul_n):
    matrix_mul(replay_mul_A,matrix_add(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n) = matrix_add(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n)
"#;
const RIGHT: &str = r#"# Right multiplication distributes over addition of rectangular complex matrices.
forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A, replay_mul_B matrix(C,replay_mul_m,replay_mul_k), replay_mul_C matrix(C,replay_mul_k,replay_mul_n):
    matrix_mul(matrix_add(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k),replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n) = matrix_add(matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_B,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n)
"#;
const REVERSE: &str = r#"# State associativity and both distributive laws with their equality sides reversed.
forall replay_mul_m, replay_mul_k, replay_mul_p, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B matrix(C,replay_mul_k,replay_mul_p), replay_mul_C matrix(C,replay_mul_p,replay_mul_n):
    matrix_mul(replay_mul_A,matrix_mul(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_p,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n) = matrix_mul(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_p),replay_mul_C,replay_mul_m,replay_mul_p,replay_mul_n)
forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B, replay_mul_C matrix(C,replay_mul_k,replay_mul_n):
    matrix_add(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n) = matrix_mul(replay_mul_A,matrix_add(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n)
forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A, replay_mul_B matrix(C,replay_mul_m,replay_mul_k), replay_mul_C matrix(C,replay_mul_k,replay_mul_n):
    matrix_add(matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_B,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n) = matrix_mul(matrix_add(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k),replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n)
"#;
const ZERO: &str = r#"# Associativity and distributivity include empty row, column and summation domains.
forall replay_mul_k, replay_mul_n N, replay_mul_A matrix(C,0,replay_mul_k), replay_mul_B matrix(C,replay_mul_k,0), replay_mul_C matrix(C,0,replay_mul_n):
    matrix_mul(matrix_mul(replay_mul_A,replay_mul_B,0,replay_mul_k,0),replay_mul_C,0,0,replay_mul_n) = matrix_mul(replay_mul_A,matrix_mul(replay_mul_B,replay_mul_C,replay_mul_k,0,replay_mul_n),0,replay_mul_k,replay_mul_n)
forall replay_mul_m, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,0), replay_mul_B, replay_mul_C matrix(C,0,replay_mul_n):
    matrix_mul(replay_mul_A,matrix_add(replay_mul_B,replay_mul_C,0,replay_mul_n),replay_mul_m,0,replay_mul_n) = matrix_add(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,0,replay_mul_n),matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,0,replay_mul_n),replay_mul_m,replay_mul_n)
forall replay_mul_k N, replay_mul_A, replay_mul_B matrix(C,0,replay_mul_k), replay_mul_C matrix(C,replay_mul_k,0):
    matrix_mul(matrix_add(replay_mul_A,replay_mul_B,0,replay_mul_k),replay_mul_C,0,replay_mul_k,0) = matrix_add(matrix_mul(replay_mul_A,replay_mul_C,0,replay_mul_k,0),matrix_mul(replay_mul_B,replay_mul_C,0,replay_mul_k,0),0,0)
"#;
const REAL: &str = r#"# Real rectangular matrices satisfy distributivity after proving their complex carriers.
forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A matrix(R,replay_mul_m,replay_mul_k), replay_mul_B, replay_mul_C matrix(R,replay_mul_k,replay_mul_n):
    replay_mul_A $in matrix(C,replay_mul_m,replay_mul_k)
    replay_mul_B $in matrix(C,replay_mul_k,replay_mul_n)
    replay_mul_C $in matrix(C,replay_mul_k,replay_mul_n)
    matrix_mul(replay_mul_A,matrix_add(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n) = matrix_add(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n)
"#;
const TRANSPORT: &str = r#"# Use an assumed equality for the associated product to identify a fourth matrix.
forall replay_mul_m, replay_mul_k, replay_mul_p, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B matrix(C,replay_mul_k,replay_mul_p), replay_mul_C matrix(C,replay_mul_p,replay_mul_n), replay_mul_D matrix(C,replay_mul_m,replay_mul_n):
    matrix_mul(replay_mul_A,matrix_mul(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_p,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n) = replay_mul_D
    =>:
        matrix_mul(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_p),replay_mul_C,replay_mul_m,replay_mul_p,replay_mul_n) = replay_mul_D
"#;
const EXPLICIT_ASSOC: &str = r#"# Prove associativity for rectangular complex matrices and instantiate dimensions 2, 3, 4, 5.
thm replay_matrix_mul_associative:
    ? forall replay_mul_m, replay_mul_k, replay_mul_p, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B matrix(C,replay_mul_k,replay_mul_p), replay_mul_C matrix(C,replay_mul_p,replay_mul_n):
        matrix_mul(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_p),replay_mul_C,replay_mul_m,replay_mul_p,replay_mul_n) = matrix_mul(replay_mul_A,matrix_mul(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_p,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n)
    release thm matrix_mul_associative(replay_mul_A,replay_mul_B,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_p,replay_mul_n)
release thm replay_matrix_mul_associative(2,3,4,5,zero_matrix(2,3),zero_matrix(3,4),zero_matrix(4,5))
"#;
const EXPLICIT_LEFT: &str = r#"# Prove left distributivity for rectangular complex matrices using the named theorem.
thm replay_matrix_mul_distributive_left:
    ? forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A matrix(C,replay_mul_m,replay_mul_k), replay_mul_B, replay_mul_C matrix(C,replay_mul_k,replay_mul_n):
        matrix_mul(replay_mul_A,matrix_add(replay_mul_B,replay_mul_C,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_k,replay_mul_n) = matrix_add(matrix_mul(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n)
    release thm matrix_mul_distributive_left(replay_mul_A,replay_mul_B,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n)
"#;
const EXPLICIT_RIGHT: &str = r#"# Prove right distributivity for rectangular complex matrices using the named theorem.
thm replay_matrix_mul_distributive_right:
    ? forall replay_mul_m, replay_mul_k, replay_mul_n N, replay_mul_A, replay_mul_B matrix(C,replay_mul_m,replay_mul_k), replay_mul_C matrix(C,replay_mul_k,replay_mul_n):
        matrix_mul(matrix_add(replay_mul_A,replay_mul_B,replay_mul_m,replay_mul_k),replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n) = matrix_add(matrix_mul(replay_mul_A,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),matrix_mul(replay_mul_B,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n),replay_mul_m,replay_mul_n)
    release thm matrix_mul_distributive_right(replay_mul_A,replay_mul_B,replay_mul_C,replay_mul_m,replay_mul_k,replay_mul_n)
"#;

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("actual native algebra law")
    };
    match law {
        NativeMatrixLawProof::MulAssociative(p) => &mut p.application,
        NativeMatrixLawProof::MulDistributiveLeft(p) => &mut p.application,
        NativeMatrixLawProof::MulDistributiveRight(p) => &mut p.application,
        _ => panic!("actual associative/distributive variant"),
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
fn native_matrix_algebra_replays_actual_variants_reverse_zero_and_real_profiles() {
    for source in [ASSOC, LEFT, RIGHT, REVERSE, ZERO] {
        let (mut run, compiler) = super::execute(source);
        for statement in &mut run.statement_results {
            let p = selected(statement, 0);
            assert_eq!(p.requirements.len(), 9);
            assert_eq!(p.requirement_proofs.len(), 9);
            assert_eq!(
                matches!(p.orientation, MatrixLawOrientation::Reverse),
                source == REVERSE
            );
        }
        super::compile_run(&run, &compiler, "native_matrix_algebra").unwrap();
    }
    let (mut run, compiler) = super::execute(REAL);
    selected(&mut run.statement_results[0], 3);
    super::compile_run(&run, &compiler, "real_matrix_algebra").unwrap();
}

#[test]
fn native_matrix_algebra_preserves_all_nine_ordered_premises_and_original_ids() {
    for source in [ASSOC, LEFT, RIGHT] {
        for change in ["count", "extra", "order", "repeated_id", "carrier"] {
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
                "carrier" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[8] else {
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
fn native_matrix_algebra_preserves_arguments_nested_products_dimensions_and_orientation() {
    for source in [ASSOC, LEFT, RIGHT] {
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
                "orientation" => p.orientation = MatrixLawOrientation::Reverse,
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
    let (mut run, compiler) = super::execute(ASSOC);
    let p = selected(&mut run.statement_results[0], 0);
    let Obj::MatrixOperator(MatrixOperator::Multiply(outer)) = &mut p.conclusion.left else {
        panic!()
    };
    let Obj::MatrixOperator(MatrixOperator::Multiply(inner)) = outer.left.as_mut() else {
        panic!()
    };
    inner.inner = Box::new(super::number_object("7"));
    assert!(super::compile_run(&run, &compiler, "nested_dimension").is_err());
}

#[test]
fn native_matrix_algebra_does_not_select_another_equal_arity_distributive_law() {
    for (source, wrong) in [
        (LEFT, MatrixAlgebraLaw::DistributiveRight),
        (RIGHT, MatrixAlgebraLaw::DistributiveLeft),
    ] {
        let (mut run, _) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert!(
            validate_matrix_algebra_law(wrong, &p.arguments, &p.requirements, &p.conclusion)
                .is_err()
        );
    }
}

#[test]
fn explicit_matrix_algebra_replays_nine_proof_store_stages_and_rectangular_call() {
    for source in [EXPLICIT_ASSOC, EXPLICIT_LEFT, EXPLICIT_RIGHT] {
        let (mut run, compiler) = super::execute(source);
        let p = release(&mut run.statement_results[0]);
        assert_eq!(p.dom_proofs.len(), 9);
        assert_eq!(p.dom_stores.len(), 9);
        assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 1);
        assert_eq!(p.conclusions_wd.len(), 1);
        super::compile_run(&run, &compiler, "explicit_matrix_algebra").unwrap();
    }
}

#[test]
fn explicit_matrix_algebra_requires_all_original_stages_and_selected_theorem() {
    for source in [EXPLICIT_ASSOC, EXPLICIT_LEFT, EXPLICIT_RIGHT] {
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
fn native_matrix_algebra_cannot_replace_missing_original_parent_constructor_evidence() {
    for source in [ASSOC, LEFT, RIGHT] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::MatrixOperator(
                        MatrixOperatorObjWellDefinedProofByDef::Multiply(p),
                    ),
                ..
            } = wd.left.as_detailed_mut().unwrap()
            else {
                panic!("original product WD")
            };
            if child {
                p.child_obj_well_defined.pop();
            } else {
                p.requirement_fact_verified.pop();
            }
            assert!(super::compile_run(&run, &compiler, "missing_algebra_parent").is_err());
        }
    }
}

#[test]
fn native_matrix_algebra_endpoint_transport_retains_original_assumption_citation() {
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
    super::compile_run(&run, &compiler, "algebra_endpoint_transport").unwrap();
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_mut()
    else {
        panic!()
    };
    path.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_algebra_endpoint").is_err());
}

#[test]
fn native_matrix_algebra_does_not_skip_any_executed_real_carrier_intermediate() {
    for index in 0..3 {
        let (mut run, compiler) = super::execute(REAL);
        super::compile_run(&run, &compiler, "original_algebra_intermediates").unwrap();
        super::forall_proof_mut(&mut run.statement_results[0])
            .proved_then_facts
            .remove(index);
        assert!(super::compile_run(&run, &compiler, "skipped_algebra_intermediate").is_err());
    }
}
