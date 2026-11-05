use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_builtin_rank_theorem::validate_rank_invertible_law;
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const NATIVE: &str = r#"# Preserve the original nonzero determinant premise for full rank.
forall replay_invertible_rank_n N, replay_invertible_rank_A matrix(C,replay_invertible_rank_n,replay_invertible_rank_n):
    det(replay_invertible_rank_A,replay_invertible_rank_n) != 0
    =>:
        matrix_rank(replay_invertible_rank_A,replay_invertible_rank_n,replay_invertible_rank_n) = replay_invertible_rank_n
"#;
const EXPLICIT: &str = r#"# Retain both proved determinant intermediates before the named call.
thm replay_matrix_rank_invertible:
    ? forall replay_invertible_rank_n N, replay_invertible_rank_A matrix(C,replay_invertible_rank_n,replay_invertible_rank_n):
        det(replay_invertible_rank_A,replay_invertible_rank_n) != 0
        =>:
            matrix_rank(replay_invertible_rank_A,replay_invertible_rank_n,replay_invertible_rank_n) = replay_invertible_rank_n
    release thm matrix_rank_invertible(replay_invertible_rank_A,replay_invertible_rank_n)
det(identity_matrix(2),2) = 1
det(identity_matrix(2),2) != 0
release thm replay_matrix_rank_invertible(2,identity_matrix(2))
"#;
const REVERSE: &str = r#"# Reverse the original guarded full-rank equality.
forall replay_invertible_rank_n N, replay_invertible_rank_A matrix(C,replay_invertible_rank_n,replay_invertible_rank_n):
    det(replay_invertible_rank_A,replay_invertible_rank_n) != 0
    =>:
        replay_invertible_rank_n = matrix_rank(replay_invertible_rank_A,replay_invertible_rank_n,replay_invertible_rank_n)
"#;
const ZERO: &str = r#"# Preserve the original determinant guard at natural order zero.
forall replay_invertible_rank_A matrix(C,0,0):
    det(replay_invertible_rank_A,0) != 0
    =>:
        matrix_rank(replay_invertible_rank_A,0,0) = 0
"#;
const REAL: &str = r#"# Retain the proved complex carrier for the original real matrix.
forall replay_invertible_rank_n N, replay_invertible_rank_A matrix(R,replay_invertible_rank_n,replay_invertible_rank_n):
    det(replay_invertible_rank_A,replay_invertible_rank_n) != 0
    =>:
        replay_invertible_rank_A $in matrix(C,replay_invertible_rank_n,replay_invertible_rank_n)
        matrix_rank(replay_invertible_rank_A,replay_invertible_rank_n,replay_invertible_rank_n) = replay_invertible_rank_n
"#;
const TRANSPORT: &str = r#"# Transport the original order endpoint using the given equality.
forall replay_invertible_rank_n, replay_invertible_rank_value N, replay_invertible_rank_A matrix(C,replay_invertible_rank_n,replay_invertible_rank_n):
    det(replay_invertible_rank_A,replay_invertible_rank_n) != 0
    replay_invertible_rank_n = replay_invertible_rank_value
    =>:
        matrix_rank(replay_invertible_rank_A,replay_invertible_rank_n,replay_invertible_rank_n) = replay_invertible_rank_value
"#;
const GUARD: &str = r#"# Retain original scalar equality and nonzero evidence for the determinant guard.
forall replay_invertible_rank_n N, replay_invertible_rank_A matrix(C,replay_invertible_rank_n,replay_invertible_rank_n), replay_invertible_rank_det C:
    det(replay_invertible_rank_A,replay_invertible_rank_n) = replay_invertible_rank_det
    replay_invertible_rank_det != 0
    =>:
        matrix_rank(replay_invertible_rank_A,replay_invertible_rank_n,replay_invertible_rank_n) = replay_invertible_rank_n
"#;

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let p = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        NativeMatrixLawProof::RankInvertible(p),
    )) = &mut p.searched_proof
    else {
        panic!("actual selected guarded rank law")
    };
    &mut p.application
}

fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("original named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall proof")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original explicit invocation")
    };
    p
}

#[test]
fn invertible_rank_replays_original_guard_reverse_zero_real_and_named_profiles() {
    for (source, index) in [
        (NATIVE, 0),
        (REVERSE, 0),
        (ZERO, 0),
        (REAL, 1),
        (TRANSPORT, 0),
        (GUARD, 0),
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = selected(&mut run.statement_results[0], index);
        assert_eq!(p.arguments.len(), 2);
        assert_eq!(p.requirements.len(), 4);
        assert_eq!(p.requirement_proofs.len(), 4);
        assert_eq!(
            matches!(p.orientation, MatrixLawOrientation::Reverse),
            source == REVERSE
        );
        super::compile_run(&run, &compiler, "original_invertible_rank").unwrap();
    }
    let (mut run, compiler) = super::execute(EXPLICIT);
    let p = release(&mut run.statement_results[0]);
    assert_eq!(p.dom_proofs.len(), 4);
    assert_eq!(p.dom_stores.len(), 4);
    assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 1);
    super::compile_run(&run, &compiler, "named_invertible_rank").unwrap();
}

#[test]
fn invertible_rank_requires_each_original_premise_id_order_carrier_and_dimension() {
    for change in [
        "missing",
        "extra",
        "order",
        "id",
        "duplicate",
        "carrier",
        "dimension",
    ] {
        let (mut run, compiler) = super::execute(NATIVE);
        let p = selected(&mut run.statement_results[0], 0);
        match change {
            "missing" => {
                p.requirement_proofs.pop();
            }
            "extra" => p.requirements.push(p.requirements[0].clone()),
            "order" => p.requirement_proofs.swap(0, 1),
            "id" | "duplicate" => {
                let id = if change == "id" {
                    FactId::new(u64::MAX)
                } else {
                    p.requirements[0].fact_id()
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[1] else {
                    panic!()
                };
                f.fact_id = id;
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[2] else {
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
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn invertible_rank_requires_original_guard_without_borrowing_parent_rank_wd() {
    for change in ["missing", "id", "matrix", "order", "zero", "citation"] {
        let (mut run, compiler) = super::execute(NATIVE);
        super::compile_run(&run, &compiler, "original_guard").unwrap();
        let p = selected(&mut run.statement_results[0], 0);
        if change == "missing" {
            p.requirement_proofs.pop();
        } else if change == "citation" {
            let a = super::atomic_proof_mut(&mut p.requirement_proofs[3]);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) = &mut a.searched_proof
            else {
                panic!("original nonzero citation")
            };
            c.cite_fact_id = FactId::new(u64::MAX);
        } else {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut p.requirements[3] else {
                panic!()
            };
            if change == "id" {
                f.fact_id = FactId::new(u64::MAX);
            } else if change == "zero" {
                f.right = super::number_object("1");
            } else {
                let Obj::MatrixOperator(MatrixOperator::Determinant(d)) = &mut f.left else {
                    panic!()
                };
                if change == "matrix" {
                    d.matrix = Box::new(super::number_object("7"));
                } else {
                    d.order = Box::new(super::number_object("7"));
                }
            }
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn invertible_rank_preserves_original_matrix_square_dimensions_endpoint_and_orientation() {
    for change in [
        "argument",
        "matrix",
        "rows",
        "cols",
        "endpoint",
        "orientation",
    ] {
        let (mut run, compiler) = super::execute(NATIVE);
        let p = selected(&mut run.statement_results[0], 0);
        match change {
            "argument" => p.arguments.swap(0, 1),
            "endpoint" => p.conclusion.right = super::number_object("7"),
            "orientation" => p.orientation = MatrixLawOrientation::Reverse,
            _ => {
                let Obj::MatrixOperator(MatrixOperator::Rank(r)) = &mut p.conclusion.left else {
                    panic!()
                };
                match change {
                    "matrix" => r.matrix = Box::new(super::number_object("7")),
                    "rows" => r.rows = Box::new(super::number_object("7")),
                    _ => r.cols = Box::new(super::number_object("7")),
                }
            }
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn invertible_rank_validates_selected_theorem_instead_of_equal_arity_subjects() {
    let (mut run, _) = super::execute(NATIVE);
    let p = selected(&mut run.statement_results[0], 0);
    assert!(validate_rank_invertible_law(
        BuiltinTheoremId::MatrixDetTranspose,
        &p.arguments,
        &p.requirements,
        &p.conclusion
    )
    .is_err());
}

#[test]
fn invertible_rank_requires_original_rank_constructor_children_and_requirements() {
    for change in ["child", "requirement"] {
        let (mut run, compiler) = super::execute(NATIVE);
        let p = super::equality_proof_mut(
            &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                .verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Rank(
                    r,
                )),
            ..
        } = p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("original rank WD")
        };
        assert_eq!(r.requirement_fact_verified.len(), 3);
        if change == "child" {
            r.child_obj_well_defined.pop();
        } else {
            r.requirement_fact_verified.pop();
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn explicit_invertible_rank_requires_four_original_stages_conclusion_and_publication() {
    for change in [
        "proof",
        "proof_order",
        "store",
        "id",
        "argument",
        "theorem",
        "wd",
        "conclusion",
        "publication",
        "formation",
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
            "id" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[1]
                else {
                    panic!()
                };
                f.fact_id = FactId::new(u64::MAX);
            }
            "argument" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "theorem" => p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::MatrixRankIdentity,
            "wd" => {
                p.conclusions_wd.pop();
            }
            "conclusion" => {
                p.builtin.as_mut().unwrap().conclusions.pop();
            }
            "publication" => {
                p.stored.pop();
            }
            "formation" => {
                p.stored_wd.pop();
            }
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn invertible_rank_endpoint_transport_requires_the_original_equality_citation() {
    let (mut run, compiler) = super::execute(TRANSPORT);
    super::compile_run(&run, &compiler, "rank_endpoint").unwrap();
    let p = selected(&mut run.statement_results[0], 0);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = p.right_equal.as_mut()
    else {
        panic!("original endpoint equality path")
    };
    assert!(!path.path.is_empty());
    path.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_rank_endpoint").is_err());
}

#[test]
fn invertible_rank_retains_the_executed_real_to_complex_intermediate() {
    let (mut run, compiler) = super::execute(REAL);
    super::compile_run(&run, &compiler, "original_real_rank").unwrap();
    super::forall_proof_mut(&mut run.statement_results[0])
        .proved_then_facts
        .remove(0);
    assert!(super::compile_run(&run, &compiler, "skipped_rank_carrier").is_err());
}

#[test]
fn invertible_rank_guard_transport_requires_original_nonzero_and_equality_citations() {
    for change in ["nonzero", "equality"] {
        let (mut run, compiler) = super::execute(GUARD);
        super::compile_run(&run, &compiler, "original_transported_rank_guard").unwrap();
        let p = selected(&mut run.statement_results[0], 0);
        let a = super::atomic_proof_mut(&mut p.requirement_proofs[3]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) = &mut a.searched_proof
        else {
            panic!("original transported scalar nonzero citation")
        };
        if change == "nonzero" {
            c.cite_fact_id = FactId::new(u64::MAX);
        } else {
            let path = c
                .why_parameters_of_known_fact_are_equal_to_givens
                .iter_mut()
                .find_map(|p| match p {
                    EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                    ) => Some(path),
                    _ => None,
                })
                .expect("original determinant equality");
            assert!(!path.path.is_empty());
            path.path[0].2 = FactId::new(u64::MAX);
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}
