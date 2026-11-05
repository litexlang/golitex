use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::compile_builtin_matrix_power_theorem::validate_matrix_power_law;
use crate::compile_to_lean::compile_frobenius_scale_law::validate_frobenius_scale_law;
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_native_matrix_laws::{MatrixLawApplicationProof, MatrixLawOrientation, NativeMatrixLawProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const POWER: &str = r#"# Natural matrix powers add exponents by multiplying the powers.
forall replay_power_n, replay_power_p, replay_power_q N, replay_power_A matrix(C,replay_power_n,replay_power_n):
    matrix_power(replay_power_A,replay_power_n,replay_power_p+replay_power_q) = matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,replay_power_q),replay_power_n,replay_power_n,replay_power_n)
"#;
const NORM: &str = r#"# The Frobenius norm scales by the complex magnitude of the scalar.
forall replay_frob_m, replay_frob_n N, replay_frob_z C, replay_frob_A matrix(C,replay_frob_m,replay_frob_n):
    frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,replay_frob_m,replay_frob_n),replay_frob_m,replay_frob_n) = C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,replay_frob_m,replay_frob_n)
"#;
const REPEATED: &str = r#"# Multiplying equal powers doubles the natural exponent.
forall replay_power_n, replay_power_p N, replay_power_A matrix(C,replay_power_n,replay_power_n):
    matrix_power(replay_power_A,replay_power_n,replay_power_p+replay_power_p) = matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,replay_power_p),replay_power_n,replay_power_n,replay_power_n)
"#;
const REVERSE: &str = r#"# Reverse both power-addition and Frobenius-scaling equalities.
forall replay_power_n, replay_power_p, replay_power_q N, replay_power_A matrix(C,replay_power_n,replay_power_n):
    matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,replay_power_q),replay_power_n,replay_power_n,replay_power_n) = matrix_power(replay_power_A,replay_power_n,replay_power_p+replay_power_q)
forall replay_frob_m, replay_frob_n N, replay_frob_z C, replay_frob_A matrix(C,replay_frob_m,replay_frob_n):
    C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,replay_frob_m,replay_frob_n) = frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,replay_frob_m,replay_frob_n),replay_frob_m,replay_frob_n)
"#;
const ZERO: &str = r#"# Power addition and Frobenius scaling retain zero exponents, dimensions and scalar.
forall replay_power_n, replay_power_q N, replay_power_A matrix(C,replay_power_n,replay_power_n):
    matrix_power(replay_power_A,replay_power_n,0+replay_power_q) = matrix_mul(matrix_power(replay_power_A,replay_power_n,0),matrix_power(replay_power_A,replay_power_n,replay_power_q),replay_power_n,replay_power_n,replay_power_n)
forall replay_power_n, replay_power_p N, replay_power_A matrix(C,replay_power_n,replay_power_n):
    matrix_power(replay_power_A,replay_power_n,replay_power_p+0) = matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,0),replay_power_n,replay_power_n,replay_power_n)
forall replay_power_p, replay_power_q N, replay_power_A matrix(C,0,0):
    matrix_power(replay_power_A,0,replay_power_p+replay_power_q) = matrix_mul(matrix_power(replay_power_A,0,replay_power_p),matrix_power(replay_power_A,0,replay_power_q),0,0,0)
forall replay_frob_n N, replay_frob_z C, replay_frob_A matrix(C,0,replay_frob_n):
    frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,0,replay_frob_n),0,replay_frob_n) = C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,0,replay_frob_n)
forall replay_frob_m N, replay_frob_z C, replay_frob_A matrix(C,replay_frob_m,0):
    frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,replay_frob_m,0),replay_frob_m,0) = C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,replay_frob_m,0)
forall replay_frob_m, replay_frob_n N, replay_frob_A matrix(C,replay_frob_m,replay_frob_n):
    frobenius_norm(matrix_scale(0,replay_frob_A,replay_frob_m,replay_frob_n),replay_frob_m,replay_frob_n) = C_abs(0)*frobenius_norm(replay_frob_A,replay_frob_m,replay_frob_n)
"#;
const REAL: &str = r#"# Prove complex carriers explicitly for real matrices and scalars before using the laws.
forall replay_power_n, replay_power_p, replay_power_q N, replay_power_A matrix(R,replay_power_n,replay_power_n):
    replay_power_A $in matrix(C,replay_power_n,replay_power_n)
    matrix_power(replay_power_A,replay_power_n,replay_power_p+replay_power_q) = matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,replay_power_q),replay_power_n,replay_power_n,replay_power_n)
forall replay_frob_m, replay_frob_n N, replay_frob_z R, replay_frob_A matrix(R,replay_frob_m,replay_frob_n):
    replay_frob_z $in C
    replay_frob_A $in matrix(C,replay_frob_m,replay_frob_n)
    frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,replay_frob_m,replay_frob_n),replay_frob_m,replay_frob_n) = C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,replay_frob_m,replay_frob_n)
"#;
const TRANSPORT: &str = r#"# An assumed canonical endpoint equality transports each original selected law.
forall replay_power_n, replay_power_p, replay_power_q N, replay_power_A matrix(C,replay_power_n,replay_power_n), replay_power_D matrix(C,replay_power_n,replay_power_n):
    matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,replay_power_q),replay_power_n,replay_power_n,replay_power_n) = replay_power_D
    =>:
        matrix_power(replay_power_A,replay_power_n,replay_power_p+replay_power_q) = replay_power_D
forall replay_frob_m, replay_frob_n N, replay_frob_z C, replay_frob_A matrix(C,replay_frob_m,replay_frob_n), replay_frob_value R:
    C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,replay_frob_m,replay_frob_n) = replay_frob_value
    =>:
        frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,replay_frob_m,replay_frob_n),replay_frob_m,replay_frob_n) = replay_frob_value
"#;
const EXPLICIT_POWER: &str = r#"# Prove natural matrix powers add exponents by multiplying the powers.
thm replay_matrix_power_add:
    ? forall replay_power_n, replay_power_p, replay_power_q N, replay_power_A matrix(C,replay_power_n,replay_power_n):
        matrix_power(replay_power_A,replay_power_n,replay_power_p+replay_power_q) = matrix_mul(matrix_power(replay_power_A,replay_power_n,replay_power_p),matrix_power(replay_power_A,replay_power_n,replay_power_q),replay_power_n,replay_power_n,replay_power_n)
    release thm matrix_power_add(replay_power_A,replay_power_n,replay_power_p,replay_power_q)
release thm replay_matrix_power_add(2,3,4,zero_matrix(2,2))
"#;
const EXPLICIT_NORM: &str = r#"# Prove the Frobenius norm scales by the complex magnitude of the scalar.
thm replay_frobenius_norm_scale:
    ? forall replay_frob_m, replay_frob_n N, replay_frob_z C, replay_frob_A matrix(C,replay_frob_m,replay_frob_n):
        frobenius_norm(matrix_scale(replay_frob_z,replay_frob_A,replay_frob_m,replay_frob_n),replay_frob_m,replay_frob_n) = C_abs(replay_frob_z)*frobenius_norm(replay_frob_A,replay_frob_m,replay_frob_n)
    release thm frobenius_norm_scale(replay_frob_z,replay_frob_A,replay_frob_m,replay_frob_n)
release thm replay_frobenius_norm_scale(2,3,1+i,zero_matrix(2,3))
"#;

fn selected(statement: &mut ExecStmtResult, index: usize) -> &mut MatrixLawApplicationProof {
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(statement).proved_then_facts[index].verify_result,
    );
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::NativeMatrixLaw(
        law,
    )) = &mut eq.searched_proof
    else {
        panic!("actual selected power/Frobenius law")
    };
    match law {
        NativeMatrixLawProof::PowerAdd(p) => &mut p.application,
        NativeMatrixLawProof::FrobeniusNormScale(p) => &mut p.application,
        _ => panic!("actual addition/scaling variant"),
    }
}
fn release(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = statement
    else {
        panic!("named theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original release")
    };
    p
}

#[test]
fn native_power_frobenius_replays_actual_variants_reverse_zero_and_real_profiles() {
    for (source, count) in [(POWER, 5), (NORM, 4)] {
        let (mut run, compiler) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert_eq!(p.requirements.len(), count);
        assert_eq!(p.requirement_proofs.len(), count);
        super::compile_run(&run, &compiler, "native_power_frobenius").unwrap();
    }
    let (mut run, compiler) = super::execute(REVERSE);
    for statement in &mut run.statement_results {
        assert!(matches!(
            selected(statement, 0).orientation,
            MatrixLawOrientation::Reverse
        ));
    }
    super::compile_run(&run, &compiler, "reverse_power_frobenius").unwrap();
    let (run, compiler) = super::execute(ZERO);
    super::compile_run(&run, &compiler, "zero_power_frobenius").unwrap();
    let (mut run, compiler) = super::execute(REAL);
    selected(&mut run.statement_results[0], 1);
    selected(&mut run.statement_results[1], 2);
    super::compile_run(&run, &compiler, "real_power_frobenius").unwrap();
}

#[test]
fn native_power_frobenius_preserves_requirement_counts_order_ids_and_domains() {
    for source in [POWER, NORM] {
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
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.requirements[if source == POWER { 1 } else { 0 }]
                    else {
                        panic!()
                    };
                    f.fact_id = FactId::new(u64::MAX);
                }
                "carrier" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.requirements[if source == POWER { 4 } else { 3 }]
                    else {
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
fn power_add_requires_both_original_natural_exponent_proofs_even_for_identical_subjects() {
    for source in [POWER, REPEATED] {
        let (mut run, compiler) = super::execute(source);
        let p = selected(&mut run.statement_results[0], 0);
        assert_ne!(p.requirements[3].fact_id(), p.requirements[4].fact_id());
        if source == REPEATED {
            assert_eq!(p.requirements[3].ir(), p.requirements[4].ir());
            assert_eq!(p.arguments[2].ir(), p.arguments[3].ir());
        }
        super::compile_run(&run, &compiler, "original_exponent_stages").unwrap();
        for change in [
            "swap",
            "drop_left",
            "drop_right",
            "duplicate_id",
            "integer_only",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "swap" => p.requirement_proofs.swap(3, 4),
                "drop_left" => {
                    p.requirement_proofs.remove(3);
                }
                "drop_right" => {
                    p.requirement_proofs.remove(4);
                }
                "duplicate_id" => {
                    let id = p.requirements[3].fact_id();
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[4] else {
                        panic!()
                    };
                    f.fact_id = id;
                }
                "integer_only" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[4] else {
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
fn native_power_frobenius_preserves_exact_subjects_exponents_scalars_dimensions_and_orientation() {
    for source in [POWER, NORM] {
        for change in [
            "argument",
            "conclusion",
            "nested",
            "dimension",
            "orientation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = selected(&mut run.statement_results[0], 0);
            match change {
                "argument" => p.arguments.swap(0, 1),
                "conclusion" => p.conclusion.right = super::number_object("7"),
                "orientation" => p.orientation = MatrixLawOrientation::Reverse,
                "nested" | "dimension" => match &mut p.conclusion.left {
                    Obj::MatrixOperator(MatrixOperator::Power(a)) => {
                        if change == "dimension" {
                            a.order = Box::new(super::number_object("7"));
                        } else {
                            let Obj::ArithmeticOperator(ArithmeticOperator::Add(e)) =
                                a.exponent.as_mut()
                            else {
                                panic!()
                            };
                            e.right = Box::new(super::number_object("7"));
                        }
                    }
                    Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(a)) => {
                        if change == "dimension" {
                            a.cols = Box::new(super::number_object("7"));
                        } else {
                            let Obj::MatrixOperator(MatrixOperator::Scale(s)) = a.matrix.as_mut()
                            else {
                                panic!()
                            };
                            s.scalar = Box::new(super::number_object("7"));
                        }
                    }
                    _ => panic!("actual root"),
                },
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_power_frobenius_never_selects_another_contract_from_equal_argument_count() {
    let (mut run, _) = super::execute(POWER);
    let p = selected(&mut run.statement_results[0], 0);
    assert!(validate_frobenius_scale_law(
        BuiltinTheoremId::MatrixPowerAdd,
        &p.arguments,
        &p.requirements,
        &p.conclusion
    )
    .is_err());
    let (mut run, _) = super::execute(NORM);
    let p = selected(&mut run.statement_results[0], 0);
    assert!(validate_matrix_power_law(
        BuiltinTheoremId::FrobeniusNormScale,
        &p.arguments,
        &p.requirements,
        &p.conclusion
    )
    .is_err());
}

#[test]
fn explicit_power_frobenius_replays_original_stages_and_named_instantiations() {
    for (source, count) in [(EXPLICIT_POWER, 5), (EXPLICIT_NORM, 4)] {
        let (mut run, compiler) = super::execute(source);
        let p = release(&mut run.statement_results[0]);
        assert_eq!(p.dom_proofs.len(), count);
        assert_eq!(p.dom_stores.len(), count);
        assert_eq!(p.conclusions_wd.len(), 1);
        assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), 1);
        super::compile_run(&run, &compiler, "explicit_power_frobenius").unwrap();
    }
}

#[test]
fn explicit_power_frobenius_rejects_missing_or_changed_original_stages_and_contracts() {
    for source in [EXPLICIT_POWER, EXPLICIT_NORM] {
        for change in [
            "stores",
            "proof_order",
            "conclusion",
            "wd",
            "id",
            "arguments",
            "theorem",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = release(&mut run.statement_results[0]);
            match change {
                "stores" => {
                    p.dom_stores.pop();
                }
                "proof_order" => p.dom_proofs.swap(0, 1),
                "conclusion" => {
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
                "arguments" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                "theorem" => {
                    p.builtin.as_mut().unwrap().theorem = if source == EXPLICIT_POWER {
                        BuiltinTheoremId::FrobeniusNormScale
                    } else {
                        BuiltinTheoremId::MatrixPowerAdd
                    }
                }
                _ => unreachable!(),
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
}

#[test]
fn native_power_frobenius_requires_original_parent_and_nested_scale_constructor_wd() {
    for source in [POWER, NORM] {
        for change in ["child", "premise"] {
            let (mut run, compiler) = super::execute(source);
            let eq = super::equality_proof_mut(
                &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
                    .verify_result,
            );
            let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::MatrixOperator(root),
                ..
            } = wd.left.as_detailed_mut().unwrap()
            else {
                panic!()
            };
            let (children, requirements) = match root {
                MatrixOperatorObjWellDefinedProofByDef::Power(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                MatrixOperatorObjWellDefinedProofByDef::FrobeniusNorm(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!("actual root WD"),
            };
            if change == "child" {
                children.pop();
            } else {
                requirements.pop();
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
    let (mut run, compiler) = super::execute(NORM);
    let eq = super::equality_proof_mut(
        &mut super::forall_proof_mut(&mut run.statement_results[0]).proved_then_facts[0]
            .verify_result,
    );
    let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(
                MatrixOperatorObjWellDefinedProofByDef::FrobeniusNorm(p),
            ),
        ..
    } = wd.left.as_detailed_mut().unwrap()
    else {
        panic!()
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::MatrixOperator(MatrixOperatorObjWellDefinedProofByDef::Scale(s)),
        ..
    } = p.child_obj_well_defined[0].as_detailed_mut().unwrap()
    else {
        panic!("original scale WD")
    };
    s.requirement_fact_verified.remove(0);
    assert!(super::compile_run(&run, &compiler, "missing_original_scalar_C").is_err());
}

#[test]
fn native_power_frobenius_endpoint_transport_retains_original_assumption_citations() {
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
        super::compile_run(&run, &compiler, "original_power_frobenius_endpoint").unwrap();
        let p = selected(&mut run.statement_results[index], 0);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = p.right_equal.as_mut()
        else {
            panic!()
        };
        path.path[0].2 = FactId::new(u64::MAX);
        assert!(super::compile_run(&run, &compiler, "missing_original_endpoint").is_err());
    }
}

#[test]
fn native_power_frobenius_does_not_skip_executed_real_carrier_intermediates() {
    for (statement, count) in [(0, 1), (1, 2)] {
        for index in 0..count {
            let (mut run, compiler) = super::execute(REAL);
            super::compile_run(&run, &compiler, "original_real_carriers").unwrap();
            super::forall_proof_mut(&mut run.statement_results[statement])
                .proved_then_facts
                .remove(index);
            assert!(super::compile_run(&run, &compiler, "skipped_real_carrier").is_err());
        }
    }
}
