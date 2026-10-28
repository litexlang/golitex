use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ComplexOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

#[test]
fn complex_observation_examples_replay_original_results() {
    for source in [
        include_str!("../../../lean/examples/complex_observation_values/statement.lit"),
        include_str!("../../../lean/examples/complex_observation_codomain/statement.lit"),
        include_str!("../../../lean/examples/complex_coordinate_reconstruction/statement.lit"),
        include_str!("../../../lean/examples/complex_conjugation_laws/statement.lit"),
        include_str!("../../../lean/examples/complex_modulus_laws/statement.lit"),
        include_str!("../../../lean/examples/complex_observation_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "complex_observation").unwrap();
    }
}

#[test]
fn complex_wd_rejects_missing_or_wrong_carrier_evidence() {
    for operation in ["conj", "re", "img", "C_abs"] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(&format!("let value = {operation}(i)"));
            let (children, requirements) = wd_stages(&mut run);
            match mutation {
                0 => children.clear(),
                1 => requirements.clear(),
                2 => {
                    let AtomicFact::InFact(f) =
                        &mut super::atomic_proof_mut(&mut requirements[0]).fact
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::R);
                }
                _ => unreachable!(),
            }
            assert!(compiler.compile_run(&run, "bad_complex_wd").is_err());
        }
    }
}

#[test]
fn complex_closed_values_reject_a_tampered_result() {
    for source in ["re(i)=0", "C_abs(3+4*i)=5"] {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let p = super::equality_proof_mut(&mut p.verify_result);
        let EqualFactSearchedProof::ByClosedCalculation(p) = &mut p.searched_proof else {
            panic!()
        };
        p.values = ClosedValuePair::Rational {
            left: EvalRational::new(9, 1).unwrap(),
            right: EvalRational::new(9, 1).unwrap(),
        };
        assert!(compiler
            .compile_run(&run, "bad_complex_calculation")
            .is_err());
    }
}

#[test]
fn complex_operators_reject_set_arguments() {
    for operation in ["conj", "re", "img", "C_abs"] {
        let source = format!("{operation}({{1}}) $in C");
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

fn wd_stages(
    run: &mut RunLitexCodeResult,
) -> (
    &mut Vec<Box<ObjWellDefinedProof>>,
    &mut Vec<VerifyFactResult>,
) {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ComplexOperator(p),
        ..
    }) = (&mut p.value_well_defined)
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!()
    };
    match p {
        ComplexOperatorObjWellDefinedProofByDef::Conjugate(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ComplexOperatorObjWellDefinedProofByDef::RealPart(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ComplexOperatorObjWellDefinedProofByDef::ImaginaryPart(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        ComplexOperatorObjWellDefinedProofByDef::ComplexAbs(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
    }
}

#[test]
fn conjugation_rejects_a_different_recorded_identity() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_conjugation::{ConjugationEqualityProof,ConjugateRealPartProof};
    let (mut run, compiler) = super::execute("have z C\nconj(conj(z)) = z\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    let p = super::equality_proof_mut(&mut p.verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Conjugation(rule)) =
        &mut p.searched_proof
    else {
        panic!()
    };
    assert!(matches!(
        rule,
        ConjugationEqualityProof::ConjugateInvolution(_)
    ));
    *rule = ConjugationEqualityProof::ConjugateRealPart(ConjugateRealPartProof);
    assert!(compiler
        .compile_run(&run, "wrong_conjugation_rule")
        .is_err());
}
