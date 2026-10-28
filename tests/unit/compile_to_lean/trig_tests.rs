use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::TrigOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

#[test]
fn trig_examples_compile_original_wd_and_selected_rules() {
    for source in [
        include_str!("../../../lean/examples/trigonometric_periodic_values/statement.lit"),
        include_str!("../../../lean/examples/trigonometric_special_values/statement.lit"),
        include_str!("../../../lean/examples/trigonometric_real_output/statement.lit"),
        include_str!("../../../lean/examples/trigonometric_pythagorean/statement.lit"),
        include_str!("../../../lean/examples/tangent_quotient/statement.lit"),
        include_str!("../../../lean/examples/trigonometric_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "trig").unwrap();
    }
}

#[test]
fn trig_wd_rejects_missing_or_altered_evidence() {
    for source in [
        "let value = sin(0)",
        "let value = cos(0)",
        "let value = tan(0)",
    ] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
            )) = &mut run.statement_results[0]
            else {
                panic!()
            };
            let Some(DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::TrigOperator(p),
                ..
            }) = (&mut p.value_well_defined)
                .as_detailed_success_mut()
                .unwrap()
            else {
                panic!()
            };
            let (children, requirements) = match p {
                TrigOperatorObjWellDefinedProofByDef::Sin(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Cos(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Tan(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!(),
            };
            match mutation {
                0 => children.clear(),
                1 => {
                    requirements.pop();
                }
                2 => {
                    let AtomicFact::InFact(f) =
                        &mut super::atomic_proof_mut(&mut requirements[0]).fact
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
                _ => unreachable!(),
            }
            assert!(compiler.compile_run(&run, "bad_trig").is_err());
        }
    }
}

#[test]
fn trig_source_domains_reject_complex_and_tangent_poles() {
    for source in ["sin(i) $in R", "tan(pi/2) $in R"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn trig_periodic_certificate_rejects_changed_coefficient_and_value() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof;
    for change_value in [false, true] {
        let (mut run, compiler) = super::execute("sin(pi/2)=1");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let p = super::equality_proof_mut(&mut p.verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::TrigComplexIdentity(
                TrigComplexIdentityProof::PeriodicTrig(p),
            ),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        if change_value {
            p.value = EvalRational::new(0, 1).unwrap().to_obj();
        } else {
            p.coefficient = EvalRational::new(0, 1).unwrap().to_obj();
        }
        assert!(compiler.compile_run(&run, "bad_period").is_err());
    }
}

#[test]
fn tangent_wd_rejects_wrong_nonzero_subject() {
    let (mut run, compiler) = super::execute("let value = tan(0)");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Tan(p)),
        ..
    }) = (&mut p.value_well_defined)
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!()
    };
    let AtomicFact::NotEqualFact(f) =
        &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[1]).fact
    else {
        panic!()
    };
    f.right = EvalRational::new(1, 1).unwrap().to_obj();
    assert!(compiler.compile_run(&run, "bad_tangent").is_err());
}
