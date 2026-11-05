use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::TrigOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

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
    for source in ["sin(i) $in R", "tan(pi/2) $in R", "cot(pi) $in R"] {
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
    for (source, change_value) in ["sin(pi/2)=1", "cot(pi/3)=sqrt(3)/3"]
        .into_iter()
        .flat_map(|source| [false, true].map(|change| (source, change)))
    {
        let (mut run, compiler) = super::execute(source);
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

#[test]
fn integer_periodic_source_rejects_noninteger_offsets_and_poles() {
    for source in [
        "forall k R:\n    sin(2*k*pi+pi/6)=1/2",
        "forall k Z:\n    sin(k*pi+pi/6)=1/2",
        "forall k Z:\n    tan(k*pi+pi/2) $in R",
        "forall k Z:\n    cot(k*pi) $in R",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn integer_periodic_nonzero_requires_original_integer_facts() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule;
    for operation in ["tan", "cot", "sec", "csc"] {
        for mutation in 0..4 {
            let source = format!("have k Z\nlet value={operation}(k*pi+pi/7)");
            let (mut run, compiler) = super::execute(&source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
            )) = &mut run.statement_results[1]
            else {
                panic!()
            };
            let Some(DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::TrigOperator(p),
                ..
            }) = p.value_well_defined.as_detailed_success_mut().unwrap()
            else {
                panic!()
            };
            let requirements = match p {
                TrigOperatorObjWellDefinedProofByDef::Tan(p) => &mut p.requirement_fact_verified,
                TrigOperatorObjWellDefinedProofByDef::Cot(p) => &mut p.requirement_fact_verified,
                TrigOperatorObjWellDefinedProofByDef::Sec(p) => &mut p.requirement_fact_verified,
                TrigOperatorObjWellDefinedProofByDef::Csc(p) => &mut p.requirement_fact_verified,
                _ => panic!(),
            };
            let atomic = super::atomic_proof_mut(&mut requirements[1]);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::PeriodicTrigNonzero(p),
                ),
            ) = &mut atomic.searched_proof
            else {
                panic!("original periodic nonzero route")
            };
            if mutation == 0 {
                p.integer_requirements.clear();
            } else if mutation == 3 {
                p.coefficient = EvalRational::new(0, 1).unwrap().to_obj();
            } else {
                let AtomicFact::InFact(fact) =
                    &mut super::atomic_proof_mut(&mut p.integer_requirements[0]).fact
                else {
                    panic!()
                };
                if mutation == 1 {
                    fact.set = Obj::StandardSet(StandardSet::R);
                } else {
                    fact.element = EvalRational::new(7, 1).unwrap().to_obj();
                }
            }
            compiler
                .compile_run(&run, "bad_integer_nonzero")
                .expect_err("nonzero WD must retain every original integer premise");
        }
    }
}

#[test]
fn rational_angle_closed_certificate_rejects_wrong_coefficient_or_extra_premise() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule;
    for operation in ["sin", "cos"] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(&format!("{operation}(pi/7)!=0"));
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) =
                &mut run.statement_results[0]
            else {
                panic!()
            };
            let atomic = super::atomic_proof_mut(&mut result.verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::PeriodicTrigNonzero(proof),
                ),
            ) = &mut atomic.searched_proof
            else {
                panic!("original closed nonzero route")
            };
            assert!(proof.integer_requirements.is_empty());
            if mutation == 2 {
                let (mut unrelated, _) = super::execute("0 $in Z");
                let ExecStmtResult::Fact(ExecFactStmtResult::Success(result)) =
                    unrelated.statement_results.remove(0)
                else {
                    panic!()
                };
                proof.integer_requirements.push(result.verify_result);
            } else {
                proof.coefficient = EvalRational::new(1, if mutation == 0 { 2 } else { 3 })
                    .unwrap()
                    .to_obj();
            }
            compiler.compile_run(&run, "bad_closed_nonzero").expect_err(
                "closed nonzero proof must match the original angle and empty period requirements",
            );
        }
    }
}

#[test]
fn rational_angle_source_rejects_poles_and_noninteger_periods() {
    for source in [
        "sin(pi)!=0",
        "cos(pi/2)!=0",
        "tan(pi/2) $in R",
        "cot(pi) $in R",
        "sec(pi/2) $in R",
        "csc(pi) $in R",
        "forall k R:\n    tan(k*pi+pi/7) $in R",
        "forall k Z:\n    sec((2*k+1)*pi/2) $in R",
        "forall k Z:\n    csc(k*pi) $in R",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
