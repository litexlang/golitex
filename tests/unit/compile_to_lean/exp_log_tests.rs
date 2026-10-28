use crate::execute::execute_fact_stmt::verify_atomic_fact::closed_calculation_proof::ClosedValuePair;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ExpLogOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

#[test]
fn exp_log_examples_compile_with_original_objects_and_rules() {
    for source in [
        include_str!("../../../lean/examples/exponential_logarithm_inverse/statement.lit"),
        include_str!("../../../lean/examples/positive_mathematical_constants/statement.lit"),
        include_str!("../../../lean/examples/logarithm_real_output/statement.lit"),
        include_str!("../../../lean/examples/exponential_logarithm_values/statement.lit"),
        include_str!("../../../lean/examples/logarithm_unit_identities/statement.lit"),
        include_str!("../../../lean/examples/exponential_logarithm_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler.compile_run(&run, "exp_log").is_ok());
    }
}

#[test]
fn exp_ln_wd_rejects_missing_or_changed_carrier_proofs() {
    for source in ["let value = exp(0)\n", "let value = ln(1)\n"] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let (children, requirements) = match let_wd(&mut run) {
                ExpLogOperatorObjWellDefinedProofByDef::Exp(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                ExpLogOperatorObjWellDefinedProofByDef::Ln(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                _ => panic!(),
            };
            match mutation {
                0 => children.clear(),
                1 => requirements.clear(),
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
            assert!(compiler.compile_run(&run, "bad_exp_ln").is_err());
        }
    }
}

#[test]
fn log_wd_rejects_missing_reordered_and_wrong_base_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute("let value = log(2, 8)\n");
        let ExpLogOperatorObjWellDefinedProofByDef::Log(p) = let_wd(&mut run) else {
            panic!()
        };
        match mutation {
            0 => p.child_obj_well_defined.clear(),
            1 => p.child_obj_well_defined.swap(0, 1),
            2 => p.requirement_fact_verified.clear(),
            3 => p.requirement_fact_verified.swap(2, 3),
            4 => {
                let AtomicFact::NotEqualFact(f) =
                    &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[4]).fact
                else {
                    panic!()
                };
                f.right = Obj::Literal(Literal::Number(Number::new("0".into())));
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_log_wd").is_err());
    }
}

#[test]
fn exp_ln_inverse_requires_the_recorded_positive_premise() {
    let (mut run, compiler) = super::execute(
        "have positive_argument R+\nexp(ln(positive_argument)) = positive_argument\n",
    );
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    let p = super::equality_proof_mut(&mut p.verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ExpOfLn(p)) =
        &mut p.searched_proof
    else {
        panic!()
    };
    p.proof_of_requirement_facts.clear();
    assert!(compiler
        .compile_run(&run, "missing_inverse_premise")
        .is_err());
}

#[test]
fn exp_log_closed_calculation_rejects_a_changed_result() {
    for source in ["exp(0) = 1", "log(8, 4) = 2 / 3"] {
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
            left: EvalRational::new(7, 1).unwrap(),
            right: EvalRational::new(7, 1).unwrap(),
        };
        assert!(compiler.compile_run(&run, "changed_calculation").is_err());
    }
}

#[test]
fn exp_log_source_domains_remain_rejected() {
    for source in [
        "ln(0) $in R",
        "log(1, 2) $in R",
        "log(-2, 4) $in R",
        "exp(i) $in R",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}

fn let_wd(run: &mut RunLitexCodeResult) -> &mut ExpLogOperatorObjWellDefinedProofByDef {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ExpLogOperator(p),
        ..
    }) = (&mut p.value_well_defined)
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!()
    };
    p
}
