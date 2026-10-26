use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::TrigOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

#[test]
fn inverse_trig_examples_replay_original_results() {
    for source in [
        include_str!("../../../lean/examples/inverse_trigonometric_values/statement.lit"),
        include_str!("../../../lean/examples/inverse_trigonometric_left_inverses/statement.lit"),
        include_str!("../../../lean/examples/inverse_trigonometric_domains/statement.lit"),
        include_str!("../../../lean/examples/reciprocal_trigonometric_definitions/statement.lit"),
        include_str!("../../../lean/examples/reciprocal_trigonometric_values/statement.lit"),
        include_str!("../../../lean/examples/inverse_trigonometric_functions/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "inverse_trig")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn inverse_trig_wd_rejects_missing_or_altered_evidence() {
    for expression in [
        "arcsin(0)",
        "arccos(0)",
        "arctan(0)",
        "arccot(0)",
        "sec(0)",
        "csc(pi/2)",
        "cot(pi/2)",
        "tan(arctan(0))",
        "sec(arctan(0))",
        "cot(arccot(0))",
        "csc(arccot(0))",
    ] {
        let (valid, compiler) = super::execute(&format!("let value = {expression}"));
        compiler.compile_run(&valid, "valid_inverse_wd").unwrap();
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(&format!("let value = {expression}"));
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
            )) = &mut run.statement_results[0]
            else {
                panic!()
            };
            let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::TrigOperator(p),
                ..
            }) = &mut p.value_well_defined
            else {
                panic!()
            };
            let (children, requirements) = match p {
                TrigOperatorObjWellDefinedProofByDef::Arcsin(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Arccos(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Arctan(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Arccot(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Sec(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Csc(p) => (
                    &mut p.child_obj_well_defined,
                    &mut p.requirement_fact_verified,
                ),
                TrigOperatorObjWellDefinedProofByDef::Cot(p) => (
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
            assert!(
                compiler.compile_run(&run, "bad_inverse_wd").is_err(),
                "{expression}, {mutation}"
            );
        }
    }
}

#[test]
fn inverse_trig_bounds_and_reciprocal_guards_keep_their_subjects() {
    for expression in ["arcsin(0)", "arccos(0)", "sec(0)", "csc(pi/2)", "cot(pi/2)"] {
        let (mut run, compiler) = super::execute(&format!("let value = {expression}"));
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::TrigOperator(p),
            ..
        }) = &mut p.value_well_defined
        else {
            panic!()
        };
        let requirements = match p {
            TrigOperatorObjWellDefinedProofByDef::Arcsin(p) => &mut p.requirement_fact_verified,
            TrigOperatorObjWellDefinedProofByDef::Arccos(p) => &mut p.requirement_fact_verified,
            TrigOperatorObjWellDefinedProofByDef::Sec(p) => &mut p.requirement_fact_verified,
            TrigOperatorObjWellDefinedProofByDef::Csc(p) => &mut p.requirement_fact_verified,
            TrigOperatorObjWellDefinedProofByDef::Cot(p) => &mut p.requirement_fact_verified,
            _ => panic!(),
        };
        match &mut super::atomic_proof_mut(&mut requirements[1]).fact {
            AtomicFact::LessEqualFact(f) => f.left = EvalRational::new(-2, 1).unwrap().to_obj(),
            AtomicFact::NotEqualFact(f) => f.left = EvalRational::new(1, 1).unwrap().to_obj(),
            _ => panic!(),
        }
        assert!(compiler.compile_run(&run, "bad_inverse_guard").is_err());
    }
}

#[test]
fn inverse_trig_source_rejects_outside_domain_and_poles() {
    for source in [
        "arcsin(2) $in R",
        "arccos(-2) $in R",
        "arctan(i) $in R",
        "arccot(i) $in R",
        "sec(pi/2) $in R",
        "csc(0) $in R",
        "cot(0) $in R",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}

#[test]
fn inverse_trig_exact_rule_cannot_be_replaced_by_another_value() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::ArcsinExactOneBuiltinRuleProof;
    let (mut run, compiler) = super::execute("arcsin(0)=0");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0] else {
        panic!()
    };
    let p = super::equality_proof_mut(&mut p.verify_result);
    assert!(matches!(
        &p.searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArcsinExactZero(_))
    ));
    p.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ArcsinExactOne(ArcsinExactOneBuiltinRuleProof {}),
    );
    assert!(compiler.compile_run(&run, "bad_inverse_rule").is_err());
}
