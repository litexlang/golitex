use crate::execute::execute_def_thm_stmt::{
    ExecDefThmBodyProof, ExecDefThmForallProof, ExecDefThmStmtResult, ExecDefThmStmtSuccess,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferFunctionContinuousAtDefinitionResult,
    InferFunctionContinuousAtFactResult, InferResult,
};

const SOURCES: [&str; 5] = [
    include_str!("../../../lean/examples/function_continuity_at_citations/statement.lit"),
    include_str!("../../../lean/examples/function_continuity_left_citations/statement.lit"),
    include_str!("../../../lean/examples/function_continuity_right_citations/statement.lit"),
    include_str!("../../../lean/examples/function_continuity_semantic_transport/statement.lit"),
    include_str!("../../../lean/examples/function_continuity_guarded_citations/statement.lit"),
];
fn theorem(run: &mut RunLitexCodeResult) -> &mut ExecDefThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    p
}
fn body(p: &mut ExecDefThmStmtSuccess) -> &mut ExecDefThmForallProof {
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    p
}
fn definition(p: &mut ExecDefThmForallProof) -> &mut InferFunctionContinuousAtDefinitionResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionContinuousAtFact(rules))) =
        &mut p.assumed_dom_facts[0].store_and_infer.infer
    else {
        panic!("continuity inference")
    };
    let [InferFunctionContinuousAtFactResult::Definition(p)] = rules.as_mut_slice() else {
        panic!("definition")
    };
    p
}
#[test]
fn continuity_citations_keep_polarity_side_domain_and_semantic_equality() {
    for source in SOURCES {
        let (run, c) = super::execute(source);
        let lean = c.compile_run(&run, "continuity").unwrap();
        assert!(lean.contains("Litex.FunctionContinuousAt"));
        assert!(lean.contains("Litex.functionContinuousAtControl"));
    }
}
#[test]
fn continuity_definition_rejects_missing_or_changed_domain_evidence() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let p = definition(body(theorem(&mut run)));
        match mutation {
            0 => p.source_fact_id = p.derived[0].primary_fact_id(),
            1 => p.derived.clear(),
            2 => p.function_domain.domain = Obj::StandardSet(StandardSet::C),
            _ => {
                let VerifyFactResult::AtomicExceptEquality(proof) =
                    p.function_domain.input_real.as_mut()
                else {
                    panic!("subset proof")
                };
                let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
                    panic!("success")
                };
                let AtomicFact::SubsetFact(f) = &mut proof.fact else {
                    panic!("subset")
                };
                f.right = Obj::StandardSet(StandardSet::C);
            }
        }
        c.compile_run(&run, "changed_continuity_domain")
            .expect_err("exact original domain evidence");
    }
}
#[test]
fn continuity_requires_original_point_membership() {
    let (mut run, c) = super::execute(SOURCES[0]);
    let FactWellDefinedProof::AtomicExceptEquality(proof) =
        &mut body(theorem(&mut run)).assumed_dom_facts[0].well_defined
    else {
        panic!("continuity WD")
    };
    let PredicateDomainProof::FunctionAnalysis(p) =
        &mut proof.as_detailed_mut().unwrap().predicate_domain
    else {
        panic!("analysis WD")
    };
    p.requirements.clear();
    c.compile_run(&run, "missing_continuity_point")
        .expect_err("original point membership");
}

const LAWS: [&str; 7] = [
    include_str!(
        "../../../lean/examples/function_continuity_at_from_epsilon_by_theorem/statement.lit"
    ),
    include_str!("../../../lean/examples/function_continuity_at_control_by_theorem/statement.lit"),
    include_str!(
        "../../../lean/examples/function_continuity_left_from_epsilon_by_theorem/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/function_continuity_left_control_by_theorem/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/function_continuity_right_from_epsilon_by_theorem/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/function_continuity_right_control_by_theorem/statement.lit"
    ),
    include_str!("../../../lean/examples/function_continuity_at_definition/statement.lit"),
];
const FORMULAS: [&str; 6] = [
    include_str!("../../../lean/examples/function_continuity_at_constant_by_theorem/statement.lit"),
    include_str!("../../../lean/examples/function_continuity_at_identity_by_theorem/statement.lit"),
    include_str!(
        "../../../lean/examples/function_continuity_left_constant_by_theorem/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/function_continuity_left_identity_by_theorem/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/function_continuity_right_constant_by_theorem/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/function_continuity_right_identity_by_theorem/statement.lit"
    ),
];
#[test]
fn continuity_constant_and_identity_replay_the_source_formula() {
    for source in FORMULAS {
        let (run, c) = super::execute(source);
        let lean = c.compile_run(&run, "formula_continuity").unwrap();
        assert!(
            lean.contains("Litex.functionContinuousAtOfConstant")
                || lean.contains("Litex.functionContinuousAtOfIdentity")
        );
    }
}
#[test]
fn continuity_epsilon_definitions_and_explicit_certificates_replay() {
    for source in LAWS {
        let (run, c) = super::execute(source);
        let output = c.compile_run(&run, "continuity_laws").unwrap();
        assert!(
            output.contains("Litex.functionContinuousAtOfForall")
                || output.contains("Litex.functionContinuousAtControl")
        );
    }
}
#[test]
fn continuity_certificates_reject_changed_side_point_or_missing_stage() {
    for source in LAWS[..6].iter().chain(FORMULAS.iter()) {
        for mutation in 0..6 {
            let (mut run, c) = super::execute(source);
            use crate::execute::{
                execute_by_stmt::{
                    ExecByStmtResult, ExecByThmStmtResult, ExecReleaseThmStmtResult,
                },
                ExecReleaseAndExpandStmtResult,
            };
            let (dom_proofs, dom_stores, conclusions_wd, derivation, builtin) =
                match &mut body(theorem(&mut run)).proof_steps[0] {
                    ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => (
                        &mut p.dom_proofs,
                        &mut p.dom_stores,
                        &mut p.conclusions_wd,
                        &mut p.theorem_derivation,
                        p.builtin.as_mut().unwrap(),
                    ),
                    ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                        ExecReleaseThmStmtResult::Success(p),
                    )) => (
                        &mut p.dom_proofs,
                        &mut p.dom_stores,
                        &mut p.conclusions_wd,
                        &mut p.theorem_derivation,
                        p.builtin.as_mut().unwrap(),
                    ),
                    _ => panic!("builtin call"),
                };
            match mutation {
                0 => {
                    dom_proofs.pop();
                }
                1 => dom_stores.clear(),
                2 => conclusions_wd.clear(),
                3 => {
                    *derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
                4 => {
                    let b = builtin;
                    use crate::builtin_theorem::BuiltinTheoremId::*;
                    let f = if matches!(
                        b.theorem,
                        FnContinuousAtControl | FnContinuousLeftControl | FnContinuousRightControl
                    ) {
                        &mut b.requirements[4]
                    } else {
                        &mut b.conclusions[0]
                    };
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) = f else {
                        panic!("continuity")
                    };
                    f.side = if f.side == RealApproachSide::Both {
                        RealApproachSide::Left
                    } else {
                        RealApproachSide::Both
                    };
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut builtin.requirements[3]
                    else {
                        panic!("point domain")
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
            }
            c.compile_run(&run, "changed_continuity_certificate")
                .expect_err("original stages, point and approach side");
        }
    }
}
