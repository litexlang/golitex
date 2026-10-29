use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    EqualFactSearchedProof, VerifyEqualityResult, VerifyEqualitySuccess,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
    verify_equality_by_builtin_rules::by_function_limit::FunctionLimitEqualityProof,
    EqualitySearchProofByBuiltinRule,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    DetailedObjWellDefinedProof, FunctionLimitApproachWellDefinedProof,
    FunctionLimitObjWellDefinedProof, LimitOperatorObjWellDefinedProofByDef,
    ObjWellDefinedProofByDef,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SELECTED: &str =
    include_str!("../../../lean/examples/function_limit_pos_infinity_selected/statement.lit");
const UNIQUE: &str =
    include_str!("../../../lean/examples/function_limit_pos_infinity_unique/statement.lit");

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        p,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut p.proof_steps[0] else {
        panic!("fact")
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!("verified")
    };
    p
}

fn limit_wd(run: &mut RunLitexCodeResult) -> &mut FunctionLimitObjWellDefinedProof {
    let wd = equality(run).well_defined_proof.as_detailed_mut().unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::LimitOperator(LimitOperatorObjWellDefinedProofByDef::Function(p)),
        ..
    } = wd.left.as_detailed_mut().unwrap()
    else {
        panic!("limit WD")
    };
    p
}

#[test]
fn infinity_limits_replay_both_directions_and_original_wd() {
    for source in [
        SELECTED,
        include_str!("../../../lean/examples/function_limit_neg_infinity_selected/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_infinity_exists/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_infinity_exists/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_infinity_real/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_infinity_real/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "infinite_limit").expect(source);
        assert!(lean.contains("Litex.infiniteFunctionLimit"));
        assert!(lean.contains("Litex.RealFunctionValue"));
        assert!(!lean.contains("sorry"));
    }
}

#[test]
fn infinity_limit_uniqueness_replays_both_original_candidates() {
    for source in [
        UNIQUE,
        include_str!("../../../lean/examples/function_limit_neg_infinity_unique/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "infinity_unique")
            .unwrap()
            .contains("Litex.infiniteFunctionLimitCandidatesEqual"));
    }
}

#[test]
fn infinity_limit_rejects_inconsistent_approach_wd() {
    let (mut run, compiler) = super::execute(SELECTED);
    limit_wd(&mut run).approach_wd = FunctionLimitApproachWellDefinedProof::AtNegativeInfinity;
    compiler
        .compile_run(&run, "wrong_wd_direction")
        .expect_err("original direction required");
}

#[test]
fn infinity_limit_rejects_inconsistent_real_approach_marker() {
    let (mut run, compiler) = super::execute(SELECTED);
    limit_wd(&mut run).approach_real = FunctionLimitApproachRealProof::AtNegativeInfinity;
    compiler
        .compile_run(&run, "wrong_real_direction")
        .expect_err("original direction required");
}

#[test]
fn infinity_limit_rejects_a_changed_candidate_direction() {
    let (mut run, compiler) = super::execute(SELECTED);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::FunctionLimit(
        FunctionLimitEqualityProof::SelectedValue(p),
    )) = &mut equality(&mut run).searched_proof
    else {
        panic!("selected")
    };
    let AtomicFact::HasFunctionLimitFact(f) = &mut p.candidate.fact else {
        panic!("candidate")
    };
    f.approach = LimitApproach::AtNegativeInfinity;
    compiler
        .compile_run(&run, "wrong_candidate_direction")
        .expect_err("original candidate required");
}

#[test]
fn infinity_limit_uniqueness_rejects_opposite_directions() {
    let (mut run, compiler) = super::execute(UNIQUE);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::FunctionLimit(
        FunctionLimitEqualityProof::Uniqueness(p),
    )) = &mut equality(&mut run).searched_proof
    else {
        panic!("unique")
    };
    let AtomicFact::HasFunctionLimitFact(f) = &mut p.right.fact else {
        panic!("candidate")
    };
    f.approach = LimitApproach::AtNegativeInfinity;
    compiler
        .compile_run(&run, "opposite_directions")
        .expect_err("common direction required");
}

const DEFINITION: &str =
    include_str!("../../../lean/examples/function_limit_pos_infinity_definition/statement.lit");

#[test]
fn infinity_limit_definition_replays_unboundedness_and_epsilon_control() {
    for source in [
        DEFINITION,
        include_str!("../../../lean/examples/function_limit_neg_infinity_definition/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_pos_infinity_guarded_definition/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/function_limit_neg_infinity_guarded_definition/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "infinite_definition")
            .unwrap()
            .contains("Litex.infiniteFunctionLimitOfForall"));
    }
}

#[test]
fn infinity_limit_definition_rejects_wrong_real_or_positive_binders() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(DEFINITION);
        let p = super::function_limit_tests::definition(&mut run);
        let Fact::ForallFact(f) = &mut p.requirement_facts[index] else {
            panic!("universal")
        };
        f.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(if index == 0 {
            StandardSet::RPos
        } else {
            StandardSet::R
        }));
        compiler
            .compile_run(&run, "wrong_infinity_binder")
            .expect_err("original binder domain required");
    }
}

#[test]
fn infinity_limit_definition_rejects_an_opposite_tail() {
    let (mut run, compiler) = super::execute(DEFINITION);
    let p = super::function_limit_tests::definition(&mut run);
    let Fact::ForallFact(f) = &mut p.requirement_facts[0] else {
        panic!("unboundedness")
    };
    let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
        panic!("witness")
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(less)) = &mut e.facts[0] else {
        panic!("tail")
    };
    std::mem::swap(&mut less.left, &mut less.right);
    compiler
        .compile_run(&run, "opposite_tail")
        .expect_err("recorded direction required");
}

#[test]
fn infinity_limit_definition_rejects_a_missing_unboundedness_proof() {
    let (mut run, compiler) = super::execute(DEFINITION);
    super::function_limit_tests::definition(&mut run)
        .proof_of_requirement_facts
        .remove(0);
    compiler
        .compile_run(&run, "missing_unboundedness")
        .expect_err("both original clauses required");
}
