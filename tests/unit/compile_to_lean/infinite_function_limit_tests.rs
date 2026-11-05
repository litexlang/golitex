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

const SELECTED: &str = r#"# A proved function-limit candidate at positive infinity determines the selector.
claim:
    ? forall f fn(x R) R, L R:
        $has_limit_pos_inf(f,L)
        =>:
            lim_pos_inf(f) = L
    lim_pos_inf(f) = L
"#;
const UNIQUE: &str = r#"# Two limits of the same real function at positive infinity are equal.
claim:
    ? forall f fn(x R) R, L R, K R:
        $has_limit_pos_inf(f,L)
        $has_limit_pos_inf(f,K)
        =>:
            L = K
    L = K
"#;

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

const DEFINITION: &str = r#"# Directional unboundedness and epsilon control prove a limit at positive infinity.
thm checked_pos_infinite_limit_intro:
    ? forall f fn(x R) R, L R:
        forall T R:
            exist x R st {T < x}
        forall epsilon R+:
            exist T R st {{x R: T < x} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_pos_inf(f,L)
    by def $has_limit_pos_inf(f,L)
"#;

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
