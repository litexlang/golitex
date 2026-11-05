use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferInFactResult, InferResult, SetBuilderMembershipProjectionStep,
};
use std::rc::Rc;

const SOURCE: &str = r#"# Project membership through a nested domain whose predicate uses numeric WD.
claim:
    ? forall epsilon R+, x {t {s R: s != 0}: 0 < abs(t) and abs(t) < epsilon}:
        x $in R
    x $in {s R: s != 0}
    x $in R
"#;

fn projection(run: &mut RunLitexCodeResult) -> &mut SetBuilderMembershipProjectionStep {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        p,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let store =
        Rc::get_mut(&mut p.introduced_params.defined_params.store_and_infer_results[1]).unwrap();
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &mut store.infer
    else {
        panic!("member inference")
    };
    rules
        .iter_mut()
        .find_map(|r| match r {
            InferInFactResult::SetBuilder(p) => Some(&mut p.steps[0]),
            _ => None,
        })
        .expect("original builder projection")
}

#[test]
fn nested_builder_projection_rejects_a_changed_source_bound() {
    let (mut run, compiler) = super::execute(SOURCE);
    projection(&mut run).builder.param_set = Box::new(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "changed_builder_bound")
        .expect_err("original source builder required");
}

#[test]
fn nested_builder_projection_rejects_a_changed_condition_index() {
    let (mut run, compiler) = super::execute(SOURCE);
    let p = projection(&mut run);
    let crate::store_fact_and_infer::InferSetBuilderProjectionResult::Condition {
        condition_index,
        ..
    } = p
        .projections
        .iter_mut()
        .find(|r| {
            matches!(
                r,
                crate::store_fact_and_infer::InferSetBuilderProjectionResult::Condition { .. }
            )
        })
        .unwrap()
    else {
        unreachable!()
    };
    *condition_index = usize::MAX;
    compiler
        .compile_run(&run, "changed_condition_index")
        .expect_err("original condition index required");
}
