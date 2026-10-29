use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const LEFT: &str =
    include_str!("../../../lean/examples/function_limit_at_to_left_by_theorem/statement.lit");
const COMBINED: &str =
    include_str!("../../../lean/examples/function_limit_from_sides_by_theorem/statement.lit");
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
        &mut p.proof_steps[0]
    else {
        panic!("side bridge")
    };
    p
}

#[test]
fn side_limit_bridges_replay_restriction_combination_and_mismatch() {
    for source in [
        LEFT,
        COMBINED,
        include_str!("../../../lean/examples/function_limit_at_to_right_by_theorem/statement.lit"),
        include_str!(
            "../../../lean/examples/function_limit_sides_mismatch_by_theorem/statement.lit"
        ),
        include_str!("../../../lean/examples/function_limit_guarded_at_to_left/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "limit_sides").unwrap();
    }
}

#[test]
fn side_limit_restriction_requires_the_exact_side_and_accumulating_domain() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(LEFT);
        let p = invocation(&mut run);
        if mutation == 0 {
            p.dom_proofs.pop();
        } else if mutation == 1 {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[0]
            else {
                panic!("side candidate")
            };
            f.approach = LimitApproach::FromRight(Box::new(Obj::StandardSet(StandardSet::R)));
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[6] else {
                panic!("accumulation")
            };
            let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
                panic!("witness")
            };
            e.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::Q));
        }
        compiler
            .compile_run(&run, "invalid_side_restriction")
            .expect_err("the selected side must accumulate on the original complete domain");
    }
}

#[test]
fn combining_sides_rejects_missing_or_reordered_candidates() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(COMBINED);
        let p = invocation(&mut run);
        if missing {
            p.dom_proofs.pop();
        } else {
            p.dom_proofs.swap(5, 6);
        }
        compiler
            .compile_run(&run, "invalid_combined_sides")
            .expect_err("original left and right candidate proofs required");
    }
}
