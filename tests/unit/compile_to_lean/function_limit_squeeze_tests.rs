use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::{ExecDefinitionStmtResult, ExecReleaseAndExpandStmtResult};
use crate::prelude::*;
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut p.proof_steps[0]
    else {
        panic!("builtin invocation")
    };
    p
}
const SOURCE: &str = include_str!("../../../lean/examples/function_limit_at_squeeze/statement.lit");
#[test]
fn squeeze_replays_five_approaches() {
    for source in [
        include_str!("../../../lean/examples/function_limit_at_squeeze/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_squeeze/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_squeeze/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_inf_squeeze/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_inf_squeeze/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        assert!(c
            .compile_run(&run, "limit_transfer")
            .unwrap()
            .contains("FunctionLimitSqueeze"));
    }
}
#[test]
fn squeeze_requires_every_recorded_stage() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SOURCE);
        let p = invocation(&mut run);
        if mutation == 0 {
            p.dom_proofs.pop();
        } else if mutation == 1 {
            p.dom_stores.clear();
        } else {
            p.dom_proofs.swap(0, 1);
        }
        c.compile_run(&run, "missing_transfer_evidence")
            .expect_err("every original requirement and store is required");
    }
}
#[test]
fn squeeze_rejects_changed_candidates_domain_and_chain() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = &mut b.requirements[12]
            else {
                panic!("lower limit")
            };
            f.function = Obj::StandardSet(StandardSet::Q);
        } else if mutation == 1 {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.requirements[11] else {
                panic!("upper domain")
            };
            f.right = Obj::StandardSet(StandardSet::Q);
        } else {
            let Fact::ForallFact(f) = &mut b.requirements[15] else {
                panic!("local chain")
            };
            let ExistOrAndChainAtomicFact::ChainFact(c) = &mut f.then_facts[0] else {
                panic!("chain")
            };
            c.objs.swap(0, 2);
        }
        c.compile_run(&run, "changed_squeeze_transfer")
            .expect_err("preserve both candidates, common domains and chain orientation");
    }
}
