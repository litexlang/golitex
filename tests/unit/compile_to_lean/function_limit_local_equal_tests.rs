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
const SOURCE: &str =
    include_str!("../../../lean/examples/function_limit_at_local_equal/statement.lit");
#[test]
fn local_equal_replays_five_approaches() {
    for source in [
        include_str!("../../../lean/examples/function_limit_at_local_equal/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_local_equal/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_local_equal/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_inf_local_equal/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_inf_local_equal/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        assert!(c
            .compile_run(&run, "limit_transfer")
            .unwrap()
            .contains("FunctionLimitLocalEqual"));
    }
}
#[test]
fn local_equal_requires_every_recorded_stage() {
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
fn local_equal_rejects_changed_output_domain_neighborhood_and_equation() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::AtomicFact(AtomicFact::SubsetFact(f)) = &mut b.requirements[10] else {
                panic!("local inclusion")
            };
            f.right = Obj::StandardSet(StandardSet::Q);
        } else if mutation == 1 {
            let Fact::AtomicFact(AtomicFact::SubsetFact(f)) = &mut b.requirements[10] else {
                panic!("neighborhood")
            };
            let Obj::SetFormer(SetFormer::SetBuilder(s)) = &mut f.left else {
                panic!("builder")
            };
            s.facts.clear();
        } else {
            let Fact::ForallFact(f) = &mut b.requirements[11] else {
                panic!("local equation")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                &mut f.then_facts[0]
            else {
                panic!("equation")
            };
            std::mem::swap(&mut eq.left, &mut eq.right);
        }
        c.compile_run(&run, "changed_local_transfer")
            .expect_err("preserve domains, cutoff and equation subjects");
    }
}
