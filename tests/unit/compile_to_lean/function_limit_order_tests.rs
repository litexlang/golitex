use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;
const SOURCE: &str = include_str!("../../../lean/examples/function_limit_at_compare/statement.lit");
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
        panic!("comparison")
    };
    p
}
#[test]
fn local_limit_order_replays_all_approaches_and_guarded_domains() {
    for source in [
        include_str!("../../../lean/examples/function_limit_at_compare/statement.lit"),
        include_str!("../../../lean/examples/function_limit_left_compare/statement.lit"),
        include_str!("../../../lean/examples/function_limit_right_compare/statement.lit"),
        include_str!("../../../lean/examples/function_limit_pos_inf_compare/statement.lit"),
        include_str!("../../../lean/examples/function_limit_neg_inf_compare/statement.lit"),
        include_str!("../../../lean/examples/function_limit_guarded_compare/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        assert!(c
            .compile_run(&run, "limit_order")
            .unwrap()
            .contains("FunctionLimitCompare"));
    }
}
#[test]
fn local_limit_order_requires_original_candidates_and_local_radius() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SOURCE);
        let p = invocation(&mut run);
        if mutation == 0 {
            p.dom_proofs.pop();
        } else if mutation == 1 {
            p.dom_proofs.swap(8, 9);
        } else {
            p.dom_stores.clear();
        }
        c.compile_run(&run, "missing_order_evidence")
            .expect_err("two candidates, radius and local comparison are required");
    }
}
#[test]
fn local_limit_order_rejects_changed_domains_comparisons_and_output() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SOURCE);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.requirements[7] else {
                panic!("domain")
            };
            f.left = Obj::StandardSet(StandardSet::Q);
        } else if mutation == 1 {
            let Fact::ForallFact(f) = &mut p.requirements[11] else {
                panic!("local order")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(f)) =
                &mut f.then_facts[0]
            else {
                panic!("weak order")
            };
            std::mem::swap(&mut f.left, &mut f.right);
        } else {
            let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut p.conclusions[0] else {
                panic!("limit order")
            };
            std::mem::swap(&mut f.left, &mut f.right);
        }
        c.compile_run(&run, "changed_order_subject")
            .expect_err("original domain, local orientation and limiting values");
    }
}
