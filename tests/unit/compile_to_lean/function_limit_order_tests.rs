use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;
const SOURCE: &str = r#"# A local weak comparison passes to the two at limit values.
thm at_limits_compare:
    ? forall f,g fn(x R) R, p,a,b R, r R+:
        $has_limit_at(f,p,a)
        $has_limit_at(g,p,b)
        forall x {t R:0<(abs(t-p)) and (abs(t-p))<r}:
            f(x)<=g(x)
        =>:
            a<=b
    by thm fn_limit_at_compare(f,g,p,a,b,r) => a<=b
"#;
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
