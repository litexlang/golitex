use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const LEFT: &str = r#"# Restrict a two-sided limit only when the selected side accumulates in the domain.
thm limit_at_to_left:
    ? forall f fn(x R) R, p,L R:
        $has_limit_at(f,p,L)
        forall r R+:
            exist x R st {0<(p-x) and (p-x)<r}
        =>:
            $has_limit_left(f,p,L)
    by thm fn_limit_at_to_left(f,p,L) => $has_limit_left(f,p,L)
"#;
const COMBINED: &str = r#"# Equal left and right limits give a two-sided limit on the same complete domain.
thm bridge_from_sides:
    ? forall f fn(x R) R, p,L R:
        $has_limit_left(f,p,L)
        $has_limit_right(f,p,L)
        =>:
            $has_limit_at(f,p,L)
    by thm fn_limit_from_sides(f,p,L) => $has_limit_at(f,p,L)
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
        panic!("side bridge")
    };
    p
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
