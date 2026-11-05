use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess, ExecReleaseThmStmtResult,
    ExecReleaseThmStmtSuccess,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const UNIQUE: &str = r#"# Invoke the explicit at function-limit uniqueness theorem.
claim:
    ? forall f fn(x R) R, p R, L R, K R:
        $has_limit_at(f,p,L)
        $has_limit_at(f,p,K)
        =>:
            L = K
    by thm fn_limit_at_unique(f,p,L,K) => L = K
"#;
const EXISTS: &str = r#"# Release the explicit at function-limit exists theorem.
claim:
    ? forall f fn(x R) R, p R, L R:
        $has_limit_at(f,p,L)
        =>:
            exist K R st {$has_limit_at(f,p,K)}
    release thm fn_limit_at_exists(f,p,L)
"#;
const SELECTED: &str = r#"# Release the explicit at function-limit selected theorem.
claim:
    ? forall f fn(x R) R, p R:
        exist L R st {$has_limit_at(f,p,L)}
        =>:
            $has_limit_at(f,p,fn_lim(f,p))
    release thm fn_limit_at_selected(f,p)
"#;

const CONSTANT: &str = r#"# A constant function has the stated at limit on an accumulating domain.
claim:
    ? forall f fn(x R) R, p R, L R:
        forall r R+:
            exist x R st {0 < abs(x-p) and abs(x-p) < r}
        forall x R:
            f(x)=L
        =>:
            $has_limit_at(f,p,L)
    by thm fn_limit_at_constant(f,p,L) => $has_limit_at(f,p,L)
"#;

#[test]
fn explicit_constant_limit_rejects_missing_or_changed_accumulation() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(CONSTANT);
        let p = invocation(&mut run);
        if missing {
            p.dom_proofs.remove(5);
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[5] else {
                panic!("accumulation")
            };
            f.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        }
        compiler
            .compile_run(&run, "bad_constant_approach")
            .expect_err("original nontrivial approach required");
    }
}

#[test]
fn explicit_constant_limit_rejects_a_different_pointwise_value() {
    let (mut run, compiler) = super::execute(CONSTANT);
    let Fact::ForallFact(f) = &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[6]
    else {
        panic!("pointwise equation")
    };
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) = &mut f.then_facts[0]
    else {
        panic!("equation")
    };
    e.right = Obj::StandardSet(StandardSet::R);
    compiler
        .compile_run(&run, "wrong_constant_value")
        .expect_err("exact original pointwise value required");
}

pub(super) fn step(run: &mut RunLitexCodeResult) -> &mut ExecStmtResult {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        p,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    &mut p.proof_steps[0]
}

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) = step(run)
    else {
        panic!("by theorem")
    };
    p
}

fn release(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = step(run)
    else {
        panic!("release theorem")
    };
    p
}

#[test]
fn explicit_limit_uniqueness_rejects_changed_evidence_and_candidates() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(UNIQUE);
        let p = invocation(&mut run);
        match mutation {
            0 => p.dom_proofs.swap(0, 1),
            1 => {
                p.dom_stores.pop();
            }
            2 => {
                let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
                    p.builtin.as_mut().unwrap().requirements.last_mut().unwrap()
                else {
                    panic!("candidate")
                };
                f.approach = LimitApproach::AtPositiveInfinity;
            }
            _ => p.builtin.as_mut().unwrap().arguments[0] = Obj::StandardSet(StandardSet::R),
        }
        compiler
            .compile_run(&run, "changed_limit_invocation")
            .expect_err("original invocation and every ordered premise required");
    }
}

#[test]
fn explicit_limit_existence_rejects_a_missing_candidate_proof() {
    let (mut run, compiler) = super::execute(EXISTS);
    release(&mut run).dom_proofs.pop();
    compiler
        .compile_run(&run, "missing_limit_candidate")
        .expect_err("original candidate required");
}

#[test]
fn explicit_limit_selection_rejects_a_different_selected_approach() {
    let (mut run, compiler) = super::execute(SELECTED);
    let p = release(&mut run).builtin.as_mut().unwrap();
    let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = &mut p.conclusions[0] else {
        panic!("selected candidate")
    };
    let Obj::LimitOperator(LimitOperator::Function(p)) = &mut f.value else {
        panic!("selector")
    };
    p.approach = LimitApproach::AtNegativeInfinity;
    compiler
        .compile_run(&run, "changed_selected_approach")
        .expect_err("selected object keeps its source function and approach");
}
