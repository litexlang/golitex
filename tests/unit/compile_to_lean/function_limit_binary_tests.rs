use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;

const SUM: &str = r#"# Transfer two at limits through add on the same complete domain.
thm at_add_limits:
    ? forall f,g,s fn(x R) R, p,a,b R:
        $has_limit_at(f,p,a)
        $has_limit_at(g,p,b)
        forall x R:
            s(x)=f(x)+g(x)
        =>:
            $has_limit_at(s,p,a+b)
    by thm fn_limit_at_add(f,g,s,p,a,b) => $has_limit_at(s,p,a+b)
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
        panic!("binary limit invocation")
    };
    p
}

#[test]
fn binary_limit_algebra_requires_three_ordered_function_contexts() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SUM);
        let p = invocation(&mut run);
        match mutation {
            0 => {
                p.dom_proofs.pop();
            }
            1 => p.dom_proofs.swap(0, 8),
            2 => p.dom_stores.clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "missing_binary_evidence")
            .expect_err("all domains, candidates and the pointwise equation are required");
    }
}

#[test]
fn binary_limit_algebra_rejects_changed_domain_equalities() {
    for index in [7, 11] {
        let (mut run, compiler) = super::execute(SUM);
        let Fact::AtomicFact(AtomicFact::EqualFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[index]
        else {
            panic!("domain equality")
        };
        f.left = Obj::StandardSet(StandardSet::RPos);
        compiler
            .compile_run(&run, "changed_binary_domain")
            .expect_err("equal complete domains must be those of the recorded functions");
    }
}

#[test]
fn binary_limit_algebra_rejects_a_changed_formula_or_result() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(SUM);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::ForallFact(f) = &mut p.requirements[14] else {
                panic!("formula")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) =
                &mut f.then_facts[0]
            else {
                panic!("equation")
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) = &mut f.right else {
                panic!("sum")
            };
            p.left = Box::new(Obj::StandardSet(StandardSet::R));
        } else {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) = &mut p.conclusions[0]
            else {
                panic!("candidate")
            };
            f.approach = LimitApproach::AtPositiveInfinity;
        }
        compiler
            .compile_run(&run, "changed_binary_subject")
            .expect_err("exact pointwise operands and output approach");
    }
}

#[test]
fn division_limits_reject_missing_or_changed_nonzero_evidence() {
    let source = r#"# Divide two at limits with a nonzero limit and nonzero denominator calls.
thm at_quotient_limit:
    ? forall f,g,q fn(x R) R, p,a,b R:
        $has_limit_at(f,p,a)
        $has_limit_at(g,p,b)
        b!=0
        forall x R:
            g(x)!=0
        forall x R:
            q(x)=f(x)/g(x)
        =>:
            $has_limit_at(q,p,a/b)
    by thm fn_limit_at_divide(f,g,q,p,a,b) => $has_limit_at(q,p,a/b)
"#;
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(source);
        let p = invocation(&mut run);
        if mutation < 2 {
            p.dom_proofs.remove(14 + mutation);
        } else if mutation == 2 {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[14]
            else {
                panic!("nonzero limit")
            };
            f.left = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[15] else {
                panic!("nonzero calls")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(f)) =
                &mut f.then_facts[0]
            else {
                panic!("nonzero call")
            };
            f.left = Obj::StandardSet(StandardSet::R);
        }
        compiler
            .compile_run(&run, "invalid_division_limit")
            .expect_err("nonzero limit and nonzero calls have distinct source evidence");
    }
}
