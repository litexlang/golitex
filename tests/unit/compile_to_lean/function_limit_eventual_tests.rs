use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::{ExecDefinitionStmtResult, ExecReleaseAndExpandStmtResult};
use crate::prelude::*;

const POSITIVE: &str = r#"# A positive limit gives positive values on a sufficiently small at neighborhood.
thm at_eventually_positive:
    ? forall f fn(x R) R, p,L R:
        $has_limit_at(f,p,L)
        0<L
        =>:
            exist delta R+ st {{x R:0<(abs(x-p)) and (abs(x-p))<delta} $subset preimage_set(f,R+)}
    release thm fn_limit_at_eventually_positive(f,p,L)
"#;
const NONZERO: &str = r#"# A nonzero limit gives nonzero values on a sufficiently small at neighborhood.
thm at_eventually_nonzero:
    ? forall f fn(x R) R, p,L R:
        $has_limit_at(f,p,L)
        L!=0
        =>:
            exist delta R+ st {{x R:0<(abs(x-p)) and (abs(x-p))<delta} $subset preimage_set(f,R*)}
    release thm fn_limit_at_eventually_nonzero(f,p,L)
"#;
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
        panic!("eventual limit release")
    };
    p
}

#[test]
fn eventual_limit_conclusions_require_candidate_and_condition_evidence() {
    for source in [POSITIVE, NONZERO] {
        for missing in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            if missing {
                p.dom_proofs.pop();
            } else {
                p.dom_proofs.swap(4, 5);
            }
            compiler
                .compile_run(&run, "invalid_eventual_evidence")
                .expect_err(
                    "candidate and positive/nonzero condition have distinct original proofs",
                );
        }
    }
}

#[test]
fn eventual_limit_conclusions_reject_changed_threshold_domain_or_target() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(POSITIVE);
        let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
        else {
            panic!("threshold")
        };
        if mutation == 0 {
            e.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        } else {
            let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s)) = &mut e.facts[0] else {
                panic!("local inclusion")
            };
            if mutation == 1 {
                let Obj::SetFormer(SetFormer::SetBuilder(b)) = &mut s.left else {
                    panic!("neighborhood")
                };
                b.param_set = Box::new(Obj::StandardSet(StandardSet::Q));
            } else {
                let Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) = &mut s.right else {
                    panic!("preimage")
                };
                p.target_set = Box::new(Obj::StandardSet(StandardSet::RStar));
            }
        }
        compiler
            .compile_run(&run, "invalid_eventual_subject")
            .expect_err("exact threshold, complete domain and target carrier required");
    }
}
