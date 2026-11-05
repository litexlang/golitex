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

const SOURCES: [&str; 4] = [
    r#"# The epsilon-tail condition proves that a real sequence is Cauchy.
thm cauchy_from_tail:
    ? forall a seq(R):
        forall epsilon R+:
            exist cutoff N+ st {cart({m N+:m>=cutoff},{n N+:n>=cutoff}) $subset {p cart(N+,N+):abs(a(p(1))-a(p(2)))<epsilon}}
        =>:
            $is_seq_cauchy(a)
    release thm sequence_cauchy_from_epsilon(a)
"#,
    r#"# A Cauchy sequence has a controlling tail for each positive tolerance.
thm cauchy_tail_exists:
    ? forall a seq(R), epsilon R+:
        $is_seq_cauchy(a)
        =>:
            exist cutoff N+ st {cart({m N+:m>=cutoff},{n N+:n>=cutoff}) $subset {p cart(N+,N+):abs(a(p(1))-a(p(2)))<epsilon}}
    release thm sequence_cauchy_tail(a,epsilon)
"#,
    r#"# A supplied real limit makes a real sequence convergent.
thm convergent_from_candidate:
    ? forall a seq(R), L R:
        $has_seq_limit(a,L)
        =>:
            $is_seq_convergent(a)
    release thm sequence_convergent_from_limit(a,L)
"#,
    r#"# A convergent real sequence has a real limit witness.
thm convergent_limit_exists:
    ? forall a seq(R):
        $is_seq_convergent(a)
        =>:
            exist L R st {$has_seq_limit(a,L)}
    release thm sequence_limit_from_convergent(a)
"#,
];
#[test]
fn sequence_certificates_require_all_original_proofs_and_stores() {
    for source in SOURCES {
        for mutation in 0..2 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            if mutation == 0 {
                p.dom_proofs.pop();
            } else {
                p.dom_stores.clear();
            }
            c.compile_run(&run, "missing_sequence_certificate")
                .expect_err("retain original ordered evidence");
        }
    }
}
#[test]
fn sequence_certificates_reject_altered_carriers_and_subjects() {
    for (index, source) in SOURCES.into_iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        match index {
            0 => {
                let Fact::ForallFact(f) = &mut b.requirements[1] else {
                    panic!("epsilon clause")
                };
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            }
            1 => {
                let Fact::ExistFact(f) = &mut b.conclusions[0] else {
                    panic!("tail witness")
                };
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            }
            2 => {
                let Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) = &mut b.conclusions[0]
                else {
                    panic!("convergence")
                };
                f.property = SequenceAnalysisProperty::Cauchy;
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) = &mut b.requirements[1]
                else {
                    panic!("convergence")
                };
                f.property = SequenceAnalysisProperty::Cauchy;
            }
        }
        c.compile_run(&run, "changed_sequence_certificate")
            .expect_err("original epsilon, positive-natural cutoff and convergence property");
    }
}
