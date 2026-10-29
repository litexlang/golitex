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
    include_str!("../../../lean/examples/sequence_cauchy_from_epsilon_by_theorem/statement.lit"),
    include_str!("../../../lean/examples/sequence_cauchy_tail_by_theorem/statement.lit"),
    include_str!("../../../lean/examples/sequence_convergent_from_limit_by_theorem/statement.lit"),
    include_str!("../../../lean/examples/sequence_limit_from_convergent_by_theorem/statement.lit"),
];
#[test]
fn sequence_cauchy_and_convergence_certificates_replay() {
    for source in SOURCES {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "sequence_certificate").unwrap();
    }
}
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
