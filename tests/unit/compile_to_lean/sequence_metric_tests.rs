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

const CAUCHY: &str =
    include_str!("../../../lean/examples/sequence_limit_cauchy_by_theorem/statement.lit");
const CONSTANT: &str =
    include_str!("../../../lean/examples/constant_sequence_properties_by_theorem/statement.lit");
#[test]
fn sequence_metric_laws_replay_supplied_limits_and_constant_properties() {
    for source in [
        CAUCHY,
        CONSTANT,
        include_str!("../../../lean/examples/constant_sequence_complete/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        let out = c.compile_run(&run, "sequence_metric").unwrap();
        assert!(
            out.contains("sequenceCauchyOfCandidate") || out.contains("sequenceConstantProperties")
        );
        if out.contains("sequenceConstantProperties") {
            assert_eq!(
                out.matches("from Litex.sequenceConstantProperties ")
                    .count(),
                1
            );
            assert!(
                out.len() < 100_000,
                "one source call must share its five results"
            );
        }
    }
}
#[test]
fn sequence_metric_laws_require_all_original_stage_evidence() {
    for source in [CAUCHY, CONSTANT] {
        for mutation in 0..4 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => p.dom_stores.clear(),
                2 => {
                    p.conclusions_wd.pop();
                }
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            c.compile_run(&run, "missing_metric_evidence")
                .expect_err("complete original proof, store, WD and selected schema");
        }
    }
}
#[test]
fn sequence_limit_cauchy_rejects_altered_candidate_and_output_property() {
    for mutation in 0..2 {
        let (mut run, c) = super::execute(CAUCHY);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == 0 {
            let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) = &mut b.requirements[1]
            else {
                panic!("candidate")
            };
            f.value = Obj::StandardSet(StandardSet::R);
        } else {
            let Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) = &mut b.conclusions[0]
            else {
                panic!("Cauchy")
            };
            f.property = SequenceAnalysisProperty::Convergent;
        }
        c.compile_run(&run, "changed_metric_subject")
            .expect_err("exact candidate and Cauchy conclusion");
    }
}
#[test]
fn constant_sequence_properties_reject_changed_index_equation_and_ordered_outputs() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(CONSTANT);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        match mutation {
            0 => {
                let Fact::ForallFact(f) = &mut b.requirements[2] else {
                    panic!("constant equation")
                };
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::Z));
            }
            1 => {
                let Fact::ForallFact(f) = &mut b.requirements[2] else {
                    panic!("constant equation")
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut f.then_facts[0]
                else {
                    panic!("equation")
                };
                std::mem::swap(&mut eq.left, &mut eq.right);
            }
            _ => b.conclusions.swap(2, 3),
        }
        c.compile_run(&run, "changed_constant_sequence")
            .expect_err("positive indexing, original equation and all five ordered properties");
    }
}
