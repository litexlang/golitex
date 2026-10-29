use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecReleaseThmStmtResult,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const FROM_EPSILON: &str =
    include_str!("../../../lean/examples/sequence_limit_from_epsilon_by_theorem/statement.lit");
const TAIL: &str =
    include_str!("../../../lean/examples/sequence_limit_tail_by_theorem/statement.lit");

fn theorem_step(run: &mut RunLitexCodeResult) -> &mut ExecStmtResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    &mut p.proof_steps[0]
}

#[test]
fn sequence_limit_theorems_replay_epsilon_introduction_and_tail_elimination() {
    for (source, law) in [
        (FROM_EPSILON, "Litex.sequenceLimitOfForall"),
        (TAIL, "Litex.sequenceLimitTail"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "sequence_epsilon_theorem")
            .unwrap()
            .contains(law));
    }
}

#[test]
fn sequence_limit_from_epsilon_rejects_missing_or_nonpositive_epsilon_evidence() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(FROM_EPSILON);
        let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
            theorem_step(&mut run)
        else {
            panic!("invocation")
        };
        if missing {
            p.dom_proofs.pop();
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[2] else {
                panic!("epsilon control")
            };
            f.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        }
        compiler
            .compile_run(&run, "changed_sequence_epsilon")
            .expect_err("the original positive-epsilon clause is required");
    }
}

#[test]
fn sequence_limit_tail_rejects_changed_cutoff_or_epsilon_carriers() {
    for changed_cutoff in [false, true] {
        let (mut run, compiler) = super::execute(TAIL);
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(p),
        )) = theorem_step(&mut run)
        else {
            panic!("release")
        };
        let builtin = p.builtin.as_mut().unwrap();
        if changed_cutoff {
            let Fact::ExistFact(e) = &mut builtin.conclusions[0] else {
                panic!("cutoff")
            };
            e.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::N));
        } else {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut builtin.requirements[2] else {
                panic!("epsilon")
            };
            f.set = Obj::StandardSet(StandardSet::R);
        }
        compiler
            .compile_run(&run, "changed_tail_certificate")
            .expect_err("a positive epsilon and positive-natural cutoff are required");
    }
}

const UNIQUE: &str =
    include_str!("../../../lean/examples/sequence_limit_unique_by_theorem/statement.lit");
const EXISTS: &str =
    include_str!("../../../lean/examples/sequence_limit_exists_by_theorem/statement.lit");
const SELECTED: &str =
    include_str!("../../../lean/examples/sequence_limit_selected_by_theorem/statement.lit");

#[test]
fn sequence_limit_theorems_replay_uniqueness_existence_and_selection() {
    for (source, law) in [
        (UNIQUE, "Litex.sequenceLimitCandidatesEqual"),
        (EXISTS, "Litex.sequenceConvergentOfCandidate"),
        (SELECTED, "Litex.sequenceLimitSelected"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "sequence_limit_theorem")
            .unwrap()
            .contains(law));
    }
}

#[test]
fn sequence_limit_uniqueness_rejects_missing_candidates_and_changed_domain() {
    for changed_domain in [false, true] {
        let (mut run, compiler) = super::execute(UNIQUE);
        let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
            super::function_limit_theorem_tests::step(&mut run)
        else {
            panic!("invocation")
        };
        if changed_domain {
            let Fact::AtomicFact(AtomicFact::InFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[0]
            else {
                panic!("membership")
            };
            let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &mut f.set else {
                panic!("signature")
            };
            s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            p.dom_proofs.pop();
        }
        compiler
            .compile_run(&run, "changed_sequence_limit_call")
            .expect_err("both candidates and exact positive-natural real domain required");
    }
}

#[test]
fn sequence_limit_selection_rejects_a_different_selected_sequence() {
    let (mut run, compiler) = super::execute(SELECTED);
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = super::function_limit_theorem_tests::step(&mut run)
    else {
        panic!("release")
    };
    let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) =
        &mut p.builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!("candidate")
    };
    let Obj::LimitOperator(LimitOperator::Sequence(p)) = &mut f.value else {
        panic!("selector")
    };
    p.sequence = Box::new(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "changed_selected_sequence")
        .expect_err("exact selected sequence required");
}
