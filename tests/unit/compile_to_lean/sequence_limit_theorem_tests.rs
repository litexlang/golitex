use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecReleaseThmStmtResult,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::ExecDefinitionStmtResult;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const FROM_EPSILON: &str = r#"# Invoke the explicit epsilon-to-limit theorem for a real sequence.
thm checked_sequence_limit_intro:
    ? forall a seq(R), L R:
        forall epsilon R+:
            exist cutoff N+ st {{n N+:n>=cutoff} $subset preimage_set(a,{v R:abs(v-L)<epsilon})}
        =>:
            $has_seq_limit(a,L)
    by thm seq_limit_from_epsilon(a,L) => $has_seq_limit(a,L)
"#;
const TAIL: &str = r#"# Extract an epsilon-tail certificate from a proved real sequence limit.
thm checked_sequence_tail:
    ? forall a seq(R), L R, epsilon R+:
        $has_seq_limit(a,L)
        =>:
            exist cutoff N+ st {{n N+:n>=cutoff} $subset preimage_set(a,{v R:abs(v-L)<epsilon})}
    release thm seq_limit_tail(a,L,epsilon)
"#;

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

const UNIQUE: &str = r#"# Invoke the explicit sequence-limit uniqueness theorem.
claim:
    ? forall a seq(R), L R, K R:
        $has_seq_limit(a,L)
        $has_seq_limit(a,K)
        =>:
            L=K
    by thm seq_limit_unique(a,L,K) => L=K
"#;
const SELECTED: &str = r#"# The selected sequence limit satisfies the limit predicate.
claim:
    ? forall a seq(R):
        exist L R st {$has_seq_limit(a,L)}
        =>:
            $has_seq_limit(a,lim(a))
    release thm seq_limit_selected(a)
"#;

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
