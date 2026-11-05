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

const SOURCES: [&str; 3] = [
    r#"# Strict increase implies weak increase for a positive-indexed real sequence.
thm strict_increase_is_weak_increase:
    ? forall a seq(R):
        $is_seq_strictly_increasing(a)
        =>:
            $is_seq_nondecreasing(a)
    release thm sequence_strict_increasing_nondecreasing(a)
"#,
    r#"# Strict decrease implies weak decrease for a positive-indexed real sequence.
thm strict_decrease_is_weak_decrease:
    ? forall a seq(R):
        $is_seq_strictly_decreasing(a)
        =>:
            $is_seq_nonincreasing(a)
    release thm sequence_strict_decreasing_nonincreasing(a)
"#,
    r#"# Two real bounds on all terms make a real sequence bounded.
thm pointwise_bounds_make_sequence_bounded:
    ? forall a seq(R), lower,upper R:
        forall n N+:
            lower<=a(n)
            a(n)<=upper
        =>:
            $is_seq_bounded(a)
    release thm sequence_bounded_from_bounds(a,lower,upper)
"#,
];
#[test]
fn sequence_order_and_bounds_reject_missing_or_altered_evidence() {
    for (index, source) in SOURCES.into_iter().enumerate() {
        for mutation in 0..3 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            if mutation == 0 {
                p.dom_proofs.pop();
            } else if mutation == 1 {
                p.dom_stores.clear();
            } else if index < 2 {
                let Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[1]
                else {
                    panic!("strict order")
                };
                f.property = SequenceAnalysisProperty::Bounded;
            } else {
                let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[3] else {
                    panic!("pointwise bounds")
                };
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::Z));
            }
            c.compile_run(&run, "changed_sequence_order")
                .expect_err("exact properties, positive indexing and original evidence");
        }
    }
}
