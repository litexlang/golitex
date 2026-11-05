use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{
    EnumerateAssignmentOutcome, ExecByForStmtResult, ExecByForStmtSuccess,
};
use crate::prelude::*;

const SQUARES: &str = r#"# Every integer in [0, 4) has square at most 9.
by for:
    ? forall n range(0, 4):
        n * n <= 9
    n * n <= 9
"#;
const GUARDS: &str = r#"# Division by a nonzero member of [-1, 2) cancels; the zero case has a false premise.
by for:
    ? forall n range(-1, 2):
        n != 0
        =>:
            n / n = 1
    n / n = 1
"#;

fn for_result(statement: &mut ExecStmtResult) -> &mut ExecByForStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::For(ExecByForStmtResult::Success(p))) = statement
    else {
        panic!("successful enumeration")
    };
    p
}

#[test]
fn integer_enumeration_replays_complete_original_branches_and_binding_ids() {
    let (mut run, compiler) = super::execute(SQUARES);
    let p = for_result(&mut run.statement_results[0]);
    assert_eq!(p.assignments.len(), 4);
    let ids = p
        .assignments
        .iter()
        .map(|a| a.binding_assumptions[0].store_and_infer.primary_fact_id())
        .collect::<Vec<_>>();
    let lean = compiler.compile_run(&run, "integer_squares").unwrap();
    for id in ids {
        assert!(lean.contains(&format!("have h_{}", id.value())));
    }
    assert!(lean.contains("Litex.inRangeInteger"));
    assert!(lean.contains("congrArg₂ M.mulValue"));
    assert_eq!(lean, compiler.compile_run(&run, "integer_squares").unwrap());
    assert!(lean.len() < 120_000);
}

#[test]
fn integer_enumeration_rejects_missing_reordered_or_changed_assignments() {
    for change in 0..5 {
        let (mut run, compiler) = super::execute(SQUARES);
        let p = for_result(&mut run.statement_results[0]);
        match change {
            0 => {
                p.assignments.pop();
            }
            1 => p.assignments.swap(0, 1),
            2 | 3 => {
                let StoreFactResult::AtomicFact(f) = &mut p.assignments[0].binding_assumptions[0]
                    .store_and_infer
                    .store
                else {
                    panic!()
                };
                let AtomicFact::EqualFact(f) = &mut f.fact else {
                    panic!()
                };
                if change == 2 {
                    f.right = Obj::StandardSet(StandardSet::R);
                } else {
                    f.left = Obj::StandardSet(StandardSet::R);
                }
            }
            4 => p.assignments[0].binding_assumptions.clear(),
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "bad_integer_assignment")
                .is_err(),
            "change {change}"
        );
    }
}

#[test]
fn integer_enumeration_rejects_foreign_and_future_substitution_citations() {
    for sibling in [false, true] {
        let (mut run, compiler) = super::execute(SQUARES);
        let p = for_result(&mut run.statement_results[0]);
        let bad_id = if sibling {
            p.assignments[1].binding_assumptions[0]
                .store_and_infer
                .primary_fact_id()
        } else {
            let EnumerateAssignmentOutcome::Proved { then_proofs, .. } = &p.assignments[0].outcome
            else {
                panic!()
            };
            then_proofs[0].store_and_infer.primary_fact_id()
        };
        let EnumerateAssignmentOutcome::Proved { proof_steps, .. } = &mut p.assignments[0].outcome
        else {
            panic!()
        };
        let ids = super::atomic_rewrite_cites_mut(super::atomic_rewrite_mut(&mut proof_steps[0]));
        assert_eq!(ids.len(), 1);
        ids[0] = bad_id;
        assert!(compiler
            .compile_run(&run, "escaped_enumeration_citation")
            .is_err());
    }
}

#[test]
fn integer_enumeration_keeps_constructed_literals_inside_their_assignment() {
    let (mut run, _) = super::execute(SQUARES);
    let p = for_result(&mut run.statement_results[0]);
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(_)) = &p.goal_wd
    else {
        panic!()
    };
    let StoreFactResult::ForallFact(stored) = &p.stored.store else {
        panic!()
    };
    let StoreFactResult::AtomicFact(f) = &p.assignments[0].binding_assumptions[0]
        .store_and_infer
        .store
    else {
        panic!()
    };
    let AtomicFact::EqualFact(binding) = &f.fact else {
        panic!()
    };
    let scope = SourcePosition::new(
        None,
        SourceOwner::EnumerationAssignment(&stored.fact, &p.assignments[0]),
        0,
    );
    assert!(scope.enumeration_literal(&binding.right).is_some());
    let other = SourcePosition::new(
        None,
        SourceOwner::EnumerationAssignment(&stored.fact, &p.assignments[1]),
        0,
    );
    assert!(other.enumeration_literal(&binding.right).is_none());
}

#[test]
fn integer_enumeration_skipped_guards_require_the_original_false_premise() {
    let (mut run, compiler) = super::execute(GUARDS);
    let p = for_result(&mut run.statement_results[0]);
    let EnumerateAssignmentOutcome::Skipped { premise_index, .. } = &mut p.assignments[1].outcome
    else {
        panic!("zero guard skipped")
    };
    *premise_index = 1;
    assert!(compiler.compile_run(&run, "bad_range_skip").is_err());
}

#[test]
fn arithmetic_subterm_order_rewrite_keeps_all_citations_in_selected_order() {
    let source = r#"# Substitute two known values inside an arithmetic expression to prove its bound.
have a R = 2
have b R = 3
a * a + b <= 7
"#;
    let (run, compiler) = super::execute(source);
    assert!(compiler
        .compile_run(&run, "nested_order_substitution")
        .is_ok());
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(source);
        let ids = super::atomic_rewrite_cites_mut(super::atomic_rewrite_mut(
            &mut run.statement_results[2],
        ));
        assert_eq!(ids.len(), 2);
        if missing {
            ids.pop();
        } else {
            ids.swap(0, 1);
        }
        assert!(compiler
            .compile_run(&run, "invalid_nested_order_substitution")
            .is_err());
    }
}
