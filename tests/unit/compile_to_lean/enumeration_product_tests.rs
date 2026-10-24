use crate::execute::execute_by_stmt::{
    EnumerateAssignmentOutcome, ExecByForStmtResult, ExecByForStmtSuccess,
};
use crate::prelude::*;

const RECTANGLE: &str =
    include_str!("../../../lean/examples/integer_rectangle_square_bound/statement.lit");
const GUARDS: &str =
    include_str!("../../../lean/examples/nonzero_integer_pair_division/statement.lit");

fn product(statement: &mut ExecStmtResult) -> &mut ExecByForStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::For(ExecByForStmtResult::Success(p))) = statement
    else {
        panic!("successful by-for result")
    };
    p
}

#[test]
fn enumeration_product_replays_every_original_binding_in_source_order() {
    let (mut run, compiler) = super::execute(RECTANGLE);
    let p = product(&mut run.statement_results[0]);
    assert_eq!(p.assignments.len(), 6);
    let mut ids = Vec::new();
    for (i, assignment) in p.assignments.iter().enumerate() {
        assert_eq!(assignment.binding_assumptions.len(), 2);
        for (j, binding) in assignment.binding_assumptions.iter().enumerate() {
            let StoreFactResult::AtomicFact(stored) = &binding.store_and_infer.store else {
                panic!()
            };
            let AtomicFact::EqualFact(f) = &stored.fact else {
                panic!()
            };
            let value = if j == 0 { i / 2 } else { i % 2 };
            assert!(
                matches!(&f.right, Obj::Literal(Literal::Number(n)) if n.normalized_value == value.to_string())
            );
            ids.push(f.fact_id);
        }
    }
    let lean = compiler.compile_run(&run, "rectangle").unwrap();
    for id in ids {
        assert!(lean.contains(&format!("have h_{}", id.value())));
    }
    assert!(lean.contains("_enumerated_case_0"));
    assert!(lean.contains("_enumerated_case_1"));
    assert!(lean.contains("Eq.trans (congrArg"));
    assert!(lean.len() < 400_000);
    assert_eq!(lean, compiler.compile_run(&run, "rectangle").unwrap());
}

#[test]
fn enumeration_product_rejects_incomplete_reordered_or_changed_evidence() {
    for change in 0..7 {
        let (mut run, compiler) = super::execute(RECTANGLE);
        let p = product(&mut run.statement_results[0]);
        match change {
            0 => {
                p.assignments.pop();
            }
            1 => p.assignments.swap(1, 2),
            2 => p.assignments[0].binding_assumptions.swap(0, 1),
            3 => {
                p.assignments[0].binding_assumptions.pop();
            }
            4 => {
                p.assignments[0]
                    .introduced_params
                    .defined_params
                    .store_and_infer_results
                    .pop();
            }
            5 => {
                p.assignments[0]
                    .introduced_params
                    .param_type_well_defined
                    .pop();
            }
            6 => {
                let StoreFactResult::AtomicFact(stored) = &mut p.assignments[0].binding_assumptions
                    [1]
                .store_and_infer
                .store
                else {
                    panic!()
                };
                let AtomicFact::EqualFact(f) = &mut stored.fact else {
                    panic!()
                };
                f.right = Obj::StandardSet(StandardSet::R);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "corrupted_product").is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn enumeration_product_rejects_sibling_future_and_reordered_rewrite_citations() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(RECTANGLE);
        let p = product(&mut run.statement_results[0]);
        let foreign = p.assignments[1].binding_assumptions[1]
            .store_and_infer
            .primary_fact_id();
        let EnumerateAssignmentOutcome::Proved {
            proof_steps,
            then_proofs,
            ..
        } = &mut p.assignments[0].outcome
        else {
            panic!()
        };
        let future = then_proofs[0].store_and_infer.primary_fact_id();
        let ids = super::atomic_rewrite_cites_mut(super::atomic_rewrite_mut(&mut proof_steps[0]));
        assert_eq!(ids.len(), 2);
        match change {
            0 => ids[1] = foreign,
            1 => ids[1] = future,
            2 => ids.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "escaped_product_citation")
            .is_err());
    }
}

#[test]
fn enumeration_product_preserves_both_guard_prefixes_and_return_conjunction() {
    let (mut run, compiler) = super::execute(GUARDS);
    let p = product(&mut run.statement_results[0]);
    let skips = p
        .assignments
        .iter()
        .filter(|a| matches!(a.outcome, EnumerateAssignmentOutcome::Skipped { .. }))
        .count();
    assert_eq!(skips, 5);
    assert!(
        matches!(&p.assignments[1].outcome, EnumerateAssignmentOutcome::Skipped { premise_index: 1, premise_assumptions, .. } if premise_assumptions.len() == 1)
    );
    assert!(
        matches!(&p.assignments[3].outcome, EnumerateAssignmentOutcome::Skipped { premise_index: 0, premise_assumptions, .. } if premise_assumptions.is_empty())
    );
    assert!(compiler.compile_run(&run, "guarded_pair").is_ok());
    let p = product(&mut run.statement_results[0]);
    let EnumerateAssignmentOutcome::Skipped { premise_index, .. } = &mut p.assignments[1].outcome
    else {
        panic!()
    };
    *premise_index = 0;
    assert!(compiler.compile_run(&run, "changed_guard").is_err());
}

#[test]
fn enumeration_product_empty_factor_does_not_expand_other_factors() {
    for source in [
        include_str!("../../../lean/examples/empty_integer_rectangle/statement.lit"),
        "by for:\n    ? forall x {0,1}, y {}:\n        x=y\n    x=y\n",
        "by for:\n    ? forall x {}, y range(0,3):\n        x=y\n    x=y\n",
    ] {
        let (mut run, compiler) = super::execute(source);
        assert!(product(&mut run.statement_results[0])
            .assignments
            .is_empty());
        let lean = compiler.compile_run(&run, "empty_product").unwrap();
        assert!(!lean.contains("_enumerated_case_"));
        assert!(lean.len() < 10_000);
    }
}

#[test]
fn enumeration_product_accepts_shared_groups_mixed_domains_and_local_scope() {
    for source in [
        include_str!("../../../lean/examples/binary_product_commutes/statement.lit"),
        include_str!("../../../lean/examples/mixed_finite_product_commutes/statement.lit"),
        include_str!("../../../lean/examples/finite_triple_product/statement.lit"),
        include_str!("../../../lean/examples/named_integer_rectangle_bound/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "product_scope").unwrap();
    }
}

#[test]
fn enumeration_product_rejects_source_valid_dependent_domains() {
    let (run, compiler) =
        super::execute("by for:\n    ? forall x {0,1}, y {x}:\n        y=y\n    y=y\n");
    assert_eq!(
        compiler
            .compile_run(&run, "dependent_product")
            .unwrap_err()
            .route,
        "Enumeration/DependentDomain"
    );
}
