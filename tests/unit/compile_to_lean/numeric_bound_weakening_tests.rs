use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    less::LessFactSearchProofByBuiltinRule as Lt,
    less_equal::LessEqualFactSearchProofByBuiltinRule as Le,
};

const LOWER: &str =
    include_str!("../../../lean/examples/weaken_numeric_lower_bounds/statement.lit");
const UPPER: &str =
    include_str!("../../../lean/examples/weaken_numeric_upper_bounds/statement.lit");

fn citation(proof: &mut VerifyAtomicExceptEqualityFactSuccess) -> &mut FactId {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof
    else {
        panic!("numeric bound builtin")
    };
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            Lt::NumericLowerBoundWeakenLt(p),
        ) => &mut p.cite_fact_id,
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            Lt::NumericUpperBoundWeakenLt(p),
        ) => &mut p.cite_fact_id,
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            Le::NumericLowerBoundWeakenLe(p),
        ) => &mut p.cite_fact_id,
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            Le::NumericUpperBoundWeakenLe(p),
        ) => &mut p.cite_fact_id,
        _ => panic!("one of the four numeric weakening leaves"),
    }
}

#[test]
fn numeric_bound_weakening_preserves_orientations_and_comparison_strengths() {
    for source in [LOWER, UPPER] {
        let (mut run, compiler) = super::execute(source);
        for stmt in &mut run.statement_results {
            let forall = super::forall_proof_mut(stmt);
            let assumption = forall.assumed_dom_facts[0]
                .store_and_infer
                .primary_fact_id();
            assert_eq!(forall.proved_then_facts.len(), 2);
            for goal in &mut forall.proved_then_facts {
                assert_eq!(
                    *citation(super::atomic_proof_mut(&mut goal.verify_result)),
                    assumption
                );
            }
        }
        let lean = compiler.compile_run(&run, "weaken_bounds").unwrap();
        for law in ["leTrans", "ltToLe", "ltLeTrans", "leLtTrans"] {
            assert!(lean.contains(&format!("Litex.{law}")));
        }
    }
}

#[test]
fn numeric_bound_weakening_rejects_future_sibling_and_wrong_family_citations() {
    for source in [LOWER, UPPER] {
        for change in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let sibling = super::forall_proof_mut(&mut run.statement_results[1]).assumed_dom_facts
                [0]
            .store_and_infer
            .primary_fact_id();
            let forall = super::forall_proof_mut(&mut run.statement_results[0]);
            let bad = match change {
                0 => sibling,
                1 => forall.proved_then_facts[0]
                    .store_and_infer
                    .primary_fact_id(),
                2 => forall
                    .introduced_params
                    .defined_params
                    .store_and_infer_results[0]
                    .primary_fact_id(),
                _ => unreachable!(),
            };
            *citation(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            )) = bad;
            assert!(compiler.compile_run(&run, "bad_numeric_citation").is_err());
        }
    }
}

#[test]
fn numeric_bound_weakening_rejects_a_changed_target_or_variable() {
    for source in [LOWER, UPPER] {
        for change in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let forall = super::forall_proof_mut(&mut run.statement_results[0]);
            let result = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let AtomicFact::LessEqualFact(goal) = &mut result.fact else {
                panic!()
            };
            if change == 0 {
                goal.left = super::number_object("99");
            } else {
                goal.right = super::number_object("0");
            }
            assert!(compiler.compile_run(&run, "changed_numeric_bound").is_err());
        }
    }
}
