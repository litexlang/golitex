use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByBuiltinRewrite as Rule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_transitive_relation::TransitiveRelationProof;

const SOURCE: &str = "forall x R:\n    x<=900\n    =>:\n        x<=1070\nforall y R:\n    y>=1260\n    =>:\n        y>=1250\n";

fn application(proof: &mut VerifyAtomicExceptEqualityFactSuccess) -> &mut TransitiveRelationProof {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(Rule::OrderTransitivity(p)) =
        &mut proof.searched_proof
    else {
        panic!("order transitivity rewrite")
    };
    &mut p.application
}

#[test]
fn one_step_order_transitivity_compiles_the_selected_known_edge_and_child() {
    let (mut run, compiler) = super::execute(SOURCE);
    for statement in &mut run.statement_results {
        let forall = super::forall_proof_mut(statement);
        let assumption = forall.assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id();
        let goal = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        assert_eq!(application(goal).known_left_fact_id, assumption);
    }
    let lean = compiler.compile_run(&run, "order_transitivity").unwrap();
    assert_eq!(lean.matches("Litex.leTrans").count(), 2);
}

#[test]
fn one_step_order_transitivity_rejects_sibling_future_and_wrong_family_citations() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(SOURCE);
        let sibling = super::forall_proof_mut(&mut run.statement_results[1]).assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id();
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let bad = match change {
            0 => sibling,
            1 => forall.proved_then_facts[0]
                .store_and_infer
                .primary_fact_id(),
            _ => forall
                .introduced_params
                .defined_params
                .store_and_infer_results[0]
                .primary_fact_id(),
        };
        let goal = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        application(goal).known_left_fact_id = bad;
        assert!(compiler.compile_run(&run, "bad_transitivity").is_err());
    }
}

#[test]
fn one_step_order_transitivity_rejects_a_changed_target_and_residual() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let goal = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        match change {
            0 | 1 => {
                let AtomicFact::LessEqualFact(target) = &mut goal.fact else {
                    panic!()
                };
                if change == 0 {
                    target.left = super::number_object("99");
                } else {
                    target.right = super::number_object("0");
                }
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::LessEqualFact(residual)) =
                    &mut application(goal).residual_fact
                else {
                    panic!()
                };
                residual.left = super::number_object("99");
            }
        }
        assert!(compiler.compile_run(&run, "changed_transitivity").is_err());
    }
}
