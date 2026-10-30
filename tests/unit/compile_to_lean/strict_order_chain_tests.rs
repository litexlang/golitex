use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByBuiltinRewrite as Rule;

const SOURCE: &str = include_str!("../../../lean/examples/strict_order_chains/statement.lit");

#[test]
fn strict_order_chains_replay_one_step_search_and_explicit_mixed_chains() {
    let (mut run, compiler) = super::execute(SOURCE);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let first = forall.assumed_dom_facts[0]
        .store_and_infer
        .primary_fact_id();
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(Rule::OrderTransitivity(p)) =
        &proof.searched_proof
    else {
        panic!("strict transitivity rewrite")
    };
    assert_eq!(p.application.known_left_fact_id, first);
    let lean = compiler.compile_run(&run, "strict_chains").unwrap();
    for law in ["ltTrans", "ltLeTrans", "leLtTrans"] {
        assert!(lean.contains(&format!("Litex.{law} ")));
    }
}

#[test]
fn strict_order_chains_reject_wrong_strength_endpoint_and_visibility() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let future = forall.proved_then_facts[0]
            .store_and_infer
            .primary_fact_id();
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        if change == 0 {
            let AtomicFact::LessFact(fact) = &proof.fact else {
                panic!()
            };
            proof.fact = LessEqualFact {
                fact_id: fact.fact_id,
                left: fact.left.clone(),
                right: fact.right.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
        } else {
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(Rule::OrderTransitivity(p)) =
                &mut proof.searched_proof
            else {
                panic!()
            };
            if change == 1 {
                p.application.known_left_fact_id = future;
            } else {
                let Fact::AtomicFact(AtomicFact::LessFact(residual)) =
                    &mut p.application.residual_fact
                else {
                    panic!()
                };
                residual.right = super::number_object("0");
            }
        }
        assert!(compiler.compile_run(&run, "invalid_strict_chain").is_err());
    }
}
