use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{LessFactSearchProofByBuiltinRule, LessTransitivityBuiltinRuleProof};

const SOURCE: &str = include_str!("../../../lean/examples/strict_order_chains/statement.lit");

fn chain(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> &mut LessTransitivityBuiltinRuleProof {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::LessTransitivity(p),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("original strict transitivity result")
    };
    p
}

#[test]
fn strict_order_chains_replay_both_ids_and_all_three_strength_combinations() {
    let (mut run, compiler) = super::execute(SOURCE);
    for (i, expected) in [(true, true), (true, false), (false, true)]
        .into_iter()
        .enumerate()
    {
        let forall = super::forall_proof_mut(&mut run.statement_results[i]);
        let first = forall.assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id();
        let second = forall.assumed_dom_facts[1]
            .store_and_infer
            .primary_fact_id();
        let p = chain(super::atomic_proof_mut(
            &mut forall.proved_then_facts[0].verify_result,
        ));
        assert_eq!(
            (p.left_to_mid_cite_fact_id, p.mid_to_right_cite_fact_id),
            (first, second)
        );
        assert_eq!((p.left_to_mid_strict, p.mid_to_right_strict), expected);
    }
    let lean = compiler.compile_run(&run, "strict_chains").unwrap();
    for law in ["ltTrans", "ltLeTrans", "leLtTrans"] {
        assert!(lean.contains(&format!("Litex.{law} ")));
    }
}

#[test]
fn strict_order_chains_reject_wrong_strength_endpoint_and_visibility() {
    for index in 0..3 {
        for change in 0..6 {
            let (mut run, compiler) = super::execute(SOURCE);
            let foreign = super::forall_proof_mut(&mut run.statement_results[(index + 1) % 3])
                .assumed_dom_facts[0]
                .store_and_infer
                .primary_fact_id();
            let forall = super::forall_proof_mut(&mut run.statement_results[index]);
            let future = forall.proved_then_facts[0]
                .store_and_infer
                .primary_fact_id();
            let p = chain(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            ));
            match change {
                0 => {
                    p.left_to_mid_strict = false;
                    p.mid_to_right_strict = false;
                }
                1 => p.left_to_mid_strict = !p.left_to_mid_strict,
                2 => std::mem::swap(
                    &mut p.left_to_mid_cite_fact_id,
                    &mut p.mid_to_right_cite_fact_id,
                ),
                3 => p.mid_to_right_cite_fact_id = p.left_to_mid_cite_fact_id,
                4 => p.left_to_mid_cite_fact_id = foreign,
                5 => p.left_to_mid_cite_fact_id = future,
                _ => unreachable!(),
            }
            assert!(
                compiler.compile_run(&run, "invalid_strict_chain").is_err(),
                "index {index}, change {change}"
            );
        }
    }
}
