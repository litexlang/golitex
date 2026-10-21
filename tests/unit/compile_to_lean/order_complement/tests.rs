use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less_equal::LessEqualFactSearchProofByBuiltinRule, greater_equal::GreaterEqualFactSearchProofByBuiltinRule, order_complement::FromKnownOrderComplementBuiltinRuleProof,
not_less::NotLessFactSearchProofByBuiltinRule,
not_greater::NotGreaterFactSearchProofByBuiltinRule,
not_less_equal::NotLessEqualFactSearchProofByBuiltinRule,
not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule};

const SOURCE: &str = "forall x, y R:\n    not x > y\n    =>:\n        x <= y\n";

fn complement(result: &mut RunLitexCodeResult) -> &mut FromKnownOrderComplementBuiltinRuleProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(
                NotLessFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(
                NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(
                NotLessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(
                NotGreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        _ => panic!("original order complement"),
    }
}

#[test]
fn weak_order_complement_consumes_the_original_real_carriers() {
    let (mut result, compiler) = super::execute(SOURCE);
    assert_eq!(complement(&mut result).real_carrier_proofs.len(), 2);
    assert!(compiler
        .compile_run(&result, "order_complement")
        .unwrap()
        .contains("le_of_not_gt"));
}

#[test]
fn weak_order_complement_rejects_exchanged_carriers_and_changed_premise() {
    for change_premise in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = complement(&mut result);
        if change_premise {
            let AtomicFact::NotGreaterFact(fact) = &mut proof.premise_proof.fact else {
                unreachable!()
            };
            std::mem::swap(&mut fact.left, &mut fact.right);
        } else {
            proof.real_carrier_proofs.swap(0, 1);
        }
        compiler
            .compile_run(&result, "invalid_complement")
            .expect_err("original premise and ordered carriers are required");
    }
}

#[test]
fn weak_order_complement_replays_greater_equal_and_rejects_wrong_carrier_order() {
    let (mut result, compiler) =
        super::execute("forall x, y R:\n    not x < y\n    =>:\n        x >= y\n");
    compiler.compile_run(&result, "ge_complement").unwrap();
    complement(&mut result).real_carrier_proofs.swap(0, 1);
    assert!(compiler.compile_run(&result, "wrong_ge_carriers").is_err());
}

#[test]
fn negative_order_complements_consume_ordered_real_carriers() {
    for (premise, conclusion) in [
        ("x <= y", "not x > y"),
        ("x >= y", "not x < y"),
        ("x < y", "not x >= y"),
        ("x > y", "not x <= y"),
    ] {
        let source = format!("forall x, y R:\n    {premise}\n    =>:\n        {conclusion}\n");
        let (mut result, compiler) = super::execute(&source);
        assert_eq!(complement(&mut result).real_carrier_proofs.len(), 2);
        compiler.compile_run(&result, "negative_order").unwrap();
        complement(&mut result).real_carrier_proofs.swap(0, 1);
        assert!(compiler
            .compile_run(&result, "wrong_negative_carriers")
            .is_err());
    }
}
