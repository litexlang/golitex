use crate::json_output::project_stmt_detailed;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferEqualFactAdditiveCancellationResult, InferEqualFactResult,
    InferResult,
};

const SOURCE: &str = "forall a, b, k C:\n    a+k=b+k\n    =>:\n        a=b\n";

fn additive_rule_mut(
    store: &mut StoreFactAndInferResult,
) -> &mut InferEqualFactAdditiveCancellationResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &mut store.infer
    else {
        panic!("stored equality inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferEqualFactResult::AdditiveCancellation(rule) => Some(rule),
            _ => None,
        })
        .expect("actual additive cancellation")
}

#[test]
fn additive_inference_replays_original_example_and_all_direct_positions() {
    let original = include_str!("../../../../examples/infer/equal/additive_cancellation.lit");
    let (result, compiler) = super::execute(original);
    let output = super::compile_run(&result, &compiler, "original_additive_example")
        .expect("all three original forms replay");
    assert_eq!(output.matches("Litex.addCancel").count(), 4);
    assert!(!output.contains("sorry") && !output.contains("admit"));
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for (seed, lemma) in [
            ("a+k=b+k", "addCancelRightRight"),
            ("a+k=k+b", "addCancelRightLeft"),
            ("k+a=b+k", "addCancelLeftRight"),
            ("k+a=k+b", "addCancelLeftLeft"),
        ] {
            let source = format!("forall a, b, k {carrier}:\n    {seed}\n    =>:\n        a=b\n");
            let (result, compiler) = super::execute(&source);
            let output = super::compile_run(&result, &compiler, "direct_positions")
                .unwrap_or_else(|error| panic!("{carrier}, {seed}: {error}"));
            assert!(output.contains(&format!("Litex.{lemma}")));
        }
    }
}

#[test]
fn additive_inference_retains_derived_wd_and_original_ids() {
    let (mut result, compiler) = super::execute(SOURCE);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let store = &mut forall.assumed_dom_facts[0].store_and_infer;
    let source_id = store.primary_fact_id();
    let rule = additive_rule_mut(store);
    assert_eq!(rule.source_fact_id, source_id);
    let StoreFactResult::AtomicFact(derived) = &rule.derived.store else {
        panic!("derived equality store")
    };
    let AtomicFact::EqualFact(_equal) = &derived.fact else {
        panic!("remaining equality")
    };
    let derived_id = derived.fact_id;
    let output = super::compile_run(&result, &compiler, "captured_additive")
        .expect("captured formation and source proof replay");
    assert!(output.contains(&format!("have h_{}", derived_id.value())));
    assert!(output.contains(&format!("h_{}", source_id.value())));
    let detail =
        project_stmt_detailed(&result.statement_results[0], &compiler.runtime).stringify_pretty();
    assert!(detail.contains("AdditiveCancellation"));
}

#[test]
fn additive_inference_rejects_changed_seed_shared_operand_and_members() {
    for change in ["seed", "shared", "members"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let unrelated = forall
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id();
        let rule = additive_rule_mut(&mut forall.assumed_dom_facts[0].store_and_infer);
        match change {
            "seed" => rule.source_fact_id = unrelated,
            "shared" => rule.common_operand = super::number_object("7"),
            "members" => std::mem::swap(&mut rule.left_in_c_proof, &mut rule.right_in_c_proof),
            _ => unreachable!(),
        }
        let error = super::compile_run(&result, &compiler, change)
            .expect_err("a changed inference certificate is not replay evidence");
        assert!(
            error.route.starts_with("Inference/Additive") || error.route == "WD/ArithmeticDomain",
            "{change}: {error}"
        );
    }
}

#[test]
fn additive_inference_rejects_wrong_derived_wd_and_deleted_inferences() {
    for change in ["deleted"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let store = &mut forall.assumed_dom_facts[0].store_and_infer;
        let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
            &mut store.infer
        else {
            panic!("equality inference")
        };
        rules.clear();
        let error = super::compile_run(&result, &compiler, change)
            .expect_err("missing or wrong original evidence is rejected");
        assert_eq!(error.route, "FactId/Producer");
    }
}

#[test]
fn additive_inference_rejects_changed_derived_subject_and_missing_nested_step() {
    let (mut result, compiler) = super::execute(SOURCE);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let rule = additive_rule_mut(&mut forall.assumed_dom_facts[0].store_and_infer);
    let StoreFactResult::AtomicFact(stored) = &mut rule.derived.store else {
        panic!("derived atomic store")
    };
    let AtomicFact::EqualFact(equal) = &mut stored.fact else {
        panic!("derived equality")
    };
    equal.right = super::number_object("7");
    let error = super::compile_run(&result, &compiler, "changed_derived_subject")
        .expect_err("the original exact fact ID cannot acquire another subject");
    assert_eq!(error.route, "Inference/AdditiveIdentity");

    let nested =
        "forall a, b, x, y Q:\n    (a+x)+y=(b+x)+y\n    =>:\n        a+x=b+x\n        a=b\n";
    let (mut result, compiler) = super::execute(nested);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &mut forall.proved_then_facts[0].store_and_infer.infer
    else {
        panic!("explicit second cancellation seed")
    };
    rules.clear();
    let error = super::compile_run(&result, &compiler, "missing_nested_cancellation")
        .expect_err("the second nested cancellation has its own recorded producer");
    assert_eq!(error.route, "FactId/Producer");
}

#[test]
fn additive_inference_rejects_future_and_closed_scope_membership_citations() {
    for closed in [false, true] {
        let source = if closed {
            format!("{SOURCE}\nforall a, b, k C:\n    k+a=b+k\n    =>:\n        a=b\n")
        } else {
            SOURCE.into()
        };
        let (mut result, compiler) = super::execute(&source);
        let index = usize::from(closed);
        let forbidden = {
            let forall = super::forall_proof_mut(&mut result.statement_results[0]);
            additive_rule_mut(&mut forall.assumed_dom_facts[0].store_and_infer)
                .derived
                .store
                .primary_fact_id()
        };
        let forall = super::forall_proof_mut(&mut result.statement_results[index]);
        let rule = additive_rule_mut(&mut forall.assumed_dom_facts[0].store_and_infer);
        let proof = super::atomic_proof_mut(&mut rule.common_in_c_proof);
        proof.searched_proof = AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: forbidden,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
        let error = super::compile_run(&result, &compiler, "forbidden_member")
            .expect_err("inference cannot cite its future result or a closed scope");
        assert!(
            error.route == "Inference/FutureProducer" || error.route == "FactId/Resolution",
            "closed={closed}: {error}"
        );
    }
}

#[test]
fn additive_inference_keeps_other_cancellation_families_independent() {
    for (seed, guards) in [
        ("a*k=b*k", "    k!=0\n"),
        ("a-k=b-k", ""),
        ("a/k=b/k", "    k!=0\n"),
        ("k/a=k/b", "    k!=0\n    a!=0\n    b!=0\n"),
    ] {
        let source = format!("forall a, b, k C:\n{guards}    {seed}\n    =>:\n        a=b\n");
        let (result, compiler) = super::execute(&source);
        let output = super::compile_run(&result, &compiler, "independent_cancellation")
            .expect("each selected cancellation has its own evidence consumer");
        assert!(!output.contains("Litex.addCancel"), "{seed}");
    }
}
