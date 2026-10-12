use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferEqualityResult, InferFactResult, StoreInferredFactResult,
};

fn execute(source: &str) -> (Runtime, RunLitexCodeResult) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source execution");
    assert!(result.success && result.session_error.is_none(), "{source}");
    assert_eq!(result.statement_results.len(), 1);
    (runtime, result)
}

fn forall(run: &RunLitexCodeResult) -> &VerifyForallFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = &run.statement_results[0]
    else {
        panic!("successful forall statement")
    };
    let VerifyFactResult::ForallFact(proof) = &success.verify_result else {
        panic!("forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_ref()
    else {
        panic!("local forall proof")
    };
    proof
}

fn rules(store: &StoreFactAndInferResult) -> &[InferEqualityResult] {
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &store.infer
    else {
        panic!("stored equality inference")
    };
    rules
}

fn captured(rule: &InferEqualityResult) -> (FactId, &StoreInferredFactResult) {
    match rule {
        InferEqualityResult::SubtractiveCancellation(rule) => (rule.source_fact_id, &rule.derived),
        InferEqualityResult::NonzeroFactorCancellation(rule) => {
            (rule.source_fact_id, &rule.derived)
        }
        InferEqualityResult::CommonDenominatorCancellation(rule) => {
            (rule.source_fact_id, &rule.derived)
        }
        InferEqualityResult::NonzeroNumeratorCancellation(rule) => {
            (rule.source_fact_id, &rule.derived)
        }
        _ => panic!("one of the four nonadditive cancellation captures"),
    }
}

fn assert_original_capture(
    proof: &VerifyForallFactSuccess,
    store: &StoreFactAndInferResult,
) -> Vec<FactId> {
    let mut ids = Vec::new();
    for rule in rules(store) {
        let (source_id, capture) = captured(rule);
        assert_eq!(source_id, store.primary_fact_id());
        let FactWellDefinedProof::Equality(formation) = &capture.well_defined else {
            panic!("original derived equality formation")
        };
        let StoreFactResult::AtomicFact(derived) = &capture.store else {
            panic!("derived atomic store")
        };
        let AtomicFact::EqualFact(equality) = &derived.fact else {
            panic!("derived equality")
        };
        assert_eq!(derived.fact_id, equality.fact_id);
        assert_eq!(formation.left.obj().ir(), equality.left.ir());
        assert_eq!(formation.right.obj().ir(), equality.right.ir());
        assert_ne!(derived.fact_id, source_id);
        assert_eq!(
            proof.local_env.facts.facts_by_id.get(&derived.fact_id),
            Some(&Fact::AtomicFact(derived.fact.clone())),
            "capture keeps the exact fact actually published in the local scope"
        );
        let descendants = vec![derived.fact_id];
        assert_eq!(rule.stored_fact_ids(), descendants);
        ids.extend(descendants);
    }
    assert_eq!(
        store
            .infer
            .as_ref()
            .expect("seed inference")
            .stored_fact_ids(),
        ids
    );
    ids
}

fn assert_json_captures(value: &JsonValue) -> usize {
    match value {
        JsonValue::Object(object) => {
            let is_capture = object.get("rule").is_some_and(|rule| {
                matches!(
                    rule.as_str().ok(),
                    Some(
                        "SubtractiveCancellation"
                            | "NonzeroFactorCancellation"
                            | "CommonDenominatorCancellation"
                            | "NonzeroNumeratorCancellation"
                    )
                )
            });
            if is_capture {
                let derived = object.get("derived").unwrap().as_object().unwrap();
                assert!(derived.get("well_defined").is_some());
                assert!(derived.get("store").is_some());
            }
            usize::from(is_capture)
                + object
                    .iter()
                    .map(|(_, child)| assert_json_captures(child))
                    .sum::<usize>()
        }
        JsonValue::Array(children) => children.iter().map(assert_json_captures).sum(),
        _ => 0,
    }
}

fn nonzero_cite(proof: &VerifyFactResult) -> FactId {
    let VerifyFactResult::AtomicExceptEquality(proof) = proof else {
        panic!("nonzero verification")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful nonzero proof")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &proof.searched_proof
    else {
        panic!("original explicit nonzero fact citation")
    };
    cite.cite_fact_id
}

#[test]
fn nonadditive_cancellation_capture_keeps_original_wd_store_and_ids_in_all_positions() {
    for (seed, guards) in [
        ("a-k=b-k", ""),
        ("k-a=k-b", ""),
        ("a*k=b*k", "    k!=0\n"),
        ("a*k=k*b", "    k!=0\n"),
        ("k*a=b*k", "    k!=0\n"),
        ("k*a=k*b", "    k!=0\n"),
        ("a/k=b/k", "    k!=0\n"),
        ("k/a=k/b", "    k!=0\n    a!=0\n    b!=0\n"),
    ] {
        let source = format!("forall a, b, k C:\n{guards}    {seed}\n    =>:\n        a=b\n");
        let (runtime, run) = execute(&source);
        let proof = forall(&run);
        let store = &proof.assumed_dom_facts.last().unwrap().store_and_infer;
        let ids = assert_original_capture(proof, store);
        assert_eq!(ids.len(), 1, "{seed}");
        assert_eq!(
            store.stored_fact_ids(),
            [vec![store.primary_fact_id()], ids].concat()
        );
        assert_eq!(
            assert_json_captures(&project_stmt_detailed(&run.statement_results[0], &runtime)),
            1,
            "{seed}"
        );
        assert!(project_stmt_normal(&run.statement_results[0], &runtime)
            .stringify()
            .contains("a = b"));
    }
}

#[test]
fn nonadditive_cancellation_capture_keeps_all_original_guard_citations_in_order() {
    for seed in ["a*k=b*k", "a/k=b/k", "k/a=k/b"] {
        let source = format!(
            "forall a, b, k C:\n    k!=0\n    a!=0\n    b!=0\n    {seed}\n    =>:\n        a=b\n"
        );
        let (_, run) = execute(&source);
        let proof = forall(&run);
        let [rule] = rules(&proof.assumed_dom_facts[3].store_and_infer) else {
            panic!("one cancellation")
        };
        let guards: Vec<&VerifyFactResult> = match rule {
            InferEqualityResult::NonzeroFactorCancellation(rule) => {
                vec![&rule.factor_nonzero_proof]
            }
            InferEqualityResult::CommonDenominatorCancellation(rule) => {
                vec![&rule.denominator_nonzero_proof]
            }
            InferEqualityResult::NonzeroNumeratorCancellation(rule) => vec![
                &rule.numerator_nonzero_proof,
                &rule.left_denominator_nonzero_proof,
                &rule.right_denominator_nonzero_proof,
            ],
            _ => panic!("guarded cancellation"),
        };
        let actual: Vec<_> = guards.into_iter().map(nonzero_cite).collect();
        let expected: Vec<_> = proof.assumed_dom_facts[..actual.len()]
            .iter()
            .map(|assumption| assumption.store_and_infer.primary_fact_id())
            .collect();
        assert_eq!(actual, expected, "{seed}");
    }
}

#[test]
fn nonadditive_cancellation_capture_keeps_nested_inference_and_composite_formation() {
    for source in [
        "forall a, b, k, t C:\n    (k-a)-t=(k-b)-t\n    =>:\n        a=b\n",
        "forall a, b, x, y C:\n    x!=0\n    y!=0\n    (a*x)*y=(b*x)*y\n    =>:\n        a=b\n",
        "forall a, b, k, t C:\n    k!=0\n    (a-t)/k=(b-t)/k\n    =>:\n        a=b\n",
        "forall a, b, k, t C*:\n    (k/a)/t=(k/b)/t\n    =>:\n        a=b\n",
    ] {
        let (runtime, run) = execute(source);
        let proof = forall(&run);
        let seed = &proof.assumed_dom_facts.last().unwrap().store_and_infer;
        let ids = assert_original_capture(proof, seed);
        assert_eq!(ids.len(), 2, "{source}");
        assert_eq!(
            assert_json_captures(&project_stmt_detailed(&run.statement_results[0], &runtime)),
            2,
            "{source}"
        );
        assert_ne!(ids[0], ids[1]);
    }
}

#[test]
fn nonadditive_cancellation_capture_does_not_retrigger_with_a_future_guard() {
    let (_, run) =
        execute("forall a, b, k C:\n    a*k=b*k\n    k!=0\n    a*k=b*k\n    =>:\n        a=b\n");
    let proof = forall(&run);
    let first = &proof.assumed_dom_facts[0].store_and_infer;
    let repeated = &proof.assumed_dom_facts[2].store_and_infer;
    assert!(rules(first).is_empty());
    assert_eq!(first.stored_fact_ids(), vec![first.primary_fact_id()]);
    assert_eq!(assert_original_capture(proof, repeated).len(), 1);
    let [InferEqualityResult::NonzeroFactorCancellation(rule)] = rules(repeated) else {
        panic!("the later explicit seed triggers cancellation")
    };
    assert_eq!(
        nonzero_cite(&rule.factor_nonzero_proof),
        proof.assumed_dom_facts[1].store_and_infer.primary_fact_id()
    );
}
