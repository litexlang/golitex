use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferEqualFactResult, InferResult, StoreInferredFactResult,
};

const CASES: [(&str, &str, &str); 4] = [
    ("a-k=b-k", "", "subCancelRightRight"),
    ("a*k=b*k", "    k!=0\n", "mulCancelRightRight"),
    ("a/k=b/k", "    k!=0\n", "divCancelCommonDenominator"),
    (
        "k/a=k/b",
        "    k!=0\n    a!=0\n    b!=0\n",
        "divCancelNonzeroNumerator",
    ),
];

fn source(seed: &str, guards: &str, carrier: &str) -> String {
    format!("forall a, b, k {carrier}:\n{guards}    {seed}\n    =>:\n        a=b\n")
}

fn rules_mut(store: &mut StoreFactAndInferResult) -> &mut Vec<InferEqualFactResult> {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &mut store.infer
    else {
        panic!("recorded equality inference group")
    };
    rules
}

fn parts_mut(
    rule: &mut InferEqualFactResult,
) -> (
    &mut FactId,
    &mut Obj,
    &mut VerifyFactResult,
    &mut VerifyFactResult,
    &mut VerifyFactResult,
    Vec<&mut VerifyFactResult>,
    &mut StoreInferredFactResult,
) {
    match rule {
        InferEqualFactResult::SubtractiveCancellation(p) => (
            &mut p.source_fact_id,
            &mut p.common_operand,
            &mut p.left_in_c_proof,
            &mut p.right_in_c_proof,
            &mut p.common_in_c_proof,
            Vec::new(),
            &mut p.derived,
        ),
        InferEqualFactResult::NonzeroFactorCancellation(p) => (
            &mut p.source_fact_id,
            &mut p.common_operand,
            &mut p.left_in_c_proof,
            &mut p.right_in_c_proof,
            &mut p.common_in_c_proof,
            vec![&mut p.factor_nonzero_proof],
            &mut p.derived,
        ),
        InferEqualFactResult::CommonDenominatorCancellation(p) => (
            &mut p.source_fact_id,
            &mut p.common_operand,
            &mut p.left_in_c_proof,
            &mut p.right_in_c_proof,
            &mut p.common_in_c_proof,
            vec![&mut p.denominator_nonzero_proof],
            &mut p.derived,
        ),
        InferEqualFactResult::NonzeroNumeratorCancellation(p) => (
            &mut p.source_fact_id,
            &mut p.common_operand,
            &mut p.left_in_c_proof,
            &mut p.right_in_c_proof,
            &mut p.common_in_c_proof,
            vec![
                &mut p.numerator_nonzero_proof,
                &mut p.left_denominator_nonzero_proof,
                &mut p.right_denominator_nonzero_proof,
            ],
            &mut p.derived,
        ),
        _ => panic!("one of the four newly supported cancellation variants"),
    }
}

#[test]
fn cancellation_inference_replays_all_direct_positions_and_carriers() {
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for (seed, guards, lemma) in CASES.into_iter().chain([
            ("k-a=k-b", "", "subCancelLeftLeft"),
            ("a*k=k*b", "    k!=0\n", "mulCancelRightLeft"),
            ("k*a=b*k", "    k!=0\n", "mulCancelLeftRight"),
            ("k*a=k*b", "    k!=0\n", "mulCancelLeftLeft"),
        ]) {
            let (result, compiler) = super::execute(&source(seed, guards, carrier));
            let output = super::compile_run(&result, &compiler, "cancellation_positions")
                .unwrap_or_else(|error| panic!("{carrier}, {seed}: {error}"));
            assert!(
                output.contains(&format!("Litex.{lemma}")),
                "{carrier}, {seed}"
            );
            assert!(!output.contains("sorry") && !output.contains("admit"));
        }
    }
}

#[test]
fn cancellation_inference_emits_original_ids_and_retained_formation() {
    for (seed, guards, lemma) in CASES {
        let (mut result, compiler) = super::execute(&source(seed, guards, "R"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
        let source_id = store.primary_fact_id();
        let (captured_source, _, _, _, _, _, captured) = parts_mut(&mut rules_mut(store)[0]);
        assert_eq!(*captured_source, source_id);
        let StoreFactResult::AtomicFact(stored) = &captured.store else {
            panic!("derived equality store")
        };
        let AtomicFact::EqualFact(_equal) = &stored.fact else {
            panic!("derived equality")
        };
        let derived_id = stored.fact_id;
        let output = super::compile_run(&result, &compiler, "cancellation_capture").unwrap();
        assert!(output.contains(&format!("have h_{}", derived_id.value())));
        assert!(output.contains(&format!("Litex.{lemma}")));
        assert!(output.contains(&format!("h_{}", source_id.value())));
    }
}

#[test]
fn cancellation_inference_replays_explicit_nested_and_mixed_steps() {
    for (seed, guards, residual, first, second) in [
        (
            "(a*x)*y=(b*x)*y",
            "    x!=0\n    y!=0\n",
            "a*x=b*x",
            "mulCancelRightRight",
            "mulCancelRightRight",
        ),
        (
            "(a-x)-y=(b-x)-y",
            "",
            "a-x=b-x",
            "subCancelRightRight",
            "subCancelRightRight",
        ),
        (
            "(a/x)/y=(b/x)/y",
            "    x!=0\n    y!=0\n",
            "a/x=b/x",
            "divCancelCommonDenominator",
            "divCancelCommonDenominator",
        ),
        (
            "(a-x)*y=(b-x)*y",
            "    y!=0\n",
            "a-x=b-x",
            "mulCancelRightRight",
            "subCancelRightRight",
        ),
        (
            "(a+x)/y=(b+x)/y",
            "    y!=0\n",
            "a+x=b+x",
            "divCancelCommonDenominator",
            "addCancelRightRight",
        ),
    ] {
        let source = format!(
            "forall a, b, x, y Q:\n{guards}    {seed}\n    =>:\n        {residual}\n        a=b\n"
        );
        let (result, compiler) = super::execute(&source);
        let output = super::compile_run(&result, &compiler, "nested_cancellation")
            .unwrap_or_else(|error| panic!("{seed}: {error}"));
        if first == second {
            assert_eq!(output.matches(&format!("Litex.{first}")).count(), 2);
        } else {
            assert!(output.contains(&format!("Litex.{first}")));
            assert!(output.contains(&format!("Litex.{second}")));
        }
    }
}

#[test]
fn cancellation_inference_rejects_changed_source_operand_and_member_evidence() {
    for (seed, guards, _) in CASES {
        for change in ["source", "operand", "member"] {
            let (mut result, compiler) = super::execute(&source(seed, guards, "C"));
            let forall = super::forall_proof_mut(&mut result.statement_results[0]);
            let unrelated = forall
                .introduced_params
                .defined_params
                .store_and_infer_results[0]
                .primary_fact_id();
            let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
            let (source_id, common, left, right, _, _, _) = parts_mut(&mut rules_mut(store)[0]);
            match change {
                "source" => *source_id = unrelated,
                "operand" => *common = super::number_object("7"),
                "member" => std::mem::swap(left, right),
                _ => unreachable!(),
            }
            super::compile_run(&result, &compiler, "invalid_cancellation").expect_err(
                "the selected certificate must preserve its source and ordered operands",
            );
        }
    }
}

#[test]
fn cancellation_inference_rejects_wrong_formation_subject_and_deleted_producer() {
    for (seed, guards, _) in CASES {
        for change in ["subject", "deleted"] {
            let (mut result, compiler) = super::execute(&source(seed, guards, "C"));
            let forall = super::forall_proof_mut(&mut result.statement_results[0]);
            let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
            if change == "deleted" {
                rules_mut(store).clear();
            } else {
                let (_, _, _, _, _, _, captured) = parts_mut(&mut rules_mut(store)[0]);
                let StoreFactResult::AtomicFact(stored) = &mut captured.store else {
                    panic!("atomic store")
                };
                let AtomicFact::EqualFact(equal) = &mut stored.fact else {
                    panic!("equality store")
                };
                equal.right = super::number_object("7");
            }
            let error = super::compile_run(&result, &compiler, "invalid_cancellation")
                .expect_err("wrong or missing captured stages do not become assumptions");
            if change == "subject" {
                assert!(error.route.ends_with("Identity"));
            }
            if change == "deleted" {
                assert_eq!(error.route, "FactId/Producer");
            }
        }
    }
}

#[test]
fn cancellation_inference_rejects_every_wrong_nonzero_subject() {
    for (seed, guards, _) in CASES.into_iter().skip(1) {
        let guard_count = if seed == "k/a=k/b" { 3 } else { 1 };
        for index in 0..guard_count {
            let (mut result, compiler) = super::execute(&source(seed, guards, "C"));
            let forall = super::forall_proof_mut(&mut result.statement_results[0]);
            let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
            let (_, _, _, _, member, mut nonzeros, _) = parts_mut(&mut rules_mut(store)[0]);
            let member_subject = super::atomic_proof_mut(member).fact.clone();
            super::atomic_proof_mut(nonzeros[index]).fact = member_subject;
            let error = super::compile_run(&result, &compiler, "wrong_nonzero")
                .expect_err("a membership fact cannot replace a nonzero certificate");
            assert_eq!(error.route, "Arithmetic/NonzeroSubject");
        }
    }
}

#[test]
fn cancellation_inference_rejects_future_and_closed_scope_member_citations() {
    for (seed, guards, _) in CASES {
        for closed in [false, true] {
            let single = source(seed, guards, "C");
            let input = if closed {
                // A distinct binder count forces two actual local introduction
                // scopes, rather than reusing the first whole forall by identity.
                let prefix = single.replace("a, b, k C", "a, b, k, closed_marker C");
                format!("{prefix}\n{single}")
            } else {
                single
            };
            let (mut result, compiler) = super::execute(&input);
            let forbidden = {
                let forall = super::forall_proof_mut(&mut result.statement_results[0]);
                let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
                parts_mut(&mut rules_mut(store)[0])
                    .6
                    .store
                    .primary_fact_id()
            };
            let forall =
                super::forall_proof_mut(&mut result.statement_results[usize::from(closed)]);
            let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
            let (_, _, _, _, member, _, _) = parts_mut(&mut rules_mut(store)[0]);
            let proof = super::atomic_proof_mut(member);
            proof.searched_proof = AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                    cite_fact_id: forbidden,
                    why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                },
            );
            let error = super::compile_run(&result, &compiler, "forbidden_cancellation_member")
                .expect_err("future inference and closed-scope stores are not visible premises");
            assert!(
                error.route == "Inference/FutureProducer" || error.route == "FactId/Resolution",
                "seed={seed}, closed={closed}: {error}"
            );
        }
    }
}

#[test]
fn nonzero_numerator_cursor_keeps_all_guard_and_nested_stages_ordered() {
    let input = source("k/(a-x)=k/(b-x)", "    k!=0\n    a-x!=0\n    b-x!=0\n", "Q")
        .replace("a, b, k Q", "a, b, k, x Q")
        .replace("        a=b", "        a-x=b-x\n        a=b");
    let (mut result, compiler) = super::execute(&input);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let store = &forall.assumed_dom_facts.last().unwrap().store_and_infer;
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &store.infer
    else {
        panic!("equality inference")
    };
    let InferEqualFactResult::NonzeroNumeratorCancellation(rule) = &rules[0] else {
        panic!("nonzero numerator cancellation")
    };
    let primary = rule.derived.store.primary_fact_id();
    assert_eq!(rule.derived.stored_fact_ids(), vec![primary]);
    let completed = SourcePosition::new(None, SourceOwner::Forall(forall), usize::MAX);
    let group = SourcePosition::new(Some(&completed), SourceOwner::EqualityInferences(rules), 0);
    let formation = SourcePosition::new(
        Some(&group),
        SourceOwner::NonzeroNumeratorInference(rule),
        6,
    );
    assert_eq!(
        formation
            .visible_fact(primary, &compiler.runtime)
            .unwrap_err()
            .route,
        "Inference/FutureProducer"
    );
    let stored = SourcePosition {
        before: 7,
        ..formation
    };
    stored
        .visible_fact(primary, &compiler.runtime)
        .expect("the primary store follows all six premises and WD");
}

#[test]
fn cancellation_inference_seed_cursor_blocks_all_future_family_stores() {
    for (seed, guards, _) in CASES {
        let (mut result, compiler) = super::execute(&source(seed, guards, "C"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let store = &forall.assumed_dom_facts.last().unwrap().store_and_infer;
        let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &store.infer
        else {
            panic!("equality inference group")
        };
        let derived = rules[0].stored_fact_ids()[0];
        // The enclosing header contains the seed's full infer tree; the current
        // original inference cursor still owns publication of each derived fact.
        let header = SourcePosition::new(None, SourceOwner::Forall(forall), usize::MAX);
        let pending = SourcePosition::new(Some(&header), SourceOwner::PropInference(store), 0);
        let error = pending
            .visible_fact(derived, &compiler.runtime)
            .expect_err("a completed outer header cannot bypass the active inference stage");
        assert_eq!(error.route, "Inference/FutureProducer", "{seed}");
        let completed = SourcePosition {
            before: rules.len(),
            ..pending
        };
        completed
            .visible_fact(derived, &compiler.runtime)
            .expect("the exact stored result becomes visible after its recorded rule");
    }
}

#[test]
fn cancellation_inference_requires_every_nested_and_nonzero_citation_stage() {
    for (seed, guards, residual) in [
        ("(a*x)*y=(b*x)*y", "    x!=0\n    y!=0\n", "a*x=b*x"),
        ("(a-x)-y=(b-x)-y", "", "a-x=b-x"),
        ("(a/x)/y=(b/x)/y", "    x!=0\n    y!=0\n", "a/x=b/x"),
    ] {
        let input = format!(
            "forall a, b, x, y Q:\n{guards}    {seed}\n    =>:\n        {residual}\n        a=b\n"
        );
        let (mut result, compiler) = super::execute(&input);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let store = &mut forall
            .proved_then_facts
            .first_mut()
            .unwrap()
            .store_and_infer;
        rules_mut(store).clear();
        let error = super::compile_run(&result, &compiler, "missing_nested_producer")
            .expect_err("the final citation cannot skip its nested original producer");
        assert_eq!(error.route, "FactId/Producer", "{seed}");
    }
    for (seed, guards, _) in CASES.into_iter().skip(1) {
        let guard_count = if seed == "k/a=k/b" { 3 } else { 1 };
        for guard in 0..guard_count {
            let (mut result, compiler) = super::execute(&source(seed, guards, "C"));
            let forall = super::forall_proof_mut(&mut result.statement_results[0]);
            let store = &mut forall.assumed_dom_facts.last_mut().unwrap().store_and_infer;
            let (_, _, _, _, _, mut nonzeros, captured) = parts_mut(&mut rules_mut(store)[0]);
            let forbidden = captured.store.primary_fact_id();
            super::atomic_proof_mut(nonzeros[guard]).searched_proof =
                AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                    AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                        cite_fact_id: forbidden,
                        why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                    },
                );
            let error = super::compile_run(&result, &compiler, "future_nonzero_citation")
                .expect_err("each nonzero premise precedes the equality it certifies");
            assert_eq!(
                error.route, "Inference/FutureProducer",
                "{seed}, guard={guard}"
            );
        }
    }
}
