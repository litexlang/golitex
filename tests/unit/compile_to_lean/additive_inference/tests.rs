use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::json_output::project_stmt_detailed;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferEqualFactAdditiveCancellationResult, InferEqualityResult,
    InferFactResult,
};

const SOURCE: &str = "forall a, b, k C:\n    a+k=b+k\n    =>:\n        a=b\n";

fn additive_rule_mut(
    store: &mut StoreFactAndInferResult,
) -> &mut InferEqualFactAdditiveCancellationResult {
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &mut store.infer
    else {
        panic!("stored equality inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferEqualityResult::AdditiveCancellation(rule) => Some(rule),
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
    let FactWellDefinedProof::Equality(wd) = &rule.derived.well_defined else {
        panic!("retained equality formation")
    };
    let StoreFactResult::AtomicFact(derived) = &rule.derived.store else {
        panic!("derived equality store")
    };
    let AtomicFact::EqualFact(equal) = &derived.fact else {
        panic!("remaining equality")
    };
    assert_eq!(wd.left.obj().ir(), equal.left.ir());
    assert_eq!(wd.right.obj().ir(), equal.right.ir());
    let derived_id = derived.fact_id;
    let output = super::compile_run(&result, &compiler, "captured_additive")
        .expect("captured formation and source proof replay");
    assert!(output.contains(&format!("have h_{}", derived_id.value())));
    assert!(output.contains(&format!("h_{}", source_id.value())));
    let detail =
        project_stmt_detailed(&result.statement_results[0], &compiler.runtime).stringify_pretty();
    assert!(detail.contains("AdditiveCancellation") && detail.contains("well_defined"));
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
    for change in ["wd", "deleted"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let store = &mut forall.assumed_dom_facts[0].store_and_infer;
        if change == "wd" {
            let FactWellDefinedProof::Equality(wd) =
                &mut additive_rule_mut(store).derived.well_defined
            else {
                panic!("retained equality formation")
            };
            std::mem::swap(&mut wd.left, &mut wd.right);
        } else {
            let Some(InferFactResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
                &mut store.infer
            else {
                panic!("equality inference")
            };
            rules.clear();
        }
        let error = super::compile_run(&result, &compiler, change)
            .expect_err("missing or wrong original evidence is rejected");
        assert_eq!(
            error.route,
            if change == "wd" {
                "WD/Subject"
            } else {
                "FactId/Producer"
            }
        );
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

    let nested = "forall a, b, x, y Q:\n    (a+x)+y=(b+x)+y\n    a+x=b+x\n    =>:\n        a=b\n";
    let (mut result, compiler) = super::execute(nested);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &mut forall.assumed_dom_facts[1].store_and_infer.infer
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

#[test]
fn additive_inference_wd_cursor_keeps_nested_constructors_after_the_current_stage() {
    let source = "forall a, b, x, y Q:\n    (a+x)+y=(b+x)+y\n    =>:\n        a=b\n991=991\n";
    let (mut result, compiler) = super::execute(source);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(marker)) =
        result.statement_results.pop().unwrap()
    else {
        panic!("the isolated numeric constructor marker")
    };
    let VerifyFactResult::Equality(marker) = marker.verify_result else {
        panic!("numeric equality formation")
    };
    let VerifyEqualityResult::Success(marker) = *marker else {
        panic!("successful numeric marker")
    };
    let marker_wd = marker.well_defined_proof.left;
    let marker_object = marker_wd.obj().clone();
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let nested_id = {
        let outer = additive_rule_mut(&mut forall.assumed_dom_facts[0].store_and_infer);
        let nested = outer;
        let FactWellDefinedProof::Equality(formation) = &mut nested.derived.well_defined else {
            panic!("nested cancellation formation")
        };
        // This visitor-only marker occurs in the nested retained WD, with its
        // original standalone statement removed from the source-result prefix.
        formation.left = marker_wd;
        nested.derived.store.primary_fact_id()
    };
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) =
        &forall.assumed_dom_facts[0].store_and_infer.infer
    else {
        panic!("original equality inference group")
    };
    let outer = rules
        .iter()
        .find_map(|rule| match rule {
            InferEqualityResult::AdditiveCancellation(rule) => Some(rule),
            _ => None,
        })
        .unwrap();
    let primary_id = outer.derived.store.primary_fact_id();
    let completed_source = SourcePosition::new(None, SourceOwner::Forall(forall), 5);
    for parent in [None, Some(&completed_source)] {
        let group = SourcePosition::new(parent, SourceOwner::EqualityInferences(rules), 0);
        let current = SourcePosition::new(Some(&group), SourceOwner::AdditiveInference(outer), 3);
        assert!(current
            .with_visible_wd(&marker_object, &mut |_, _| Ok(()))
            .unwrap()
            .is_none());
        let completed = SourcePosition {
            before: 4,
            ..current
        };
        assert!(completed
            .with_visible_wd(&marker_object, &mut |_, _| Ok(()))
            .unwrap()
            .is_some());
        if parent.is_some() {
            assert_eq!(primary_id, nested_id);
            assert_eq!(
                current
                    .visible_fact(primary_id, &compiler.runtime)
                    .unwrap_err()
                    .route,
                "Inference/FutureProducer"
            );
            completed
                .visible_fact(primary_id, &compiler.runtime)
                .expect("the direct conclusion follows its original WD");
        }
    }
}
