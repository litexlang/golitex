use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::TemplateMembershipProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferInFactResult, InferResult, InferTemplateMembershipResult,
};

const SOURCE: &str = r#"template<S set>:
    have replay_pairs set = cart(S, S)
(1, 2) $in \replay_pairs<R>
(3, 4) $in \replay_pairs<R>
(1, 2) $in cart(R, R)
"#;
const NESTED: &str = r#"template<S set>:
    have replay_carrier set = S
1 $in \replay_carrier<\replay_carrier<R>>
"#;
const FUNCTION: &str = r#"template<A, B nonempty_set>:
    have replay_maps set = fn(x A) B
fn(x R) R {x + 1} $in \replay_maps<R, R>
fn(x R) R {x + 1} $in fn(x R) R
"#;
const GUARDED: &str = r#"template<S set: $is_nonempty_set(S)>:
    have replay_guarded_pairs set = cart(S, S)
(5, 6) $in \replay_guarded_pairs<R>
"#;
const STOP: &str = r#"template<S set>:
    have replay_carrier set = S
have replay_real_alias set = R
1 $in \replay_carrier<replay_real_alias>
"#;

fn inferred(statement: &ExecStmtResult) -> &InferTemplateMembershipResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = statement else {
        panic!("membership statement")
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
        &statement.store_and_infer_result.infer
    else {
        panic!("membership inference")
    };
    rules
        .iter()
        .find_map(|rule| match rule {
            InferInFactResult::Template(proof) => Some(proof),
            _ => None,
        })
        .expect("actual template inference")
}

fn inferred_mut(statement: &mut ExecStmtResult) -> &mut InferTemplateMembershipResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = statement else {
        panic!("membership statement")
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
        &mut statement.store_and_infer_result.infer
    else {
        panic!("membership inference")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferInFactResult::Template(proof) => Some(proof),
            _ => None,
        })
        .expect("actual template inference")
}

fn atomic(statement: &mut ExecStmtResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = statement else {
        panic!("verified membership")
    };
    super::atomic_proof_mut(&mut statement.verify_result)
}

fn selected(statement: &mut ExecStmtResult) -> &mut TemplateMembershipProof {
    let AtomicExceptEqualityFactSearchedProof::ByTemplateMembership(proof) =
        &mut atomic(statement).searched_proof
    else {
        panic!("actual template-membership conversion")
    };
    proof
}

#[test]
fn template_membership_replays_the_actual_cartesian_residual() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = selected(&mut result.statement_results[1]);
    assert_eq!(proof.expansions.len(), 1);
    selected(&mut result.statement_results[2]);
    assert!(matches!(
        atomic(&mut result.statement_results[3]).searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
    ));
    let output = super::compile_run(&result, &compiler, "template_membership").unwrap();
    assert!(output.contains("Litex.tupleInCart"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn template_membership_replays_nested_same_owner_instances() {
    let (mut result, compiler) = super::execute(NESTED);
    let proof = selected(&mut result.statement_results[1]);
    assert_eq!(proof.expansions.len(), 2);
    super::compile_run(&result, &compiler, "nested_template_membership").unwrap();
}

#[test]
fn template_membership_replays_the_original_function_set_search() {
    let (mut result, compiler) = super::execute(FUNCTION);
    selected(&mut result.statement_results[1]);
    assert!(matches!(
        atomic(&mut result.statement_results[2]).searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
    ));
    super::compile_run(&result, &compiler, "function_template_membership").unwrap();
}

#[test]
fn template_membership_keeps_its_guarded_instance_formation() {
    let (mut result, compiler) = super::execute(GUARDED);
    selected(&mut result.statement_results[1]);
    super::compile_run(&result, &compiler, "guarded_template_membership").unwrap();
}

#[test]
fn template_membership_stops_conversion_at_an_ordinary_identifier() {
    let (mut result, compiler) = super::execute(STOP);
    let proof = selected(&mut result.statement_results[2]);
    assert_eq!(proof.expansions.len(), 1);
    assert!(matches!(proof.expansions[0].set, Obj::Identifier(_)));
    super::compile_run(&result, &compiler, "template_identifier_boundary").unwrap();
}

#[test]
fn template_membership_inference_rejects_wrong_source_stores_and_native_projections() {
    for change in [
        "missing_store",
        "source_id",
        "store_subject",
        "native_order",
        "native_missing",
    ] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = inferred_mut(&mut result.statement_results[1]);
        match change {
            "missing_store" => {
                proof.stores.pop();
            }
            "source_id" => proof.source_fact_id = FactId::new(u64::MAX),
            "store_subject" => {
                let StoreFactResult::AtomicFact(stored) = &mut proof.stores[0].store else {
                    unreachable!()
                };
                let AtomicFact::InFact(member) = &mut stored.fact else {
                    unreachable!()
                };
                member.set = Obj::StandardSet(StandardSet::Z);
            }
            "native_order" | "native_missing" => {
                let native = proof
                    .native_rules
                    .iter_mut()
                    .find_map(|rule| match rule {
                        InferInFactResult::CartCoordinates(proof) => Some(proof),
                        _ => None,
                    })
                    .expect("actual native coordinate inference");
                if change == "native_order" {
                    native.coordinates[0].coordinate_index = 1;
                } else {
                    native.coordinates.pop();
                }
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["TemplateInference/", "Store/", "CartInference/"],
        );
    }
}

#[test]
fn template_membership_inference_keeps_expansion_stores_in_order() {
    let (mut result, compiler) = super::execute(NESTED);
    let proof = inferred_mut(&mut result.statement_results[1]);
    assert_eq!(proof.stores.len(), 2);
    proof.stores.swap(0, 1);
    proof.expansions.swap(0, 1);
    super::phase2_rejected(
        &result,
        &compiler,
        "reordered expansion stores",
        &["TemplateMembership/"],
    );
}

#[test]
fn template_membership_inference_publishes_each_original_stage_only_afterward() {
    let (result, compiler) = super::execute(SOURCE);
    let proof = inferred(&result.statement_results[1]);
    let expanded = proof.stores[0].primary_fact_id();
    let coordinate = proof
        .native_rules
        .iter()
        .find_map(|rule| match rule {
            InferInFactResult::CartCoordinates(proof) => {
                Some(proof.coordinates[0].membership.primary_fact_id())
            }
            _ => None,
        })
        .expect("actual native coordinate store");
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let pending = SourcePosition::new(Some(&root), SourceOwner::TemplateInference(proof), 0);
    assert_eq!(
        pending
            .visible_fact(expanded, &compiler.runtime)
            .unwrap_err()
            .route,
        "Inference/FutureProducer"
    );
    let converted = SourcePosition {
        before: 1,
        ..pending
    };
    converted.visible_fact(expanded, &compiler.runtime).unwrap();
    assert_eq!(
        converted
            .visible_fact(coordinate, &compiler.runtime)
            .unwrap_err()
            .route,
        "Inference/FutureProducer"
    );
    let projected = SourcePosition {
        before: 2,
        ..pending
    };
    projected
        .visible_fact(coordinate, &compiler.runtime)
        .unwrap();
}

#[test]
fn template_membership_retains_false_and_missing_guard_source_controls() {
    for source in [
        GUARDED.replace("<R>", "<{}>"),
        SOURCE.replace(
            "(1, 2) $in \\replay_pairs<R>",
            "(1, i) $in \\replay_pairs<R>",
        ),
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

#[test]
fn template_membership_rejects_missing_changed_and_repeated_expansions() {
    for change in ["missing", "element", "carrier", "duplicate", "original_id"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let original_id = atomic(&mut result.statement_results[1]).fact.fact_id();
        let proof = selected(&mut result.statement_results[1]);
        match change {
            "missing" => proof.expansions.clear(),
            "element" => proof.expansions[0].element = Obj::StandardSet(StandardSet::R),
            "carrier" => proof.expansions[0].set = Obj::StandardSet(StandardSet::R),
            "duplicate" => proof.expansions.push(proof.expansions[0].clone()),
            "original_id" => proof.expansions[0].fact_id = original_id,
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["TemplateMembership/"]);
    }
}

#[test]
fn template_membership_cannot_use_another_original_residual() {
    let (mut result, compiler) = super::execute(SOURCE);
    let (first, second) = result.statement_results.split_at_mut(2);
    std::mem::swap(
        &mut selected(&mut first[1]).residual,
        &mut selected(&mut second[0]).residual,
    );
    assert!(super::compile_run(&result, &compiler, "swapped_template_residual").is_err());
}
