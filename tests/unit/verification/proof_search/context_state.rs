//! Contracts for explicit proof-search state and scope transitions.

use crate::fact::{AtomicFact, Fact};
use crate::parsing::Tokenizer;
use crate::result::{SuccessFactProofNode, SuccessFactProofResult, VerifyFactResult};
use crate::runtime::Runtime;
use crate::statement::Stmt;
use crate::verification::VerifyState;
use std::rc::Rc;

#[test]
fn verify_state_constructors_select_the_expected_semantics() {
    let initial = VerifyState::initial();
    assert_eq!(initial.proof_search_round, 0);
    assert!(initial.is_initial_round());

    let final_round = VerifyState::final_round();
    assert_eq!(final_round.proof_search_round, 2);
    assert!(!final_round.is_initial_round());
}

#[test]
fn verify_state_transitions_change_only_the_named_dimension() {
    let next_round = VerifyState::initial().with_next_round();
    assert_eq!(next_round.proof_search_round, 1);
    assert!(!next_round.is_initial_round());
}

#[test]
fn one_proof_search_reuses_the_exact_successful_atomic_proof() {
    let mut runtime = new_test_runtime();
    let fact = parse_atomic_fact(&mut runtime, "1 < 2");
    let state = VerifyState::initial();

    let first = runtime
        .verify_atomic_fact(&fact, &state)
        .expect("first verification should succeed");
    let first_source = direct_verification(&first);
    let second = runtime
        .verify_atomic_fact(&fact, &state)
        .expect("second verification should reuse the search-local proof");

    assert!(Rc::ptr_eq(&first_source, reused_verification(&second)));
    assert_eq!(second.fact_id(), None);
}

#[test]
fn a_fresh_proof_search_does_not_inherit_an_old_memo() {
    let mut runtime = new_test_runtime();
    let fact = parse_atomic_fact(&mut runtime, "1 < 2");

    let first = runtime
        .verify_atomic_fact(&fact, &VerifyState::initial())
        .expect("first search should succeed");
    let first_source = direct_verification(&first);
    let second = runtime
        .verify_atomic_fact(&fact, &VerifyState::initial())
        .expect("fresh search should verify independently");
    let second_source = direct_verification(&second);

    assert!(!Rc::ptr_eq(&first_source, &second_source));
}

#[test]
fn child_scope_sees_parent_memos_but_parent_does_not_see_child_memos() {
    let mut runtime = new_test_runtime();
    let parent_fact = parse_atomic_fact(&mut runtime, "1 < 2");
    let child_fact = parse_atomic_fact(&mut runtime, "2 < 3");
    let parent = VerifyState::initial();
    let parent_result = runtime
        .verify_atomic_fact(&parent_fact, &parent)
        .expect("parent proof should succeed");
    let parent_source = direct_verification(&parent_result);

    let child = parent.with_child_proof_scope();
    let inherited = runtime
        .verify_atomic_fact(&parent_fact, &child)
        .expect("child should see its parent proof");
    assert!(Rc::ptr_eq(&parent_source, reused_verification(&inherited)));

    runtime
        .verify_atomic_fact(&child_fact, &child)
        .expect("child proof should succeed");
    assert!(child.atomic_fact_proof(&child_fact.to_string()).is_some());
    assert!(parent.atomic_fact_proof(&child_fact.to_string()).is_none());
}

#[test]
fn child_guard_cleanup_never_clears_an_ancestor_guard() {
    let parent = VerifyState::initial();
    let child = parent.with_child_proof_scope();
    let object_key = "guarded-object".to_string();
    assert!(parent.begin_well_defined_object(&object_key));

    child.end_well_defined_object(&object_key);
    assert!(
        !parent.begin_well_defined_object(&object_key),
        "child cleanup must leave the active parent guard intact"
    );
    parent.end_well_defined_object(&object_key);
    assert!(parent.begin_well_defined_object(&object_key));
    parent.end_well_defined_object(&object_key);

    parent.set_set_builder_forall_transport_active(true);
    child.set_set_builder_forall_transport_active(false);
    assert!(child.set_builder_forall_transport_is_active());
    parent.set_set_builder_forall_transport_active(false);
    assert!(!child.set_builder_forall_transport_is_active());
}

#[test]
fn unknown_atomic_facts_are_not_memoized() {
    let mut runtime = new_test_runtime();
    let fact = parse_atomic_fact(&mut runtime, "1 = 2");
    let state = VerifyState::initial();

    let result = runtime
        .verify_atomic_fact(&fact, &state)
        .expect("unknown verification should not be a runtime error");

    assert!(result.is_unknown());
    assert!(state.atomic_fact_proof(&fact.to_string()).is_none());
}

fn new_test_runtime() -> Runtime {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("proof_search_state_test.lit");
    runtime
}

fn parse_atomic_fact(runtime: &mut Runtime, source: &str) -> AtomicFact {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, Rc::from("proof_search_state_test.lit"))
        .expect("test statement should tokenize");
    let stmt = runtime
        .parse_statement(&mut blocks[0])
        .expect("test statement should parse");
    let Stmt::Fact(Fact::AtomicFact(fact)) = stmt else {
        panic!("expected an atomic fact: {source}");
    };
    fact
}

fn direct_verification(result: &VerifyFactResult) -> Rc<SuccessFactProofNode> {
    let success = result.verified().expect("atomic fact should be factual");
    assert!(!matches!(success.proof(), SuccessFactProofResult::Reuse(_)));
    success.verification.clone()
}

fn reused_verification(result: &VerifyFactResult) -> &Rc<SuccessFactProofNode> {
    let success = result
        .verified()
        .expect("cached atomic fact should be factual");
    let SuccessFactProofResult::Reuse(result) = success.proof() else {
        panic!("atomic success should point to its search-local source");
    };
    &result.source
}
