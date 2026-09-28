use super::*;
use crate::prelude::{default_line_file, EqualFact, Number, Obj};

fn equality(left: &str, right: &str) -> AtomicFact {
    let left: Obj = Number::new(left.to_string()).into();
    let right: Obj = Number::new(right.to_string()).into();
    EqualFact::new(left, right, default_line_file()).into()
}

#[test]
fn active_fact_is_blocked_only_until_its_inference_frame_finishes() {
    let state = InferenceState::new();
    let fact = equality("1", "1");

    let frame = state
        .enter_atomic_fact(&fact)
        .expect("first inference frame should enter");
    assert!(state.enter_atomic_fact(&fact).is_none());

    drop(frame);
    assert!(state.enter_atomic_fact(&fact).is_some());
}

#[test]
fn distinct_atomic_facts_may_expand_in_the_same_inference_tree() {
    let state = InferenceState::new();
    let first = equality("1", "1");
    let second = equality("2", "2");

    let _first_frame = state
        .enter_atomic_fact(&first)
        .expect("first fact should enter");
    assert!(state.enter_atomic_fact(&second).is_some());
}
