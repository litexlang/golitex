//! Tests for general proof-search state transitions.

use crate::verify::VerifyState;

#[test]
fn verify_state_constructors_select_the_expected_semantics() {
    let initial = VerifyState::initial();
    assert_eq!(initial.proof_search_round, 0);
    assert!(!initial.well_definedness_verified);
    assert!(initial.is_initial_round());

    let after_well_definedness = VerifyState::after_well_definedness();
    assert_eq!(after_well_definedness.proof_search_round, 0);
    assert!(after_well_definedness.well_definedness_verified);

    let final_round = VerifyState::final_round();
    assert_eq!(final_round.proof_search_round, 2);
    assert!(!final_round.well_definedness_verified);
    assert!(!final_round.is_initial_round());

    let final_after_well_definedness = VerifyState::final_round_after_well_definedness();
    assert_eq!(final_after_well_definedness.proof_search_round, 2);
    assert!(final_after_well_definedness.well_definedness_verified);
}

#[test]
fn verify_state_transitions_change_only_the_named_dimension() {
    let restricted = VerifyState::initial().without_known_forall_for_equality();
    let next_round = restricted.with_next_round();
    assert_eq!(next_round.proof_search_round, 1);
    assert!(!next_round.well_definedness_verified);
    assert!(!next_round.equality_may_use_known_forall);

    let after_well_definedness = next_round.with_well_definedness_verified();
    assert_eq!(after_well_definedness.proof_search_round, 1);
    assert!(after_well_definedness.well_definedness_verified);
    assert!(!after_well_definedness.equality_may_use_known_forall);
}
