#[cfg(test)]
mod verify_test;
mod verify_by_syntax;
mod verify_atomic_fact;
mod verify_fact_well_defined;
mod verify_in_fact_builtin_rules;
mod verify_state;
mod verify_obj_well_defined;
mod verify_non_equational_atomic_fact;
mod verify_fact;

pub use verify_state::VerifyState;