#[cfg(test)]
mod verify_test;
mod syntactic_verifier;
mod verify_atomic_fact;
mod verify_well_defined;
mod verify_in_fact;
mod verify_state;

pub use syntactic_verifier::SyntacticVerifier;
pub use verify_state::VerifyState;