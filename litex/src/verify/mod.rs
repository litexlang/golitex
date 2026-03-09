#[cfg(test)]
mod verify_test;
mod syntactic_verifier;
mod verify_atomic_fact;
mod verify_well_defined;
mod verify_fact;
mod verify_in_fact;

pub use syntactic_verifier::SyntacticVerifier;
