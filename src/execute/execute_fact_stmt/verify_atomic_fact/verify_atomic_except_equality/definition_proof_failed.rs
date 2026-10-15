use crate::prelude::*;

/// A definition route may be unavailable, or fail at an actual obligation.
/// Ordinary search may ignore this miss; explicit `by def` reports it.
pub enum DefinitionProofFailed {
    Unavailable,
    Arity {
        expected: usize,
        actual: usize,
    },
    Instantiate(String),
    Requirement {
        index: usize,
        fact: Fact,
        result: Box<VerifyFactResult>,
    },
}
