//! Fact well-definedness proof identities and payloads.

use crate::prelude::*;
use std::rc::Rc;

/// Runtime-wide identity of one concrete proposition proved while checking
/// object well-definedness. These facts are compiler evidence only: assigning
/// this ID never inserts the proposition into Litex's ordinary known-fact
/// environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedFactId(u64);

impl WellDefinedFactId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

/// One concrete proposition and the exact successful verifier proof retained
/// by the environment for To-Lean replay.
#[derive(Clone, Debug)]
pub struct WellDefinedFactProof {
    pub id: WellDefinedFactId,
    pub proposition: Fact,
    pub proof: Rc<SuccessVerifyFactResult>,
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
}

impl WellDefinedFactProof {
    pub fn new(
        id: WellDefinedFactId,
        proposition: Fact,
        proof: Rc<SuccessVerifyFactResult>,
        ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
    ) -> Self {
        Self {
            id,
            proposition,
            proof,
            ambient_binder_scope_ids,
        }
    }
}
