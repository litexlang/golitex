//! Binder scope identities, premise roles, and proofs.

use crate::prelude::*;

/// Runtime-wide identity of one lexical binder scope opened while checking a
/// binder-owning object. It is compiler evidence only; Litex environments
/// still own the assumptions and discard them normally when the scope exits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedBinderScopeId(u64);

impl WellDefinedBinderScopeId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinedBinderPremiseRole {
    ParameterMembership {
        parameter_group_index: usize,
        parameter_index: usize,
    },
    Domain {
        domain_index: usize,
    },
    /// One source-ordered predicate in a set builder.  Unlike function-domain
    /// premises, later predicates may rely on this fact while their own
    /// well-definedness is checked.
    LocalCondition {
        condition_index: usize,
    },
}

/// One ordinary environment FactId that becomes a Lean premise when replaying
/// a verifier proof inside a binder-owned object.
#[derive(Clone, Debug)]
pub struct WellDefinedBinderPremiseProof {
    pub role: WellDefinedBinderPremiseRole,
    pub symbol_id: Option<SymbolId>,
    pub fact_id: FactId,
    pub proposition: Fact,
}

impl WellDefinedBinderPremiseProof {
    pub fn new(
        role: WellDefinedBinderPremiseRole,
        symbol_id: Option<SymbolId>,
        fact_id: FactId,
        proposition: Fact,
    ) -> Self {
        Self {
            role,
            symbol_id,
            fact_id,
            proposition,
        }
    }
}

/// Frozen definition of one temporary Litex binder environment. The direct
/// premises are assumptions; `assumption_infers` records consequences that
/// must be re-derived rather than silently promoted to extra Lean axioms.
#[derive(Clone)]
pub struct WellDefinedBinderScopeProof {
    pub id: WellDefinedBinderScopeId,
    pub owner_object: Obj,
    pub ambient_scope_ids: Vec<WellDefinedBinderScopeId>,
    pub premises: Vec<WellDefinedBinderPremiseProof>,
    pub assumption_infers: SuccessInferResult,
}

impl std::fmt::Debug for WellDefinedBinderScopeProof {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinedBinderScopeProof")
            .field("id", &self.id)
            .field("owner_object", &self.owner_object.to_string())
            .field("ambient_scope_ids", &self.ambient_scope_ids)
            .field("premises", &self.premises)
            .field("assumption_infers", &self.assumption_infers)
            .finish()
    }
}
