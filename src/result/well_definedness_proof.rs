use crate::prelude::*;
use std::rc::Rc;

/// Runtime-wide identity of one successful object well-definedness proof.
///
/// Visibility still follows the owning Litex environment. Runtime-wide
/// allocation only prevents committed child environments from colliding with
/// their parents and prevents rolled-back identities from being reused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedObjProofId(u64);

impl WellDefinedObjProofId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

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

/// The callable contract selected while checking a function application.
/// Stored membership facts are the canonical contract identity. A structural
/// fallback is retained for kernel-owned callables that have no ordinary
/// membership fact, such as an anonymous function literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinedFunctionContract {
    StoredMembershipFact(FactId),
    Structural(ObjString),
}

/// Cache identity of an object under the exact context-sensitive function
/// contracts selected by the verifier.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedCacheKey {
    pub object_key: ObjString,
    pub function_contracts: Vec<WellDefinedFunctionContract>,
}

impl WellDefinedCacheKey {
    pub fn new(
        object_key: ObjString,
        function_contracts: Vec<WellDefinedFunctionContract>,
    ) -> Self {
        Self {
            object_key,
            function_contracts,
        }
    }

    pub fn without_function_contract(object_key: ObjString) -> Self {
        Self::new(object_key, Vec::new())
    }
}

/// Ordinary verification may cache truth without constructing compiler
/// evidence. To-Lean may reuse an entry only when `proof_id` is present.
#[derive(Clone, Debug)]
pub struct CachedWellDefinedObj {
    pub proof_id: Option<WellDefinedObjProofId>,
}

impl CachedWellDefinedObj {
    pub fn ordinary() -> Self {
        Self { proof_id: None }
    }

    pub fn with_proof(proof_id: WellDefinedObjProofId) -> Self {
        Self {
            proof_id: Some(proof_id),
        }
    }
}

/// One concrete proposition and the exact successful verifier proof retained
/// by the environment for To-Lean replay.
#[derive(Clone, Debug)]
pub struct WellDefinedFactProof {
    pub id: WellDefinedFactId,
    pub proposition: Fact,
    pub proof: Rc<FactualStmtSuccess>,
}

impl WellDefinedFactProof {
    pub fn new(id: WellDefinedFactId, proposition: Fact, proof: Rc<FactualStmtSuccess>) -> Self {
        Self {
            id,
            proposition,
            proof,
        }
    }
}

/// Exact proof argument consumed by one checked function-application layer.
#[derive(Clone)]
pub struct WellDefinedTargetRequirementProof {
    pub source_object: Obj,
    pub role: WellDefinednessRequirementRole,
    pub fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

impl std::fmt::Debug for WellDefinedTargetRequirementProof {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinedTargetRequirementProof")
            .field("source_object", &self.source_object.to_string())
            .field("role", &self.role)
            .field("fact_id", &self.fact_id)
            .field(
                "expected_proposition",
                &self.expected_proposition.to_string(),
            )
            .finish()
    }
}

impl WellDefinedTargetRequirementProof {
    pub fn new(
        source_object: Obj,
        role: WellDefinednessRequirementRole,
        fact_id: WellDefinedFactId,
        expected_proposition: Fact,
    ) -> Self {
        Self {
            source_object,
            role,
            fact_id,
            expected_proposition,
        }
    }
}

/// A node in the environment-owned DAG explaining why one object is
/// well-defined. Only direct child and direct fact edges are stored; the full
/// derivation is the transitive closure from `id`.
#[derive(Clone)]
pub struct WellDefinedObjProof {
    pub id: WellDefinedObjProofId,
    pub object: Obj,
    pub cache_key: WellDefinedCacheKey,
    pub child_proof_ids: Vec<WellDefinedObjProofId>,
    pub fact_ids: Vec<WellDefinedFactId>,
    pub target_requirements: Vec<WellDefinedTargetRequirementProof>,
    pub intrinsic_result_set: Option<Obj>,
}

impl std::fmt::Debug for WellDefinedObjProof {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinedObjProof")
            .field("id", &self.id)
            .field("object", &self.object.to_string())
            .field("cache_key", &self.cache_key)
            .field("child_proof_ids", &self.child_proof_ids)
            .field("fact_ids", &self.fact_ids)
            .field("target_requirements", &self.target_requirements)
            .field(
                "intrinsic_result_set",
                &self.intrinsic_result_set.as_ref().map(ToString::to_string),
            )
            .finish()
    }
}

impl WellDefinedObjProof {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        id: WellDefinedObjProofId,
        object: Obj,
        cache_key: WellDefinedCacheKey,
        child_proof_ids: Vec<WellDefinedObjProofId>,
        fact_ids: Vec<WellDefinedFactId>,
        target_requirements: Vec<WellDefinedTargetRequirementProof>,
        intrinsic_result_set: Option<Obj>,
    ) -> Self {
        Self {
            id,
            object,
            cache_key,
            child_proof_ids,
            fact_ids,
            target_requirements,
            intrinsic_result_set,
        }
    }
}
