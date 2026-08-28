//! Top-level object well-definedness proof payload.

use crate::prelude::*;

/// A node in the environment-owned DAG explaining why one object is
/// well-defined. Only direct child and direct fact edges are stored; the full
/// derivation is the transitive closure from `id`.
#[derive(Clone)]
pub struct WellDefinedObjProof {
    pub id: WellDefinedObjId,
    pub object: Obj,
    pub cache_key: WellDefinedCacheKey,
    pub child_uses: Vec<WellDefinedObjChildUse>,
    pub fact_ids: Vec<WellDefinedFactId>,
    pub target_requirements: Vec<WellDefinedTargetRequirementProof>,
    pub intrinsic_result_set: Option<Obj>,
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
    pub owned_binder_scope: Option<WellDefinedBinderScopeProof>,
}

impl std::fmt::Debug for WellDefinedObjProof {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinedObjProof")
            .field("id", &self.id)
            .field("object", &self.object.to_string())
            .field("cache_key", &self.cache_key)
            .field("child_uses", &self.child_uses)
            .field("fact_ids", &self.fact_ids)
            .field("target_requirements", &self.target_requirements)
            .field(
                "intrinsic_result_set",
                &self.intrinsic_result_set.as_ref().map(ToString::to_string),
            )
            .field("ambient_binder_scope_ids", &self.ambient_binder_scope_ids)
            .field("owned_binder_scope", &self.owned_binder_scope)
            .finish()
    }
}

impl WellDefinedObjProof {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        id: WellDefinedObjId,
        object: Obj,
        cache_key: WellDefinedCacheKey,
        child_uses: Vec<WellDefinedObjChildUse>,
        fact_ids: Vec<WellDefinedFactId>,
        target_requirements: Vec<WellDefinedTargetRequirementProof>,
        intrinsic_result_set: Option<Obj>,
        ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
        owned_binder_scope: Option<WellDefinedBinderScopeProof>,
    ) -> Self {
        Self {
            id,
            object,
            cache_key,
            child_uses,
            fact_ids,
            target_requirements,
            intrinsic_result_set,
            ambient_binder_scope_ids,
            owned_binder_scope,
        }
    }
}
