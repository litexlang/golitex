//! Target requirement phases, uses, and proofs.

use crate::prelude::*;

/// Exact proof argument consumed by one checked function-application layer.
#[derive(Clone)]
pub struct WellDefinedTargetRequirementProof {
    pub source_object: Obj,
    pub role: WellDefinednessRequirementRole,
    pub fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

/// One source application occurrence that consumes requirements from an
/// environment-owned object proof. Repeated source expressions keep distinct
/// occurrence IDs even when the WD cache lets them cite the same proof node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinednessTargetRequirementPhase {
    Preflight,
    Proof,
    Store,
}

#[derive(Clone, Debug)]
pub struct WellDefinedTargetRequirementUse {
    pub source_occurrence_id: SourceObjectOccurrenceId,
    pub well_defined_obj_id: WellDefinedObjId,
    pub phase: WellDefinednessTargetRequirementPhase,
    pub role: WellDefinednessRequirementRole,
    pub fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

impl WellDefinedTargetRequirementUse {
    pub fn new(
        source_occurrence_id: SourceObjectOccurrenceId,
        well_defined_obj_id: WellDefinedObjId,
        phase: WellDefinednessTargetRequirementPhase,
        role: WellDefinednessRequirementRole,
        fact_id: WellDefinedFactId,
        expected_proposition: Fact,
    ) -> Self {
        Self {
            source_occurrence_id,
            well_defined_obj_id,
            phase,
            role,
            fact_id,
            expected_proposition,
        }
    }
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
