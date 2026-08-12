use crate::prelude::*;
use std::rc::Rc;

/// Stable only within one executed source statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinednessCertificateId(u64);

impl WellDefinednessCertificateId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

/// Stable only within one executed source statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinednessObjectOccurrenceId(u64);

impl WellDefinednessObjectOccurrenceId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinednessRequirementRole {
    /// The verifier consumed this proof while checking an object. Whether a
    /// target term also consumes it is decided only by a typed application
    /// certificate, never by dropping this audit entry.
    SourceObjectRequirement,
    /// A checked membership is passed after the ordinary value arguments of
    /// one exact Litex application layer.
    FunctionArgumentMembership {
        layer_index: usize,
        parameter_index: usize,
    },
    /// A checked source-domain fact is passed after all membership arguments
    /// of one exact Litex application layer.
    FunctionDomain {
        layer_index: usize,
        domain_index: usize,
    },
}

/// One exact successful factual proof retained while an object
/// well-definedness scope is still alive.
#[derive(Clone, Debug)]
pub struct WellDefinednessFactEvidence {
    pub certificate_id: WellDefinednessCertificateId,
    /// Runtime-wide identity of the environment-owned proof fact.
    pub well_defined_fact_id: WellDefinedFactId,
    pub role: WellDefinednessRequirementRole,
    pub proof: Rc<FactualStmtSuccess>,
}

/// Frozen statement projection of one environment-owned object-proof node.
/// `well_defined_fact_ids` are its direct edges; `fact_ids` also includes the
/// transitive compatibility view used by the current Lean ownership checks.
#[derive(Clone)]
pub struct WellDefinednessObjectEvidence {
    pub occurrence_id: WellDefinednessObjectOccurrenceId,
    /// Runtime-wide identity of the environment-owned DAG node.
    pub well_defined_obj_proof_id: WellDefinedObjProofId,
    pub object: Obj,
    pub intrinsic_result_set: Option<Obj>,
    pub child_proof_ids: Vec<WellDefinedObjProofId>,
    pub well_defined_fact_ids: Vec<WellDefinedFactId>,
    /// Statement-local projection retained for compatibility with the Lean
    /// certificate validator. The authoritative edges are the stable IDs
    /// above.
    pub fact_ids: Vec<WellDefinednessCertificateId>,
}

impl std::fmt::Debug for WellDefinednessObjectEvidence {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinednessObjectEvidence")
            .field("occurrence_id", &self.occurrence_id)
            .field("well_defined_obj_proof_id", &self.well_defined_obj_proof_id)
            .field("object", &self.object.to_string())
            .field(
                "intrinsic_result_set",
                &self.intrinsic_result_set.as_ref().map(ToString::to_string),
            )
            .field("child_proof_ids", &self.child_proof_ids)
            .field("well_defined_fact_ids", &self.well_defined_fact_ids)
            .field("fact_ids", &self.fact_ids)
            .finish()
    }
}

impl WellDefinednessObjectEvidence {
    pub fn new(
        occurrence_id: WellDefinednessObjectOccurrenceId,
        well_defined_obj_proof_id: WellDefinedObjProofId,
        object: Obj,
        intrinsic_result_set: Option<Obj>,
        child_proof_ids: Vec<WellDefinedObjProofId>,
        well_defined_fact_ids: Vec<WellDefinedFactId>,
        fact_ids: Vec<WellDefinednessCertificateId>,
    ) -> Self {
        Self {
            occurrence_id,
            well_defined_obj_proof_id,
            object,
            intrinsic_result_set,
            child_proof_ids,
            well_defined_fact_ids,
            fact_ids,
        }
    }
}

/// Exact link from a target proof argument to the verifier proof that
/// discharged it. Source-only obligations remain in `objects` and `facts` but
/// deliberately have no target-use entry.
#[derive(Clone)]
pub struct WellDefinednessTargetRequirementEvidence {
    pub object_occurrence_id: WellDefinednessObjectOccurrenceId,
    pub well_defined_obj_proof_id: WellDefinedObjProofId,
    pub source_object: Obj,
    pub role: WellDefinednessRequirementRole,
    pub certificate_id: WellDefinednessCertificateId,
    pub well_defined_fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

impl std::fmt::Debug for WellDefinednessTargetRequirementEvidence {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinednessTargetRequirementEvidence")
            .field("object_occurrence_id", &self.object_occurrence_id)
            .field("well_defined_obj_proof_id", &self.well_defined_obj_proof_id)
            .field("source_object", &self.source_object.to_string())
            .field("role", &self.role)
            .field("certificate_id", &self.certificate_id)
            .field("well_defined_fact_id", &self.well_defined_fact_id)
            .field(
                "expected_proposition",
                &self.expected_proposition.to_string(),
            )
            .finish()
    }
}

impl WellDefinednessTargetRequirementEvidence {
    pub fn new(
        object_occurrence_id: WellDefinednessObjectOccurrenceId,
        well_defined_obj_proof_id: WellDefinedObjProofId,
        source_object: Obj,
        role: WellDefinednessRequirementRole,
        certificate_id: WellDefinednessCertificateId,
        well_defined_fact_id: WellDefinedFactId,
        expected_proposition: Fact,
    ) -> Self {
        Self {
            object_occurrence_id,
            well_defined_obj_proof_id,
            source_object,
            role,
            certificate_id,
            well_defined_fact_id,
            expected_proposition,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct WellDefinednessCertificate {
    /// Roots used by this statement. All proof/fact bodies remain owned by
    /// their Litex environments; the remaining fields are a frozen projection
    /// used after a local environment has left runtime scope.
    pub root_proof_ids: Vec<WellDefinedObjProofId>,
    pub facts: Vec<WellDefinednessFactEvidence>,
    pub objects: Vec<WellDefinednessObjectEvidence>,
    pub target_requirements: Vec<WellDefinednessTargetRequirementEvidence>,
}

impl WellDefinednessCertificate {
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty() && self.objects.is_empty() && self.target_requirements.is_empty()
    }
}
