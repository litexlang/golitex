use crate::prelude::*;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinednessRequirementRole {
    /// One ordered operand-membership proof consumed by a proof-carrying
    /// builtin object constructor such as complex addition.
    BuiltinArgumentMembership { argument_index: usize },
    /// One ordered nonzero proof consumed by a partial builtin object
    /// constructor such as complex division.
    BuiltinArgumentNonzero { argument_index: usize },
    /// One ordered pairwise-distinctness proof consumed by a constructor
    /// whose source invariant compares entries at exact list positions.
    ConstructorPairwiseDistinct {
        left_index: usize,
        right_index: usize,
    },
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
    /// Direct proof that an anonymous-function body belongs to its declared
    /// return carrier under the function's binder assumptions.
    AnonymousFunctionBodyMembership,
    /// Alternative return proof used when the body is one exact bound
    /// parameter and its parameter carrier is a subset of the return carrier.
    AnonymousFunctionBoundParameterSubset {
        parameter_group_index: usize,
        parameter_index: usize,
    },
}

/// One top-level object proof use in an exact statement execution phase.
/// Keeping the phase prevents the backend from guessing between structurally
/// equal cache nodes produced by preflight, proof, and store passes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinednessRootObjectProofUse {
    pub well_defined_obj_id: WellDefinedObjId,
    pub phase: WellDefinednessTargetRequirementPhase,
}

impl WellDefinednessRootObjectProofUse {
    pub fn new(
        well_defined_obj_id: WellDefinedObjId,
        phase: WellDefinednessTargetRequirementPhase,
    ) -> Self {
        Self {
            well_defined_obj_id,
            phase,
        }
    }
}

/// Exact verifier-owned join from one parser occurrence to the fixed WD
/// object it consumed. Live capture may observe the same occurrence in
/// several execution phases; freezing selects one canonical phase before this
/// edge reaches To-Lean.
#[derive(Clone)]
pub struct WellDefinednessSourceObjectUse {
    pub source_occurrence_id: SourceObjectOccurrenceId,
    pub source_object: Obj,
    pub well_defined_obj_id: WellDefinedObjId,
    pub phase: WellDefinednessTargetRequirementPhase,
}

impl std::fmt::Debug for WellDefinednessSourceObjectUse {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinednessSourceObjectUse")
            .field("source_occurrence_id", &self.source_occurrence_id)
            .field("source_object", &self.source_object.to_string())
            .field("well_defined_obj_id", &self.well_defined_obj_id)
            .field("phase", &self.phase)
            .finish()
    }
}

impl WellDefinednessSourceObjectUse {
    pub fn new(
        source_occurrence_id: SourceObjectOccurrenceId,
        source_object: Obj,
        well_defined_obj_id: WellDefinedObjId,
        phase: WellDefinednessTargetRequirementPhase,
    ) -> Self {
        Self {
            source_occurrence_id,
            source_object,
            well_defined_obj_id,
            phase,
        }
    }
}

/// One exact successful factual proof retained while an object
/// well-definedness scope is still alive.
#[derive(Clone, Debug)]
pub struct WellDefinednessFactEvidence {
    /// Runtime-wide identity of the environment-owned proof fact.
    pub well_defined_fact_id: WellDefinedFactId,
    pub proof: Rc<FactualStmtSuccess>,
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
}

#[derive(Clone, Debug)]
pub struct WellDefinednessBinderScopeEvidence {
    pub scope: WellDefinedBinderScopeProof,
}

/// Frozen statement projection of one environment-owned object-proof node.
/// `well_defined_fact_ids` are its direct proof edges. Transitive evidence is
/// recovered by following `child_uses`; it is never duplicated here.
#[derive(Clone)]
pub struct WellDefinednessObjectEvidence {
    /// Runtime-wide identity of the environment-owned DAG node.
    pub well_defined_obj_id: WellDefinedObjId,
    pub object: Obj,
    pub function_contracts: Vec<WellDefinedFunctionContract>,
    pub intrinsic_result_set: Option<Obj>,
    pub child_uses: Vec<WellDefinedObjChildUse>,
    pub well_defined_fact_ids: Vec<WellDefinedFactId>,
    pub target_requirements: Vec<WellDefinedTargetRequirementProof>,
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
    pub owned_binder_scope_id: Option<WellDefinedBinderScopeId>,
}

impl std::fmt::Debug for WellDefinednessObjectEvidence {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinednessObjectEvidence")
            .field("well_defined_obj_id", &self.well_defined_obj_id)
            .field("object", &self.object.to_string())
            .field("function_contracts", &self.function_contracts)
            .field(
                "intrinsic_result_set",
                &self.intrinsic_result_set.as_ref().map(ToString::to_string),
            )
            .field("child_uses", &self.child_uses)
            .field("well_defined_fact_ids", &self.well_defined_fact_ids)
            .field("target_requirements", &self.target_requirements)
            .field("ambient_binder_scope_ids", &self.ambient_binder_scope_ids)
            .field("owned_binder_scope_id", &self.owned_binder_scope_id)
            .finish()
    }
}

impl WellDefinednessObjectEvidence {
    pub fn new(
        well_defined_obj_id: WellDefinedObjId,
        object: Obj,
        function_contracts: Vec<WellDefinedFunctionContract>,
        intrinsic_result_set: Option<Obj>,
        child_uses: Vec<WellDefinedObjChildUse>,
        well_defined_fact_ids: Vec<WellDefinedFactId>,
        target_requirements: Vec<WellDefinedTargetRequirementProof>,
        ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
        owned_binder_scope_id: Option<WellDefinedBinderScopeId>,
    ) -> Self {
        Self {
            well_defined_obj_id,
            object,
            function_contracts,
            intrinsic_result_set,
            child_uses,
            well_defined_fact_ids,
            target_requirements,
            ambient_binder_scope_ids,
            owned_binder_scope_id,
        }
    }
}

/// Exact link from a target proof argument to the verifier proof that
/// discharged it. Source-only obligations remain in `objects` and `facts` but
/// deliberately have no target-use entry.
#[derive(Clone)]
pub struct WellDefinednessTargetRequirementEvidence {
    pub source_occurrence_id: SourceObjectOccurrenceId,
    pub well_defined_obj_id: WellDefinedObjId,
    pub phase: WellDefinednessTargetRequirementPhase,
    pub role: WellDefinednessRequirementRole,
    pub well_defined_fact_id: WellDefinedFactId,
    pub expected_proposition: Fact,
}

/// Exact ordinary FactId assigned to a parameter premise while checking a
/// nested source quantifier. The child environment may later disappear, but
/// the compiler still has to map citations of this ID to the corresponding
/// Lean binder.
#[derive(Clone, Debug)]
pub struct WellDefinednessParameterFactEvidence {
    pub symbol_id: SymbolId,
    pub fact_id: FactId,
    pub proposition: Fact,
}

impl WellDefinednessParameterFactEvidence {
    pub fn new(symbol_id: SymbolId, fact_id: FactId, proposition: Fact) -> Self {
        Self {
            symbol_id,
            fact_id,
            proposition,
        }
    }
}

impl std::fmt::Debug for WellDefinednessTargetRequirementEvidence {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinednessTargetRequirementEvidence")
            .field("source_occurrence_id", &self.source_occurrence_id)
            .field("well_defined_obj_id", &self.well_defined_obj_id)
            .field("phase", &self.phase)
            .field("role", &self.role)
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
        source_occurrence_id: SourceObjectOccurrenceId,
        well_defined_obj_id: WellDefinedObjId,
        phase: WellDefinednessTargetRequirementPhase,
        role: WellDefinednessRequirementRole,
        well_defined_fact_id: WellDefinedFactId,
        expected_proposition: Fact,
    ) -> Self {
        Self {
            source_occurrence_id,
            well_defined_obj_id,
            phase,
            role,
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
    pub root_obj_ids: Vec<WellDefinedObjId>,
    pub root_proof_uses: Vec<WellDefinednessRootObjectProofUse>,
    /// Exact source-occurrence uses. During live capture this can contain one
    /// entry per execution phase; `freeze_well_definedness_certificate`
    /// reduces it to one canonical edge per occurrence.
    pub source_object_uses: Vec<WellDefinednessSourceObjectUse>,
    /// Live-capture links from exact source applications to reusable proof
    /// nodes. `freeze_well_definedness_certificate` validates and projects
    /// these into `target_requirements`.
    pub(crate) target_requirement_uses: Vec<WellDefinedTargetRequirementUse>,
    pub facts: Vec<WellDefinednessFactEvidence>,
    pub objects: Vec<WellDefinednessObjectEvidence>,
    pub binder_scopes: Vec<WellDefinednessBinderScopeEvidence>,
    pub target_requirements: Vec<WellDefinednessTargetRequirementEvidence>,
    pub parameter_facts: Vec<WellDefinednessParameterFactEvidence>,
}

impl WellDefinednessCertificate {
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
            && self.objects.is_empty()
            && self.root_proof_uses.is_empty()
            && self.source_object_uses.is_empty()
            && self.target_requirement_uses.is_empty()
            && self.target_requirements.is_empty()
            && self.parameter_facts.is_empty()
            && self.binder_scopes.is_empty()
    }
}
