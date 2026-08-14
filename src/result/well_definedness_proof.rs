use crate::prelude::*;
use std::rc::Rc;

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
    pub assumption_infers: InferResult,
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

/// Runtime-wide identity of one fixed object whose well-definedness was verified.
///
/// Visibility still follows the owning Litex environment. Runtime-wide
/// allocation only prevents committed child environments from colliding with
/// their parents and prevents rolled-back identities from being reused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinedObjId(u64);

impl WellDefinedObjId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

/// Exact construction position at which a parent object consumes one direct
/// child object. Roles are ordered and may repeat the same object identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellDefinedObjChildRole {
    /// The already-checked callable prefix consumed by the next source
    /// application layer.  For `g(1)(2)`, the outer object points to the
    /// independently named prefix object `g(1)` through this edge.
    FunctionPrefix {
        through_layer_index: usize,
    },
    /// A structured callable expression consumed by the first application
    /// layer, for example an anonymous function, sequence literal, matrix
    /// operator, field projection, or instantiated template.
    FunctionHead,
    FunctionArgument {
        layer_index: usize,
        argument_index: usize,
    },
    BuiltinArgument {
        argument_index: usize,
    },
    ConstructorArgument {
        argument_index: usize,
    },
    BinderParameterCarrier {
        parameter_group_index: usize,
    },
    BinderReturnCarrier,
    BinderBody,
    /// A nested object check performed while proving the parent well-defined,
    /// but not consumed as a value slot by the parent's target constructor.
    /// These ordered audit edges preserve Litex's verification trace. A Lean
    /// emitter must never use them to fill a constructor argument.
    VerificationDependency {
        dependency_index: usize,
    },
}

#[derive(Clone)]
pub struct WellDefinedObjChildUse {
    pub role: WellDefinedObjChildRole,
    pub obj_id: WellDefinedObjId,
    /// Exact object checked at this edge. This independently freezes audit
    /// dependencies, whose target cannot be reconstructed from a constructor
    /// value slot.
    pub source_object: Obj,
}

impl WellDefinedObjChildUse {
    pub fn new(
        role: WellDefinedObjChildRole,
        obj_id: WellDefinedObjId,
        source_object: Obj,
    ) -> Self {
        Self {
            role,
            obj_id,
            source_object,
        }
    }
}

impl std::fmt::Debug for WellDefinedObjChildUse {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("WellDefinedObjChildUse")
            .field("role", &self.role)
            .field("obj_id", &self.obj_id)
            .field("source_object", &self.source_object.to_string())
            .finish()
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
/// evidence. To-Lean may reuse an entry only when `obj_id` is present.
#[derive(Clone, Debug)]
pub struct CachedWellDefinedObj {
    pub obj_id: Option<WellDefinedObjId>,
}

impl CachedWellDefinedObj {
    pub fn ordinary() -> Self {
        Self { obj_id: None }
    }

    pub fn with_obj(obj_id: WellDefinedObjId) -> Self {
        Self {
            obj_id: Some(obj_id),
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
    pub ambient_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
}

impl WellDefinedFactProof {
    pub fn new(
        id: WellDefinedFactId,
        proposition: Fact,
        proof: Rc<FactualStmtSuccess>,
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
