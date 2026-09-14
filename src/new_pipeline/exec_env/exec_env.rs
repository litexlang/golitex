use crate::new_pipeline::ast::obj::Identifier;
use crate::new_pipeline::ast::stmt::DefPropStmt as NewDefPropStmt;
use crate::new_pipeline::runtime::runtime_ids::{FactId, IdentifierId, WellDefinednessId};
use crate::prelude::*;
use std::collections::HashMap;

pub use super::known_fact_memory::{
    AtomicExceptEqualityFactMemory, KnownEqualityMemory, KnownFactMemory,
};

// -----------------------------------------------------------------------------
// Core data model
// -----------------------------------------------------------------------------

/// State owned by one execution scope.
///
/// A child scope may read this environment and all of its parents.  It writes
/// only to its own instance.  When a statement returns, the result may retain
/// the child environment so its local definitions, facts, and WD records stay
/// available to the renderer without being merged into the parent implicitly.
#[derive(Clone)]
pub struct ExecEnv {
    /// Definitions visible to statements executed in this scope.
    pub definitions: DefinitionMemory,

    /// Facts and fact indexes stored in this scope.
    pub facts: KnownFactMemory,

    /// Shape/value properties attached to special objects by stored facts.
    pub special_object_properties: HashMap<ObjString, Vec<SpecialObjProperty>>,

    /// Algebraic properties proved for predicates in this scope.
    pub prop_algebraic_properties: HashMap<PropName, Vec<PropAlgebraicProperty>>,

    /// Well-definedness records owned by this scope.
    ///
    /// WD lookup walks this scope and then its parent scopes.  A successful
    /// WD proof is recorded here only when the current verification state
    /// explicitly allows storage; temporary builtin-rule searches therefore
    /// remain read-only.
    pub well_defined_objects: WellDefinedObjectMemory,
}

/// The two-way index for well-defined objects owned by one scope.
#[derive(Clone, Default)]
pub struct WellDefinedObjectMemory {
    /// Canonical object key to the proof identity that established WD.
    pub object_to_wd_id: HashMap<ObjString, WellDefinednessId>,

    /// Proof identity back to the object carried by a result or citation.
    pub wd_id_to_object: HashMap<WellDefinednessId, Obj>,
}

/// Definitions introduced in one execution environment.
#[derive(Clone)]
pub struct DefinitionMemory {
    /// Named atoms defined in this scope (`let`, `have`, forall/exist locals, …).
    /// Keyed by IdentifierId; value carries the full Identifier (name + IdentifierId).
    pub identifiers: HashMap<IdentifierId, IdentifierDefinitionMemory>,

    pub predicate_definitions: HashMap<PropName, NewDefPropStmt>,
    pub abstract_predicate_definitions: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub algorithm_definitions: HashMap<AlgoName, DefAlgoStmt>,
    pub structure_definitions: HashMap<StructName, DefStructStmt>,
    pub template_definitions: HashMap<TemplateName, DefTemplateStmt>,
    pub setting_definitions: HashMap<String, DefSettingStmt>,
    pub theorem_definitions: HashMap<ThmName, DefThmStmt>,
    pub axiom_definitions: HashMap<ThmName, AxiomStmt>,
    pub strategy_definitions: HashMap<StrategyName, DefStrategyStmt>,
}

/// One defined atom in `DefinitionMemory.identifiers`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentifierDefinitionMemory {
    pub identifier: Identifier,
}

/// Algebraic properties that can be proved for a predicate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropAlgebraicProperty {
    Transitive,
    SymmetricArgumentPermutate(Vec<Vec<usize>>),
    Reflexive,
    Antisymmetric,
}

/// Properties recorded for objects whose structure has a reusable fact-based
/// interpretation.
#[derive(Clone)]
pub enum SpecialObjProperty {
    TupleEquality((Tuple, FactId)),
    TupleOwner((Cart, FactId)),
    CartEquality((Cart, FactId)),
    FiniteSeqEquality((FiniteSeqListObj, FactId)),
    FiniteSeqOwner((FiniteSeqSet, FactId)),
    SetBuilderEquality((SetBuilder, FactId)),
    SimplifiedValue(KnownObjValue),
    InFunctionSet((FnSetBody, FactId)),
    EqualToFunction((Obj, FactId)),
}

// -----------------------------------------------------------------------------
// Construction and cache operations
// -----------------------------------------------------------------------------

impl ExecEnv {
    pub fn new() -> Self {
        Self {
            definitions: DefinitionMemory::new(),
            facts: KnownFactMemory::new(),
            special_object_properties: HashMap::new(),
            prop_algebraic_properties: HashMap::new(),
            well_defined_objects: WellDefinedObjectMemory::new(),
        }
    }

    pub fn lookup_def_prop(&self, name: &str) -> Option<&NewDefPropStmt> {
        self.definitions.predicate_definitions.get(name)
    }

    pub fn store_def_prop(&mut self, def_prop: NewDefPropStmt) {
        self.definitions
            .predicate_definitions
            .insert(def_prop.name.clone(), def_prop);
    }
}

impl Default for ExecEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl WellDefinedObjectMemory {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the WD proof identity for an object, if this scope owns one.
    pub fn lookup(&self, object: &Obj) -> Option<WellDefinednessId> {
        self.object_to_wd_id.get(&obj_equality_key(object)).copied()
    }

    /// Record a WD proof and its object payload in both directions.
    /// Re-recording the same object or proof id is idempotent.
    pub fn record(&mut self, object: Obj, wd_id: WellDefinednessId) {
        let object_key = obj_equality_key(&object);

        self.object_to_wd_id.insert(object_key, wd_id);
        self.wd_id_to_object.insert(wd_id, object);
    }
}

impl DefinitionMemory {
    pub fn new() -> Self {
        Self {
            identifiers: HashMap::new(),
            predicate_definitions: HashMap::new(),
            abstract_predicate_definitions: HashMap::new(),
            algorithm_definitions: HashMap::new(),
            structure_definitions: HashMap::new(),
            template_definitions: HashMap::new(),
            setting_definitions: HashMap::new(),
            theorem_definitions: HashMap::new(),
            axiom_definitions: HashMap::new(),
            strategy_definitions: HashMap::new(),
        }
    }
}

impl Default for DefinitionMemory {
    fn default() -> Self {
        Self::new()
    }
}
