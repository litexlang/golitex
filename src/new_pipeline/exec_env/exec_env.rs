use crate::new_pipeline::ast::names::{AtomicName, PlainName};
use crate::new_pipeline::ast::obj::{
    Cart, FiniteSeqListObj, FiniteSeqSet, FnSet, Obj, SetBuilder, Tuple,
};
use crate::new_pipeline::ast::stmt::AxiomStmt;
use crate::new_pipeline::ast::stmt::DefAbstractPropStmt;
use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::ast::stmt::DefSettingStmt;
use crate::new_pipeline::ast::stmt::DefStrategyStmt;
use crate::new_pipeline::ast::stmt::DefStructStmt;
use crate::new_pipeline::ast::stmt::DefTemplateStmt;
use crate::new_pipeline::ast::stmt::DefThmStmt;
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::runtime::runtime_ids::{FactId, WellDefinednessId};
use std::collections::HashMap;

pub use super::known_fact_memory::{
    AtomicExceptEqualityFactMemory, KnownEqualityMemory, KnownFactMemory,
};

// -----------------------------------------------------------------------------
// Core data model
// -----------------------------------------------------------------------------

/// State owned by one execution scope.
///
/// Together with `Runtime`, this is core data model.  `Runtime` owns the live
/// stacks and session; each `ExecEnv` is one scope's definitions, facts, and
/// WD records.
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
    pub special_object_properties: HashMap<ObjIR, Vec<SpecialObjProperty>>,

    /// Algebraic properties proved for predicates in this scope.
    pub prop_rewrite_properties: HashMap<AtomicName, Vec<PropRewriteProperty>>,

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
    pub object_to_wd_id: HashMap<ObjIR, WellDefinednessId>,

    /// Proof identity back to the object carried by a result or citation.
    pub wd_id_to_object: HashMap<WellDefinednessId, Obj>,
}

/// Definitions introduced in one execution environment.
///
/// All maps are keyed by `PlainName` (unqualified local name);
/// `Mod::Export::name` is a reference path, not a store key.
#[derive(Clone)]
pub struct DefinitionMemory {
    /// Named atoms defined in this scope (`let`, `have`, forall/exist locals, …).
    pub identifiers: HashMap<PlainName, DefinedIdentifierInfo>,

    pub predicate_definitions: HashMap<PlainName, DefPropStmt>,
    pub abstract_predicate_definitions: HashMap<PlainName, DefAbstractPropStmt>,
    pub algorithm_definitions: HashMap<PlainName, DefAlgoStmt>,
    pub structure_definitions: HashMap<PlainName, DefStructStmt>,
    pub template_definitions: HashMap<PlainName, DefTemplateStmt>,
    pub setting_definitions: HashMap<PlainName, DefSettingStmt>,
    pub theorem_definitions: HashMap<PlainName, DefThmStmt>,
    pub axiom_definitions: HashMap<PlainName, AxiomStmt>,
    pub strategy_definitions: HashMap<PlainName, DefStrategyStmt>,
}

/// One defined atom in `DefinitionMemory.identifiers`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinedIdentifierInfo {
    pub identifier: String,
}

/// Algebraic properties that can be proved for a predicate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropRewriteProperty {
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
    /// Non-closed object equals a closed numeric expr; cite `FactId`.
    /// Example: from `a = 2^3/7 + 10 * 2.5`, key `a` stores the closed RHS.
    ClosedNumericEqual((Obj, FactId)),
    InFunctionSet((FnSet, FactId)),
    EqualToFunction((Obj, FactId)),
}

// -----------------------------------------------------------------------------
// Construction and memory operations
// -----------------------------------------------------------------------------

impl ExecEnv {
    pub fn new() -> Self {
        Self {
            definitions: DefinitionMemory::new(),
            facts: KnownFactMemory::new(),
            special_object_properties: HashMap::new(),
            prop_rewrite_properties: HashMap::new(),
            well_defined_objects: WellDefinedObjectMemory::new(),
        }
    }

    pub fn lookup_def_prop(&self, name: &str) -> Option<&DefPropStmt> {
        self.definitions.predicate_definitions.get(name)
    }

    pub fn store_def_prop(&mut self, def_prop: DefPropStmt) {
        self.definitions
            .predicate_definitions
            .insert(def_prop.name.clone(), def_prop);
    }

    pub fn lookup_def_abstract_prop(&self, name: &str) -> Option<&DefAbstractPropStmt> {
        self.definitions.abstract_predicate_definitions.get(name)
    }

    pub fn store_def_abstract_prop(&mut self, def_abstract_prop: DefAbstractPropStmt) {
        self.definitions
            .abstract_predicate_definitions
            .insert(def_abstract_prop.name.clone(), def_abstract_prop);
    }

    // Success path of exec_stmt: commit the temp child into this parent.
    // Failed discards the child instead — see merge_exec_env.rs module docs.
    pub fn merge_from(
        &mut self,
        child: &ExecEnv,
    ) -> crate::new_pipeline::runtime::RuntimeResult<()> {
        super::merge_exec_env::merge_exec_env_from(self, child)
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
        self.object_to_wd_id.get(&object.ir()).copied()
    }

    /// Record a WD proof and its object payload in both directions.
    /// Re-recording the same object or proof id is idempotent.
    pub fn record(&mut self, object: Obj, wd_id: WellDefinednessId) {
        let object_key = object.ir();

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
