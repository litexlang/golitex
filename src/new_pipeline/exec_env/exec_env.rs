use crate::new_pipeline::ast::names::{AtomicName, BoundName, PlainName};
use crate::new_pipeline::ast::obj::{FiniteSeqSet, FnSet, Obj, SeqSet, StructObj};
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::ast::stmt::AxiomStmt;
use crate::new_pipeline::ast::stmt::DefAbstractPropStmt;
use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::ast::stmt::DefSettingStmt;
use crate::new_pipeline::ast::stmt::DefStrategyStmt;
use crate::new_pipeline::ast::stmt::DefStructStmt;
use crate::new_pipeline::ast::stmt::DefTemplateStmt;
use crate::new_pipeline::ast::stmt::DefThmStmt;
use crate::new_pipeline::ast::stmt::HaveFnByForallExistUniqueStmt;
use crate::new_pipeline::ast::stmt::HaveFnByInducStmt;
use crate::new_pipeline::ast::stmt::HaveFnEqualCaseByCaseStmt;
use crate::new_pipeline::ast::stmt::HaveFnEqualStmt;
use crate::new_pipeline::ast::stmt::HaveObjByExistFactsStmt;
use crate::new_pipeline::ast::stmt::HaveObjEqualStmt;
use crate::new_pipeline::ast::stmt::HaveObjInNonemptySetOrParamTypeStmt;
use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::ast::stmt::TrustHaveStmt;
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::runtime::runtime_ids::{FactId, WellDefinednessId};
use std::collections::HashMap;
use std::rc::Rc;

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

    /// Definition-time shape memory only. Never written from arbitrary stored facts.
    pub special_object_properties: HashMap<ObjIR, Vec<SpecialObjectPropertyByDefinition>>,

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

/// Where a name in `DefinitionMemory.identifiers` came from.
///
/// User-level object defs keep `(name, introducing stmt)`.
/// Scoped binders share `ParamType((BoundName, ParamType))` — name is on `BoundName`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StoredIdentifierDefinition {
    HaveObjInNonemptySetOrParamType((String, Rc<HaveObjInNonemptySetOrParamTypeStmt>)),
    HaveObjEqual((String, Rc<HaveObjEqualStmt>)),
    HaveObjByExistFacts((String, Rc<HaveObjByExistFactsStmt>)),
    TrustHave((String, Rc<TrustHaveStmt>)),
    LetObj((String, Rc<LetObjStmt>)),
    HaveFnEqual((String, Rc<HaveFnEqualStmt>)),
    HaveFnEqualCaseByCase((String, Rc<HaveFnEqualCaseByCaseStmt>)),
    HaveFnByForallExistUnique((String, Rc<HaveFnByForallExistUniqueStmt>)),
    HaveFnByInduc((String, Rc<HaveFnByInducStmt>)),
    /// Local / scoped typed binder (`forall`, `prop` params, struct fields, …).
    ParamType((BoundName, ParamType)),
}

/// Definitions introduced in one execution environment.
///
/// All maps are keyed by `PlainName` (unqualified local name);
/// `Mod::Export::name` is a reference path, not a store key.
#[derive(Clone)]
pub struct DefinitionMemory {
    /// Named atoms defined in this scope (`let`, `have`, forall/exist locals, …).
    pub identifiers: HashMap<PlainName, StoredIdentifierDefinition>,

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

/// Algebraic properties that can be proved for a predicate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropRewriteProperty {
    Transitive,
    SymmetricArgumentPermutate(Vec<Vec<usize>>),
    Reflexive,
}

/// Definition-channel object shapes. Only definition exits may write these
/// (have/let/have fn/typed params/template WD/field-from-struct-def, …).
/// Post-hoc `$in` / `=` proofs must not mutate this memory.
#[derive(Clone)]
pub enum SpecialObjectPropertyByDefinition {
    /// Callable signature from a definition exit; cite the definitional membership FactId.
    InFunctionSet((FnSet, FactId)),
    /// `f = anon` from a definition exit; cite the defining equality FactId.
    EqualToFunction((Obj, FactId)),
    /// Definition-time struct carrier only (`have p &Point`, `forall p &Point`, …).
    /// Never written from a later `$in &Struct` proof (avoids carrier conflicts).
    /// `FactId` cites the definition-time membership `p $in &Point`.
    /// Example: after `have p &Point`, key `p` stores `(&Point, fact_id)` for `p.x` WD.
    DefinedAsStruct((StructObj, FactId)),
    /// Definition-time `a $in finite_seq(S, n)`; cite the definitional membership FactId.
    DefinedAsFiniteSeq((FiniteSeqSet, FactId)),
    /// Definition-time `a $in seq(S)`; cite the definitional membership FactId.
    DefinedAsSeqSet((SeqSet, FactId)),
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

    pub fn lookup_def_thm(&self, name: &str) -> Option<&DefThmStmt> {
        self.definitions.theorem_definitions.get(name)
    }

    pub fn store_def_thm(&mut self, def_thm: DefThmStmt) {
        self.definitions
            .theorem_definitions
            .insert(def_thm.name.clone(), def_thm);
    }

    pub fn lookup_def_struct(&self, name: &str) -> Option<&DefStructStmt> {
        self.definitions.structure_definitions.get(name)
    }

    pub fn store_def_struct(&mut self, def_struct: DefStructStmt) {
        self.definitions
            .structure_definitions
            .insert(def_struct.name.clone(), def_struct);
    }

    pub fn lookup_def_template(&self, name: &str) -> Option<&DefTemplateStmt> {
        self.definitions.template_definitions.get(name)
    }

    pub fn store_def_template(&mut self, def_template: DefTemplateStmt) {
        self.definitions
            .template_definitions
            .insert(def_template.template_name.clone(), def_template);
    }

    pub fn lookup_axiom(&self, name: &str) -> Option<&AxiomStmt> {
        self.definitions.axiom_definitions.get(name)
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
