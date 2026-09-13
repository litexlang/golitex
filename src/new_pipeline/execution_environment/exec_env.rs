use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact};
use crate::new_pipeline::ast::obj::Obj as AstObj;
use crate::new_pipeline::ast::stmt::DefPropStmt as NewDefPropStmt;
use crate::new_pipeline::execution_environment::helper::{
    ast_obj_eq, atomic_fact_proposition_eq,
};
use crate::new_pipeline::runtime::runtime_ids::{FactId, WellDefinednessId};
use crate::prelude::*;
use std::collections::HashMap;

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
    /// `let` object bindings in this scope (name → value + defining equality id).
    pub let_bindings: HashMap<String, LetObjectBinding>,

    /// Equality facts proved (or introduced by `let`) in this scope — new_pipeline AST.
    pub native_equal_facts: HashMap<FactId, EqualFact>,

    /// Non-equality atomic facts stored in this scope (have type facts, proved facts, …).
    pub native_atomic_facts: HashMap<FactId, AtomicFact>,

    /// Well-definedness records for new_pipeline Ast objects in this scope.
    pub native_well_defined: HashMap<String, WellDefinednessId>,

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

/// One `let name = value` binding stored in ExecEnv.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetObjectBinding {
    pub value: AstObj,
    pub equality_fact_id: FactId,
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
    /// Payload fields come later; presence of the key means the name is defined.
    pub symbols: HashMap<String, SymbolDefinitionMemory>,

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

/// One defined atom in `DefinitionMemory.symbols`.
/// Empty for now; may later grow param_type / transparent def / … like the old
/// SymbolDefinition.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolDefinitionMemory {}

/// Facts stored in one execution environment and the indexes used to search
/// them later.
#[derive(Clone)]
pub struct KnownFactMemory {
    /// Canonical facts retained for citations and result construction.
    pub facts_by_id: HashMap<FactId, Fact>,

    pub known_equality: KnownEquality,
    pub known_non_equational_facts: NonEquationalAtomicFactMemory,
    pub set_relations: SpecialSetRelationMemory,
    pub known_exist: ExistFactMemory,
    pub known_or: OrFactMemory,
    pub forall_facts: KnownForallFactMemory,
    pub fact_cache: HashMap<FactString, CachedKnownFact>,
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
            let_bindings: HashMap::new(),
            native_equal_facts: HashMap::new(),
            native_atomic_facts: HashMap::new(),
            native_well_defined: HashMap::new(),
            definitions: DefinitionMemory::new(),
            facts: KnownFactMemory::new(),
            special_object_properties: HashMap::new(),
            prop_algebraic_properties: HashMap::new(),
            well_defined_objects: WellDefinedObjectMemory::new(),
        }
    }

    pub fn store_let_binding(&mut self, name: String, binding: LetObjectBinding) {
        self.let_bindings.insert(name, binding);
    }

    pub fn lookup_let_binding(&self, name: &str) -> Option<&LetObjectBinding> {
        self.let_bindings.get(name)
    }

    pub fn define_symbol(&mut self, name: String, def: SymbolDefinitionMemory) {
        self.definitions.symbols.insert(name, def);
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<&SymbolDefinitionMemory> {
        self.definitions.symbols.get(name)
    }

    pub fn store_native_equal_fact(&mut self, fact: EqualFact) {
        self.native_equal_facts.insert(fact.fact_id, fact);
    }

    pub fn lookup_native_equal_fact(&self, fact_id: FactId) -> Option<&EqualFact> {
        self.native_equal_facts.get(&fact_id)
    }

    pub fn find_native_equal(&self, left: &AstObj, right: &AstObj) -> Option<FactId> {
        for (id, fact) in &self.native_equal_facts {
            if ast_obj_eq(&fact.left, left) && ast_obj_eq(&fact.right, right) {
                return Some(*id);
            }
            if ast_obj_eq(&fact.left, right) && ast_obj_eq(&fact.right, left) {
                return Some(*id);
            }
        }
        None
    }

    pub fn store_native_atomic_fact(&mut self, fact: AtomicFact) {
        let fact_id = crate::new_pipeline::execution_environment::helper::atomic_fact_id(&fact);
        self.native_atomic_facts.insert(fact_id, fact);
    }

    pub fn find_native_atomic_fact(&self, goal: &AtomicFact) -> Option<FactId> {
        for (id, known) in &self.native_atomic_facts {
            if atomic_fact_proposition_eq(known, goal) {
                return Some(*id);
            }
        }
        None
    }

    pub fn lookup_native_wd(&self, object_key: &str) -> Option<WellDefinednessId> {
        self.native_well_defined.get(object_key).copied()
    }

    pub fn record_native_wd(&mut self, object_key: String, wd_id: WellDefinednessId) {
        self.native_well_defined.entry(object_key).or_insert(wd_id);
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
    ///
    /// Re-recording the same object or proof id is idempotent.  Debug builds
    /// additionally detect an accidental collision between different objects
    /// and the same canonical key or proof id.
    pub fn record(&mut self, object: Obj, wd_id: WellDefinednessId) {
        let object_key = obj_equality_key(&object);

        if let Some(existing_id) = self.object_to_wd_id.get(&object_key) {
            debug_assert_eq!(*existing_id, wd_id);
            return;
        }

        if let Some(existing_object) = self.wd_id_to_object.get(&wd_id) {
            debug_assert_eq!(obj_equality_key(existing_object), object_key);
            return;
        }

        self.object_to_wd_id.insert(object_key, wd_id);
        self.wd_id_to_object.insert(wd_id, object);
    }
}

impl DefinitionMemory {
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
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

impl KnownFactMemory {
    pub fn new() -> Self {
        Self {
            facts_by_id: HashMap::new(),
            known_equality: KnownEquality::new(),
            known_non_equational_facts: NonEquationalAtomicFactMemory::new(),
            set_relations: SpecialSetRelationMemory::new(),
            known_exist: ExistFactMemory::new(),
            known_or: OrFactMemory::new(),
            forall_facts: KnownForallFactMemory::new(),
            fact_cache: HashMap::new(),
        }
    }
}

impl Default for KnownFactMemory {
    fn default() -> Self {
        Self::new()
    }
}
