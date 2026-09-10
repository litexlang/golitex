pub struct ExecEnv {
    pub defined_atoms_and_their_ids: HashMap<Id, Atom>,
    pub definitions: DefinitionMemory,

    pub known_facts_and_their_id: HashMap<Id, Fact>,
    pub facts: KnownFactMemory,

    pub special_object_properties: HashMap<ObjString, SpecialObjectPropertyMemory>,

    pub known_prop_algebraic_property_ids: HashMap<Id, (PropName, PropAlgebraicProperty)>,
    pub prop_algebraic_properties: HashMap<PropName, Vec<PropAlgebraicProperty>>,

    pub well_defined_objects_and_their_ids: HashMap<ObjString, Id>,
}

pub struct DefinitionMemory {
    pub symbol_definitions: HashMap<String, SymbolDefinition>,
    pub predicate_definitions: HashMap<PropName, DefPropStmt>,
    pub abstract_predicate_definitions: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub algorithm_definitions: HashMap<AlgoName, DefAlgoStmt>,
    pub structure_definitions: HashMap<StructName, DefStructStmt>,
    pub template_definitions: HashMap<TemplateName, DefTemplateStmt>,
    pub setting_definitions: HashMap<String, DefSettingStmt>,
    pub theorem_definitions: HashMap<ThmName, DefThmStmt>,
    pub axiom_definitions: HashMap<ThmName, AxiomStmt>,
    pub strategy_definitions: HashMap<StrategyName, DefStrategyStmt>,
}

pub struct KnownFactMemory {
    pub known_equality: KnownEquality,
    pub atomic: AtomicFactMemory,
    pub set_relations: SetRelationMemory,
    pub or_facts: HashMap<OrFactKey, Vec<OrFact>>,
    pub exist_facts: HashMap<ExistFactKey, Vec<ExistFact>>,
    pub forall_facts: ForallConclusionMemory,
    pub fact_cache: HashMap<FactString, CachedKnownFact>,
}

pub enum PropAlgebraicProperty {
    Transitive,
    SymmetricArgumentPermutate(Vec<Vec<usize>>),
    Reflexive,
    Antisymmetric,
}
