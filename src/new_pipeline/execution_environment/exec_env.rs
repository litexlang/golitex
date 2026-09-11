pub struct ExecEnv {
    // 每次对应 atom 的时候都要往里面store一下
    pub defined_atoms_and_their_ids: HashMap<Id, Atom>,

    // 里面存了predicate,atom,struct等各种定义。每次定义东西的时候放
    pub definitions: DefinitionMemory,

    // 每次store fact的时候往里面放一下
    pub known_facts_and_their_id: HashMap<Id, Fact>,
    pub facts: KnownFactMemory,

    // store fact如果是特殊的事实那往里面放
    pub special_object_properties: HashMap<ObjString, Vec<SpecialObjProperty>>,

    // 每次证明出来prop的性质的时候放一下
    pub prop_algebraic_properties: HashMap<PropName, Vec<PropAlgebraicProperty>>,

    // 每次证明好一个obj的wd的时候放一下。这是重大的架构更新。以后每次检查wd的时候需要看一下有没有cache过了。如果之前证明过了这个obj是两良好定义的，那就直接成立了
    pub well_defined_objects_and_their_ids: HashMap<ObjString, Id>,

    // 我不太确定这个东西有没有有用，放一下再说
    pub known_prop_algebraic_property_ids: HashMap<Id, (PropName, PropAlgebraicProperty)>,

    // 我不太确定这个东西有没有有用，放一下再说
    pub well_defined_ids_of_objects: HashMap<Id, Obj>,
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
    SymmetricArgumentPermutate(Box<Vec<Vec<usize>>>),
    Reflexive,
    Antisymmetric,
}

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
