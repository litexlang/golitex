pub struct ExecEnv {
    /// Definitions and symbol identities for declarations visible to later
    /// statements.
    pub definitions: DefinitionMemory,

    /// Stored facts and indexes used to find mathematical evidence.
    pub facts: KnownFactMemory,

    /// Known object values and shape facets keyed by canonical object string.
    pub object_properties: ObjectPropertyMemory,

    /// Algebraic properties registered for predicates, such as transitivity,
    /// symmetry, reflexivity, and antisymmetry.
    pub prop_algebraic_properties: PropAlgebraicPropertyMemory,

    /// Objects whose well-definedness has been established in this environment.
    /// The proof itself remains owned by the corresponding Result.
    /// 每次当前环境里证明了某个东西的wd后，都会被放进来。
    pub well_defined_objects: HashMap<ObjString, WellDefinednessId2>,
    pub known_well_defined_fact_ids: HashMap<Id>,
}

pub struct KnownFactMemory {
    pub known_equality: KnownEquality,
    pub atomic: AtomicFactIndex,
    pub set_relations: SetRelationIndex,
    pub quantified: QuantifiedFactIndex,
    pub forall_conclusions: ForallConclusionIndex,
    pub stored_facts: EnvironmentStoredFactStore,
    pub known_fact_cache: HashMap<FactString, CachedKnownFact>,
    pub facts_by_id: HashMap<FactId, Fact>,
}
