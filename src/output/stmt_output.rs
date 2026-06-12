struct StoreFactOutput {
    original_fact: Fact,
    infer: Vec<Fact>,
}

struct DefineParamsAndAssumeTheirPropertiesOutput {
    params: Vec<Param>,
    assume_properties: Vec<Fact>,
}

enum AtomicFactVerificationOutput {
    ByKnownAtomicFact(AtomicFactVerificationByKnownAtomicFactOutput),
    ByKnownForallFact(AtomicFactVerificationByKnownForallFactOutput),
    ByDefinition(AtomicFactVerificationByDefinitionOutput),
    ByBuiltinRule(AtomicFactVerificationByBuiltinRuleOutput),
    ByStrategy(AtomicFactVerificationByStrategyOutput),
}

struct AtomicFactOutput {
    store_fact_output: StoreFactOutput,
}
