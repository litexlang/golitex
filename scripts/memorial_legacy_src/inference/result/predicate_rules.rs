#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinedPredicateParameterRequirementProjectionInferRule {
    pub predicate_name: String,
    pub parameter_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinedPredicateDefinitionClauseProjectionInferRule {
    pub predicate_name: String,
    pub clause_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisteredTransitivePredicateChainClosureInferRule {
    pub predicate_name: String,
    pub start_object_index: usize,
    pub end_object_index: usize,
}
