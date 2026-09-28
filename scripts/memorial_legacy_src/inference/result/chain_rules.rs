/// One non-adjacent equality exposed by an exact source relation chain.
///
/// The object interval is half-open over the chain edges and closed over its
/// endpoint objects: `[start_object_index, end_object_index]` consumes exactly
/// the adjacent equalities at edge indexes `start..end`. Consumers must check
/// those premises against the source chain before folding transitivity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityChainClosureInferRule {
    pub start_object_index: usize,
    pub end_object_index: usize,
}

/// One non-adjacent consequence of a numeric `<`/`<=` or `>`/`>=` chain.
/// The exact ordered premises remain in the Result application; these indexes
/// freeze the source interval without encoding a theorem-specific pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NumericOrderChainClosureInferRule {
    pub start_object_index: usize,
    pub end_object_index: usize,
}
