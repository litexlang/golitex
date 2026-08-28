//! Environment-owned algebraic property profile for one predicate.

/// All algebraic properties currently registered for one predicate.
///
/// Keeping one profile per predicate makes the predicate name the single
/// ownership key. A property is independently optional.
#[derive(Clone, Default)]
pub struct EnvironmentPredicateProperties {
    pub is_transitive: bool,
    pub symmetric_argument_permutations: Vec<Vec<usize>>,
    pub is_reflexive: bool,
    pub is_antisymmetric: bool,
}
