//! Predicate-name to algebraic-property storage.

use crate::prelude::*;
use std::collections::HashMap;

/// Registered algebraic properties of predicates.
#[derive(Clone)]
pub struct EnvironmentPredicatePropertyStore {
    pub properties_by_predicate: HashMap<String, EnvironmentPredicateProperties>,
}

impl EnvironmentPredicatePropertyStore {
    pub fn new() -> Self {
        Self {
            properties_by_predicate: HashMap::new(),
        }
    }

    pub fn properties(&self, predicate_name: &str) -> Option<&EnvironmentPredicateProperties> {
        self.properties_by_predicate.get(predicate_name)
    }

    pub fn properties_mut(
        &mut self,
        predicate_name: String,
    ) -> &mut EnvironmentPredicateProperties {
        self.properties_by_predicate
            .entry(predicate_name)
            .or_default()
    }

    pub fn is_transitive(&self, predicate_name: &str) -> bool {
        self.properties(predicate_name)
            .is_some_and(|properties| properties.is_transitive)
    }

    pub fn symmetric_argument_permutations(
        &self,
        predicate_name: &str,
    ) -> Option<&Vec<Vec<usize>>> {
        self.properties(predicate_name)
            .map(|properties| &properties.symmetric_argument_permutations)
            .filter(|permutations| !permutations.is_empty())
    }

    pub fn is_reflexive(&self, predicate_name: &str) -> bool {
        self.properties(predicate_name)
            .is_some_and(|properties| properties.is_reflexive)
    }

    pub fn is_antisymmetric(&self, predicate_name: &str) -> bool {
        self.properties(predicate_name)
            .is_some_and(|properties| properties.is_antisymmetric)
    }

    pub fn transitive_predicate_count(&self) -> usize {
        self.properties_by_predicate
            .values()
            .filter(|properties| properties.is_transitive)
            .count()
    }

    pub fn symmetric_predicate_count(&self) -> usize {
        self.properties_by_predicate
            .values()
            .filter(|properties| !properties.symmetric_argument_permutations.is_empty())
            .count()
    }

    pub fn symmetric_permutation_count(&self) -> usize {
        self.properties_by_predicate
            .values()
            .map(|properties| properties.symmetric_argument_permutations.len())
            .sum()
    }

    pub fn reflexive_predicate_count(&self) -> usize {
        self.properties_by_predicate
            .values()
            .filter(|properties| properties.is_reflexive)
            .count()
    }

    pub fn antisymmetric_predicate_count(&self) -> usize {
        self.properties_by_predicate
            .values()
            .filter(|properties| properties.is_antisymmetric)
            .count()
    }

    /// Preserve the old summary's property-registration counting semantics:
    /// one predicate may contribute once to each independent property kind.
    pub fn property_registration_count(&self) -> usize {
        self.transitive_predicate_count()
            + self.symmetric_predicate_count()
            + self.reflexive_predicate_count()
            + self.antisymmetric_predicate_count()
    }
}
