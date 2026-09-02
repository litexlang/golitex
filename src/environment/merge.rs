//! Transactional merge of one committed child Environment.

use crate::prelude::*;
use std::collections::HashSet;

impl Environment {
    pub fn merge_committed_child(&mut self, child: Environment) -> Result<(), RuntimeError> {
        self.validate_committed_child(&child)?;
        self.merge_committed_child_in_place(child)
    }

    fn merge_committed_child_in_place(&mut self, child: Environment) -> Result<(), RuntimeError> {
        self.merge_defined_names(&child)?;
        self.merge_equalities_from_child(&child)?;
        self.merge_child_fact_and_cache_tables(child)?;
        Ok(())
    }

    fn merge_defined_names(&mut self, child: &Environment) -> Result<(), RuntimeError> {
        for (name, definition) in child.definitions.symbols.iter() {
            if let Some(existing) = self.definitions.symbols.get(name) {
                if same_symbol_definition(existing, definition) {
                    let existing_symbol_id = existing.binding().id();
                    self.definitions
                        .symbols
                        .get_by_id_mut(existing_symbol_id)
                        .expect("the matching parent symbol should remain present")
                        .merge_missing_direct_struct_carrier_from(definition);
                    self.definitions
                        .symbols
                        .get_by_id_mut(existing_symbol_id)
                        .expect("the matching parent symbol should remain present")
                        .merge_missing_transparent_object_definition_from(definition);
                    continue;
                }
                return Err(merge_name_conflict_error(
                    name,
                    existing.role().description(),
                ));
            }
            self.definitions
                .symbols
                .insert(definition.clone())
                .expect("symbol was checked absent before merge");
        }

        for (name, stmt) in child.definitions.predicate_definitions.iter() {
            if self.definitions.predicate_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "prop"));
            }
            if self
                .definitions
                .abstract_predicate_definitions
                .contains_key(name)
            {
                return Err(merge_name_conflict_error(name, "abstract_prop"));
            }
            self.definitions
                .predicate_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.abstract_predicate_definitions.iter() {
            if self
                .definitions
                .abstract_predicate_definitions
                .contains_key(name)
            {
                return Err(merge_name_conflict_error(name, "abstract_prop"));
            }
            if self.definitions.predicate_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "prop"));
            }
            self.definitions
                .abstract_predicate_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.algorithm_definitions.iter() {
            if self.definitions.algorithm_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "algo"));
            }
            self.definitions
                .algorithm_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.structure_definitions.iter() {
            if self.definitions.structure_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "struct"));
            }
            self.definitions
                .structure_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.template_definitions.iter() {
            if self.definitions.template_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "template"));
            }
            self.definitions
                .template_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.setting_definitions.iter() {
            if self.definitions.setting_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "setting"));
            }
            self.definitions
                .setting_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.theorem_definitions.iter() {
            if self.definitions.theorem_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "thm"));
            }
            self.definitions
                .theorem_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.axiom_definitions.iter() {
            if self.definitions.axiom_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "axiom"));
            }
            self.definitions
                .axiom_definitions
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.definitions.strategy_definitions.iter() {
            if self.definitions.strategy_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "strategy"));
            }
            self.definitions
                .strategy_definitions
                .insert(name.clone(), stmt.clone());
        }

        Ok(())
    }

    fn merge_equalities_from_child(&mut self, child: &Environment) -> Result<(), RuntimeError> {
        let mut seen_equalities = HashSet::new();
        let mut child_equalities = Vec::new();
        for (_, (direct_proof_map, _)) in child.facts.known_equality.iter() {
            for atomic_fact in direct_proof_map.values() {
                let AtomicFact::EqualFact(equal_fact) = atomic_fact else {
                    continue;
                };
                let key = unordered_equality_key(equal_fact);
                if seen_equalities.insert(key) {
                    child_equalities.push(equal_fact.clone());
                }
            }
        }

        for equality in child_equalities.iter() {
            self.store_equality(equality)?;
        }

        Ok(())
    }

    fn merge_child_fact_and_cache_tables(
        &mut self,
        child: Environment,
    ) -> Result<(), RuntimeError> {
        let Environment {
            definitions: _,
            facts,
            objects,
            predicate_algebraic_properties,
            caches,
        } = child;
        let EnvironmentPredicateAlgebraicPropertyStore {
            properties_by_predicate,
        } = predicate_algebraic_properties;
        let EnvironmentVerificationCache {
            infer_rule_firings: cache_infer_rule_firing,
        } = caches;

        self.facts.merge_non_equality_from(facts)?;

        self.objects.merge_from(objects);

        for (name, properties) in properties_by_predicate {
            if properties.is_transitive {
                self.store_transitive_prop_name(name.clone());
            }
            if properties.is_reflexive {
                self.store_reflexive_prop_name(name.clone());
            }
            if properties.is_antisymmetric {
                self.store_antisymmetric_prop_name(name.clone());
            }
            for permutation in properties.symmetric_argument_permutations {
                self.store_symmetric_prop_permutation(
                    name.clone(),
                    permutation,
                    default_line_file(),
                )?;
            }
        }

        for (key, _) in cache_infer_rule_firing {
            self.caches.infer_rule_firings.insert(key, ());
        }

        Ok(())
    }

    fn validate_committed_child(&self, child: &Environment) -> Result<(), RuntimeError> {
        for (name, child_definition) in child.definitions.symbols.iter() {
            if let Some(existing) = self.definitions.symbols.get(name) {
                if same_symbol_definition(existing, child_definition) {
                    continue;
                }
                return Err(merge_name_conflict_error(
                    name,
                    existing.role().description(),
                ));
            }
        }

        for name in child.definitions.predicate_definitions.keys() {
            if self.definitions.predicate_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "prop"));
            }
            if self
                .definitions
                .abstract_predicate_definitions
                .contains_key(name)
            {
                return Err(merge_name_conflict_error(name, "abstract_prop"));
            }
        }
        for name in child.definitions.abstract_predicate_definitions.keys() {
            if self
                .definitions
                .abstract_predicate_definitions
                .contains_key(name)
            {
                return Err(merge_name_conflict_error(name, "abstract_prop"));
            }
            if self.definitions.predicate_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "prop"));
            }
        }
        for name in child.definitions.algorithm_definitions.keys() {
            if self.definitions.algorithm_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "algo"));
            }
        }
        for name in child.definitions.structure_definitions.keys() {
            if self.definitions.structure_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "struct"));
            }
        }
        for name in child.definitions.template_definitions.keys() {
            if self.definitions.template_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "template"));
            }
        }
        for name in child.definitions.setting_definitions.keys() {
            if self.definitions.setting_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "setting"));
            }
        }
        for name in child.definitions.theorem_definitions.keys() {
            if self.definitions.theorem_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "thm"));
            }
        }
        for name in child.definitions.axiom_definitions.keys() {
            if self.definitions.axiom_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "axiom"));
            }
        }
        for name in child.definitions.strategy_definitions.keys() {
            if self.definitions.strategy_definitions.contains_key(name) {
                return Err(merge_name_conflict_error(name, "strategy"));
            }
        }

        for (name, child_properties) in child
            .predicate_algebraic_properties
            .properties_by_predicate
            .iter()
        {
            let child_permutations = &child_properties.symmetric_argument_permutations;
            let Some(child_arity) = child_permutations.first().map(Vec::len) else {
                continue;
            };
            let Some(parent_arity) = self
                .predicate_algebraic_properties
                .symmetric_argument_permutations(name)
                .and_then(|permutations| permutations.first())
                .map(Vec::len)
            else {
                continue;
            };
            if parent_arity != child_arity {
                return Err(
                    StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "store_symmetric_prop_permutation: `{}` already has arity {}, got {}",
                            name, parent_arity, child_arity
                        ),
                        default_line_file(),
                    ))
                    .into(),
                );
            }
        }

        Ok(())
    }
}

fn same_symbol_definition(left: &SymbolDefinition, right: &SymbolDefinition) -> bool {
    if left.binding().id() != right.binding().id() || left.role() != right.role() {
        return false;
    }
    match (
        left.transparent_object_definition(),
        right.transparent_object_definition(),
    ) {
        (Some(left), Some(right)) => left.is_same_definition_as(right),
        _ => true,
    }
}

fn merge_name_conflict_error(name: &str, existing_namespace: &str) -> RuntimeError {
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
        "cannot commit child environment: name `{}` is already used in parent as {}",
        name, existing_namespace
    )))
    .into()
}

fn unordered_equality_key(equal_fact: &EqualFact) -> String {
    let left = equal_fact.left.to_string();
    let right = equal_fact.right.to_string();
    if left <= right {
        format!("{}\n{}", left, right)
    } else {
        format!("{}\n{}", right, left)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/environment/environment_merge/tests.rs"]
mod tests;
