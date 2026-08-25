use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

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
                        .merge_missing_definition_type_views_from(definition);
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

    fn merge_known_atomic_facts(
        &mut self,
        child_map: std::collections::HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    ) {
        for (key, child_facts) in child_map {
            let parent_facts = self
                .facts
                .known_atomic_facts_with_0_or_more_than_2_args
                .entry(key)
                .or_default();
            append_missing_atomic_facts(parent_facts, child_facts);
        }
    }

    fn merge_known_atomic_facts_with_1_arg(
        &mut self,
        child_map: std::collections::HashMap<
            (AtomicFactKey, bool),
            std::collections::HashMap<ObjString, AtomicFact>,
        >,
    ) {
        for (key, child_facts) in child_map {
            let parent_facts = self
                .facts
                .known_atomic_facts_with_1_arg
                .entry(key)
                .or_default();
            for (arg_key, fact) in child_facts {
                parent_facts.insert(arg_key, fact);
            }
        }
    }

    fn merge_known_atomic_facts_with_2_args(
        &mut self,
        child_map: std::collections::HashMap<
            (AtomicFactKey, bool),
            std::collections::HashMap<(ObjString, ObjString), AtomicFact>,
        >,
    ) {
        for (key, child_facts) in child_map {
            let parent_facts = self
                .facts
                .known_atomic_facts_with_2_args
                .entry(key)
                .or_default();
            for (arg_key, fact) in child_facts {
                parent_facts.insert(arg_key, fact);
            }
        }
    }

    fn merge_known_exist_facts(
        &mut self,
        child_map: std::collections::HashMap<ExistFactKey, Vec<ExistFactEnum>>,
    ) {
        for (key, child_facts) in child_map {
            let parent_facts = self.facts.known_exist_facts.entry(key).or_default();
            append_missing_exist_facts(parent_facts, child_facts);
        }
    }

    fn merge_known_or_facts(
        &mut self,
        child_map: std::collections::HashMap<OrFactKey, Vec<OrFact>>,
    ) {
        for (key, child_facts) in child_map {
            let parent_facts = self.facts.known_or_facts.entry(key).or_default();
            append_missing_or_facts(parent_facts, child_facts);
        }
    }

    fn merge_child_fact_and_cache_tables(
        &mut self,
        child: Environment,
    ) -> Result<(), RuntimeError> {
        let Environment {
            definitions: _,
            facts,
            objects,
            predicate_properties,
            caches,
        } = child;
        let EnvironmentFactStore {
            known_equality: _,
            known_atomic_facts_with_0_or_more_than_2_args,
            known_atomic_facts_with_1_arg,
            known_atomic_facts_with_2_args,
            known_owner_sets,
            known_direct_supersets,
            known_exist_facts,
            known_or_facts,
            known_atomic_facts_in_forall_facts,
            known_atomic_facts_in_forall_facts_by_arg_shape,
            known_exist_facts_in_forall_facts,
            known_and_facts_in_forall_facts,
            known_or_facts_in_forall_facts,
            stored_facts,
        } = facts;
        let EnvironmentPredicatePropertyStore {
            properties_by_predicate,
        } = predicate_properties;
        let EnvironmentVerificationCache {
            well_defined_objects: cache_well_defined_obj,
            infer_rule_firings: cache_infer_rule_firing,
        } = caches;

        self.merge_known_atomic_facts(known_atomic_facts_with_0_or_more_than_2_args);
        self.merge_known_atomic_facts_with_1_arg(known_atomic_facts_with_1_arg);
        self.merge_known_atomic_facts_with_2_args(known_atomic_facts_with_2_args);
        for (element_key, child_owner_sets) in known_owner_sets {
            let parent_owner_sets = self.facts.known_owner_sets.entry(element_key).or_default();
            for (set_key, evidence) in child_owner_sets {
                parent_owner_sets.entry(set_key).or_insert(evidence);
            }
        }
        for (subset_key, child_supersets) in known_direct_supersets {
            let parent_supersets = self
                .facts
                .known_direct_supersets
                .entry(subset_key)
                .or_default();
            for (superset_key, evidence) in child_supersets {
                parent_supersets.entry(superset_key).or_insert(evidence);
            }
        }
        self.merge_known_exist_facts(known_exist_facts);
        self.merge_known_or_facts(known_or_facts);

        for (key, child_facts) in known_atomic_facts_in_forall_facts {
            let parent_facts = self
                .facts
                .known_atomic_facts_in_forall_facts
                .entry(key)
                .or_default();
            append_missing_atomic_forall_pairs(parent_facts, child_facts);
        }

        for (key, child_shape_map) in known_atomic_facts_in_forall_facts_by_arg_shape {
            let parent_shape_map = self
                .facts
                .known_atomic_facts_in_forall_facts_by_arg_shape
                .entry(key)
                .or_default();
            for (shape_key, child_facts) in child_shape_map {
                let parent_facts = parent_shape_map.entry(shape_key).or_default();
                append_missing_atomic_forall_pairs(parent_facts, child_facts);
            }
        }

        for (key, child_facts) in known_exist_facts_in_forall_facts {
            let parent_facts = self
                .facts
                .known_exist_facts_in_forall_facts
                .entry(key)
                .or_default();
            append_missing_exist_forall_pairs(parent_facts, child_facts);
        }

        for (key, child_facts) in known_and_facts_in_forall_facts {
            let parent_facts = self
                .facts
                .known_and_facts_in_forall_facts
                .entry(key)
                .or_default();
            append_missing_and_forall_pairs(parent_facts, child_facts);
        }

        for (key, child_facts) in known_or_facts_in_forall_facts {
            let parent_facts = self
                .facts
                .known_or_facts_in_forall_facts
                .entry(key)
                .or_default();
            append_missing_or_forall_pairs(parent_facts, child_facts);
        }

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

        for (key, cached) in cache_well_defined_obj {
            self.caches.well_defined_objects.insert(key, cached);
        }
        self.facts.stored_facts.merge_from(stored_facts)?;
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

        for (name, child_properties) in child.predicate_properties.properties_by_predicate.iter() {
            let child_permutations = &child_properties.symmetric_argument_permutations;
            let Some(child_arity) = child_permutations.first().map(Vec::len) else {
                continue;
            };
            let Some(parent_arity) = self
                .predicate_properties
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
    left.binding().id() == right.binding().id() && left.role() == right.role()
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

fn append_missing_atomic_facts(parent: &mut Vec<AtomicFact>, child: Vec<AtomicFact>) {
    let mut seen = HashSet::new();
    for fact in parent.iter() {
        seen.insert(fact.to_string());
    }
    for fact in child {
        if seen.insert(fact.to_string()) {
            parent.push(fact);
        }
    }
}

fn append_missing_exist_facts(parent: &mut Vec<ExistFactEnum>, child: Vec<ExistFactEnum>) {
    let mut seen = HashSet::new();
    for fact in parent.iter() {
        seen.insert(fact.to_string());
    }
    for fact in child {
        if seen.insert(fact.to_string()) {
            parent.push(fact);
        }
    }
}

fn append_missing_or_facts(parent: &mut Vec<OrFact>, child: Vec<OrFact>) {
    let mut seen = HashSet::new();
    for fact in parent.iter() {
        seen.insert(fact.to_string());
    }
    for fact in child {
        if seen.insert(fact.to_string()) {
            parent.push(fact);
        }
    }
}

fn append_missing_atomic_forall_pairs(
    parent: &mut Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = HashSet::new();
    for (fact, stored_forall_conclusion_reference) in parent.iter() {
        seen.insert(forall_pair_key(
            fact.to_string(),
            stored_forall_conclusion_reference,
        ));
    }
    for (fact, stored_forall_conclusion_reference) in child {
        if seen.insert(forall_pair_key(
            fact.to_string(),
            &stored_forall_conclusion_reference,
        )) {
            parent.push((fact, stored_forall_conclusion_reference));
        }
    }
}

fn append_missing_exist_forall_pairs(
    parent: &mut Vec<(ExistFactEnum, Rc<StoredForallConclusionReference>)>,
    child: Vec<(ExistFactEnum, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = HashSet::new();
    for (fact, stored_forall_conclusion_reference) in parent.iter() {
        seen.insert(forall_pair_key(
            fact.to_string(),
            stored_forall_conclusion_reference,
        ));
    }
    for (fact, stored_forall_conclusion_reference) in child {
        if seen.insert(forall_pair_key(
            fact.to_string(),
            &stored_forall_conclusion_reference,
        )) {
            parent.push((fact, stored_forall_conclusion_reference));
        }
    }
}

fn append_missing_and_forall_pairs(
    parent: &mut Vec<(AndFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(AndFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = HashSet::new();
    for (fact, stored_forall_conclusion_reference) in parent.iter() {
        seen.insert(forall_pair_key(
            fact.to_string(),
            stored_forall_conclusion_reference,
        ));
    }
    for (fact, stored_forall_conclusion_reference) in child {
        if seen.insert(forall_pair_key(
            fact.to_string(),
            &stored_forall_conclusion_reference,
        )) {
            parent.push((fact, stored_forall_conclusion_reference));
        }
    }
}

fn append_missing_or_forall_pairs(
    parent: &mut Vec<(OrFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(OrFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = HashSet::new();
    for (fact, stored_forall_conclusion_reference) in parent.iter() {
        seen.insert(forall_pair_key(
            fact.to_string(),
            stored_forall_conclusion_reference,
        ));
    }
    for (fact, stored_forall_conclusion_reference) in child {
        if seen.insert(forall_pair_key(
            fact.to_string(),
            &stored_forall_conclusion_reference,
        )) {
            parent.push((fact, stored_forall_conclusion_reference));
        }
    }
}

fn forall_pair_key(
    fact_key: String,
    stored_forall_conclusion_reference: &StoredForallConclusionReference,
) -> String {
    format!(
        "{}|{}|{:?}",
        fact_key,
        stored_forall_conclusion_reference.source_fact_id,
        stored_forall_conclusion_reference.conclusion_location
    )
}

#[cfg(test)]
#[path = "../../tests/unit/environment/environment_merge/tests.rs"]
mod tests;
