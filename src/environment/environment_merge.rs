use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

impl Environment {
    pub fn merge_committed_child(&mut self, child: Environment) -> Result<(), RuntimeError> {
        let mut merged = self.clone();
        merged.merge_committed_child_in_place(child)?;
        *self = merged;
        Ok(())
    }

    fn merge_committed_child_in_place(&mut self, child: Environment) -> Result<(), RuntimeError> {
        self.merge_defined_names(&child)?;
        self.merge_equalities_from_child(&child)?;
        self.merge_child_fact_and_cache_tables(child)?;
        Ok(())
    }

    fn merge_defined_names(&mut self, child: &Environment) -> Result<(), RuntimeError> {
        for (name, kind) in child.defined_identifiers.iter() {
            if self.defined_identifiers.contains_key(name) {
                return Err(merge_name_conflict_error(name, "identifier"));
            }
            self.defined_identifiers.insert(name.clone(), kind.clone());
        }

        for (name, stmt) in child.defined_def_props.iter() {
            if self.defined_def_props.contains_key(name) {
                return Err(merge_name_conflict_error(name, "prop"));
            }
            if self.defined_abstract_props.contains_key(name) {
                return Err(merge_name_conflict_error(name, "abstract_prop"));
            }
            self.defined_def_props.insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.defined_abstract_props.iter() {
            if self.defined_abstract_props.contains_key(name) {
                return Err(merge_name_conflict_error(name, "abstract_prop"));
            }
            if self.defined_def_props.contains_key(name) {
                return Err(merge_name_conflict_error(name, "prop"));
            }
            self.defined_abstract_props
                .insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.defined_algorithms.iter() {
            if self.defined_algorithms.contains_key(name) {
                return Err(merge_name_conflict_error(name, "algo"));
            }
            self.defined_algorithms.insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.defined_structs.iter() {
            if self.defined_structs.contains_key(name) {
                return Err(merge_name_conflict_error(name, "struct"));
            }
            self.defined_structs.insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.defined_templates.iter() {
            if self.defined_templates.contains_key(name) {
                return Err(merge_name_conflict_error(name, "template"));
            }
            self.defined_templates.insert(name.clone(), stmt.clone());
        }

        for (name, stmt) in child.defined_thm_stmts.iter() {
            if self.defined_thm_stmts.contains_key(name) {
                return Err(merge_name_conflict_error(name, "thm"));
            }
            self.defined_thm_stmts.insert(name.clone(), stmt.clone());
        }
        for (name, summary) in child.defined_thm_trust_summaries.iter() {
            self.defined_thm_trust_summaries
                .insert(name.clone(), summary.clone());
        }

        for (name, stmt) in child.defined_strategy_stmts.iter() {
            if self.defined_strategy_stmts.contains_key(name) {
                return Err(merge_name_conflict_error(name, "strategy"));
            }
            self.defined_strategy_stmts
                .insert(name.clone(), stmt.clone());
        }

        Ok(())
    }

    fn merge_equalities_from_child(&mut self, child: &Environment) -> Result<(), RuntimeError> {
        let mut seen_equalities = HashSet::new();
        let mut child_equalities = Vec::new();
        for (_, (direct_proof_map, _)) in child.known_equality.iter() {
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
            let parent_facts = self.known_atomic_facts_with_1_arg.entry(key).or_default();
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
            let parent_facts = self.known_atomic_facts_with_2_args.entry(key).or_default();
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
            let parent_facts = self.known_exist_facts.entry(key).or_default();
            append_missing_exist_facts(parent_facts, child_facts);
        }
    }

    fn merge_known_or_facts(
        &mut self,
        child_map: std::collections::HashMap<OrFactKey, Vec<OrFact>>,
    ) {
        for (key, child_facts) in child_map {
            let parent_facts = self.known_or_facts.entry(key).or_default();
            append_missing_or_facts(parent_facts, child_facts);
        }
    }

    fn merge_child_fact_and_cache_tables(
        &mut self,
        child: Environment,
    ) -> Result<(), RuntimeError> {
        let Environment {
            defined_identifiers: _,
            defined_def_props: _,
            defined_abstract_props: _,
            defined_algorithms: _,
            defined_structs: _,
            defined_templates: _,
            defined_thm_stmts: _,
            defined_thm_trust_summaries: _,
            defined_strategy_stmts: _,
            known_equality: _,
            known_atomic_facts_with_0_or_more_than_2_args,
            known_atomic_facts_with_1_arg,
            known_atomic_facts_with_2_args,
            known_exist_facts,
            known_or_facts,
            known_atomic_facts_in_forall_facts,
            known_atomic_facts_in_forall_facts_by_arg_shape,
            known_exist_facts_in_forall_facts,
            known_and_facts_in_forall_facts,
            known_or_facts_in_forall_facts,
            known_objs_equal_to_tuple,
            known_objs_equal_to_cart,
            known_objs_equal_to_finite_seq_list,
            known_objs_equal_to_matrix_list,
            known_obj_values,
            known_objs_equal_to_set_builder,
            known_objs_in_fn_sets,
            known_transitive_props,
            known_symmetric_props,
            known_reflexive_props,
            known_antisymmetric_props,
            cache_well_defined_obj,
            cache_known_fact,
            cache_known_fact_trust,
            used_strategy_stmts,
            stopped_strategy_stmts,
        } = child;

        self.merge_known_atomic_facts(known_atomic_facts_with_0_or_more_than_2_args);
        self.merge_known_atomic_facts_with_1_arg(known_atomic_facts_with_1_arg);
        self.merge_known_atomic_facts_with_2_args(known_atomic_facts_with_2_args);
        self.merge_known_exist_facts(known_exist_facts);
        self.merge_known_or_facts(known_or_facts);

        for (key, child_facts) in known_atomic_facts_in_forall_facts {
            let parent_facts = self
                .known_atomic_facts_in_forall_facts
                .entry(key)
                .or_default();
            append_missing_atomic_forall_pairs(parent_facts, child_facts);
        }

        for (key, child_shape_map) in known_atomic_facts_in_forall_facts_by_arg_shape {
            let parent_shape_map = self
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
                .known_exist_facts_in_forall_facts
                .entry(key)
                .or_default();
            append_missing_exist_forall_pairs(parent_facts, child_facts);
        }

        for (key, child_facts) in known_and_facts_in_forall_facts {
            let parent_facts = self.known_and_facts_in_forall_facts.entry(key).or_default();
            append_missing_and_forall_pairs(parent_facts, child_facts);
        }

        for (key, child_facts) in known_or_facts_in_forall_facts {
            let parent_facts = self.known_or_facts_in_forall_facts.entry(key).or_default();
            append_missing_or_forall_pairs(parent_facts, child_facts);
        }

        for (name, (tuple, cart, line_file)) in known_objs_equal_to_tuple {
            let old = self.known_objs_equal_to_tuple.get(&name).cloned();
            let merged_tuple = match (tuple, old.as_ref()) {
                (Some(new_tuple), _) => Some(new_tuple),
                (None, Some((old_tuple, _, _))) => old_tuple.clone(),
                (None, None) => None,
            };
            let merged_cart = match (cart, old.as_ref()) {
                (Some(new_cart), _) => Some(new_cart),
                (None, Some((_, old_cart, _))) => old_cart.clone(),
                (None, None) => None,
            };
            self.known_objs_equal_to_tuple
                .insert(name, (merged_tuple, merged_cart, line_file));
        }

        for (name, value) in known_objs_equal_to_cart {
            self.known_objs_equal_to_cart.insert(name, value);
        }

        for (name, (list, member_of, line_file)) in known_objs_equal_to_finite_seq_list {
            let old = self.known_objs_equal_to_finite_seq_list.get(&name).cloned();
            let merged_member = match (member_of, old.as_ref()) {
                (Some(new_member), _) => Some(new_member),
                (None, Some((_, Some(old_member), _))) => Some(old_member.clone()),
                (None, _) => None,
            };
            self.known_objs_equal_to_finite_seq_list
                .insert(name, (list, merged_member, line_file));
        }

        for (name, (matrix, member_of, line_file)) in known_objs_equal_to_matrix_list {
            let old = self.known_objs_equal_to_matrix_list.get(&name).cloned();
            let merged_member = match (member_of, old.as_ref()) {
                (Some(new_member), _) => Some(new_member),
                (None, Some((_, Some(old_member), _))) => Some(old_member.clone()),
                (None, _) => None,
            };
            self.known_objs_equal_to_matrix_list
                .insert(name, (matrix, merged_member, line_file));
        }

        for (name, value) in known_obj_values {
            self.known_obj_values.insert(name, value);
        }

        for (name, value) in known_objs_equal_to_set_builder {
            self.known_objs_equal_to_set_builder.insert(name, value);
        }

        for (name, child_info) in known_objs_in_fn_sets {
            merge_known_fn_info_map_entry(&mut self.known_objs_in_fn_sets, name, child_info);
        }

        for (name, _) in known_transitive_props {
            self.known_transitive_props.insert(name, ());
        }
        for (name, permutations) in known_symmetric_props {
            for permutation in permutations {
                self.store_symmetric_prop_permutation(
                    name.clone(),
                    permutation,
                    default_line_file(),
                )?;
            }
        }
        for (name, _) in known_reflexive_props {
            self.known_reflexive_props.insert(name, ());
        }
        for (name, _) in known_antisymmetric_props {
            self.known_antisymmetric_props.insert(name, ());
        }

        for (key, _) in cache_well_defined_obj {
            self.cache_well_defined_obj.insert(key, ());
        }
        for (key, line_file) in cache_known_fact {
            self.cache_known_fact.insert(key, line_file);
        }
        for (key, summary) in cache_known_fact_trust {
            self.cache_known_fact_trust.insert(key, summary);
        }

        for (key, strategy_name) in used_strategy_stmts {
            self.used_strategy_stmts
                .insert(key.clone(), strategy_name.clone());
            self.stopped_strategy_stmts.remove(&key);
        }
        for (key, strategy_name) in stopped_strategy_stmts {
            self.stopped_strategy_stmts.insert(key, strategy_name);
        }
        Ok(())
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
    parent: &mut Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
    child: Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
) {
    let mut seen = HashSet::new();
    for (fact, params_and_dom) in parent.iter() {
        seen.insert(forall_pair_key(fact.to_string(), params_and_dom));
    }
    for (fact, params_and_dom) in child {
        if seen.insert(forall_pair_key(fact.to_string(), &params_and_dom)) {
            parent.push((fact, params_and_dom));
        }
    }
}

fn append_missing_exist_forall_pairs(
    parent: &mut Vec<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)>,
    child: Vec<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)>,
) {
    let mut seen = HashSet::new();
    for (fact, params_and_dom) in parent.iter() {
        seen.insert(forall_pair_key(fact.to_string(), params_and_dom));
    }
    for (fact, params_and_dom) in child {
        if seen.insert(forall_pair_key(fact.to_string(), &params_and_dom)) {
            parent.push((fact, params_and_dom));
        }
    }
}

fn append_missing_and_forall_pairs(
    parent: &mut Vec<(AndFact, Rc<KnownForallFactParamsAndDom>)>,
    child: Vec<(AndFact, Rc<KnownForallFactParamsAndDom>)>,
) {
    let mut seen = HashSet::new();
    for (fact, params_and_dom) in parent.iter() {
        seen.insert(forall_pair_key(fact.to_string(), params_and_dom));
    }
    for (fact, params_and_dom) in child {
        if seen.insert(forall_pair_key(fact.to_string(), &params_and_dom)) {
            parent.push((fact, params_and_dom));
        }
    }
}

fn append_missing_or_forall_pairs(
    parent: &mut Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
    child: Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
) {
    let mut seen = HashSet::new();
    for (fact, params_and_dom) in parent.iter() {
        seen.insert(forall_pair_key(fact.to_string(), params_and_dom));
    }
    for (fact, params_and_dom) in child {
        if seen.insert(forall_pair_key(fact.to_string(), &params_and_dom)) {
            parent.push((fact, params_and_dom));
        }
    }
}

fn forall_pair_key(fact_key: String, params_and_dom: &KnownForallFactParamsAndDom) -> String {
    let mut key = format!("{}|{}", fact_key, params_and_dom.params_def);
    for fact in params_and_dom.dom.iter() {
        key.push('|');
        key.push_str(&fact.to_string());
    }
    key
}

fn merge_known_fn_info_map_entry(
    map: &mut std::collections::HashMap<ObjString, KnownFnInfo>,
    name: ObjString,
    child_info: KnownFnInfo,
) {
    let parent_info = map.entry(name).or_default();
    if let Some(fn_set) = child_info.fn_set {
        parent_info.fn_set = Some(fn_set);
    }
    if let Some(equal_to) = child_info.equal_to {
        parent_info.equal_to = Some(equal_to);
    }
    if let Some(child_restricts) = child_info.restrict_to {
        let parent_restricts = parent_info.restrict_to.get_or_insert_with(Vec::new);
        let mut seen = HashSet::new();
        for (body, _) in parent_restricts.iter() {
            seen.insert(body.to_string());
        }
        for (body, line_file) in child_restricts {
            if seen.insert(body.to_string()) {
                parent_restricts.push((body, line_file));
            }
        }
    }
}
