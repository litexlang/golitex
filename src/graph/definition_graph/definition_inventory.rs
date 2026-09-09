//! Identifiers, propositions, functions, algorithms, structures, templates, theorems, and strategies.

use super::*;

impl DefinitionGraphBuilder {
    pub(super) fn add_identifiers(&mut self, environment: &ExecEnv) {
        let mut identifiers = environment.definitions.object_symbols().collect::<Vec<_>>();
        identifiers.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in identifiers {
            self.ensure_node(
                definition_id("identifier", name),
                "identifier",
                "identifier",
                name,
                true,
                None,
                Some(&format!(
                    "identifier {}: {}",
                    name,
                    definition.role().description()
                )),
            );
        }
    }

    pub(super) fn add_props(&mut self, environment: &ExecEnv) {
        let mut abstract_props = environment
            .definitions
            .abstract_predicate_definitions
            .iter()
            .collect::<Vec<_>>();
        abstract_props.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in abstract_props {
            self.ensure_node(
                definition_id("prop", name),
                "prop",
                "abstract_prop",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
        }

        let mut props = environment
            .definitions
            .predicate_definitions
            .iter()
            .collect::<Vec<_>>();
        props.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in props {
            let node_id = definition_id("prop", name);
            self.ensure_node(
                node_id.clone(),
                "prop",
                "prop",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut signature = DepCollector::new();
            signature.collect_param_def_with_type_deps(&definition.typed_parameters);
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut definition_body = DepCollector::new();
            definition_body.add_param_def_with_type(&definition.typed_parameters);
            for fact in &definition.iff_facts {
                definition_body.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
        }
    }

    pub(super) fn add_functions(&mut self, environment: &ExecEnv) {
        let mut functions = environment
            .objects
            .knowledge_by_object
            .iter()
            .filter_map(|(name, knowledge)| {
                knowledge
                    .function_set
                    .as_ref()
                    .map(|definition| (name, definition))
            })
            .collect::<Vec<_>>();
        functions.sort_by(|left, right| left.0.cmp(right.0));
        for (stored_name, definition) in functions {
            let display_name = strip_free_param_numeric_tags_in_display(stored_name);
            let name = self.normalized_dependency_name(&display_name);
            let node_id = definition_id("fn", name.as_str());
            let line_file = definition
                .equal_to
                .as_ref()
                .map(|(_, line_file)| line_file)
                .or_else(|| definition.fn_set.as_ref().map(|(_, line_file)| line_file));
            self.ensure_node(
                node_id.clone(),
                "fn",
                "function",
                name.as_str(),
                true,
                line_file,
                Some(&format!("have fn {}", name)),
            );
            let mut signature = DepCollector::new();
            signature.add_local_name(name.as_str());
            let mut well_definedness = DepCollector::new();
            well_definedness.add_local_name(name.as_str());
            if let Some((fn_set, _)) = definition.fn_set.as_ref() {
                signature.collect_param_def_with_set_deps(&fn_set.set_bound_parameters);
                signature.add_param_def_with_set(&fn_set.set_bound_parameters);
                signature.collect_obj(&fn_set.ret_set);

                well_definedness.add_param_def_with_set(&fn_set.set_bound_parameters);
                for fact in fn_set.dom_facts.iter() {
                    well_definedness.collect_quantifier_free_fact(fact);
                }
            }
            self.add_dependency_edges(&node_id, signature, "signature");
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            let mut definition_body = DepCollector::new();
            definition_body.add_local_name(name.as_str());
            if let Some((equal_to, _)) = definition.equal_to.as_ref() {
                definition_body.collect_obj(equal_to);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
        }
    }

    pub(super) fn add_algorithms(&mut self, environment: &ExecEnv) {
        let mut algorithms = environment
            .definitions
            .algorithm_definitions
            .iter()
            .collect::<Vec<_>>();
        algorithms.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in algorithms {
            let node_id = definition_id("algorithm", name);
            self.ensure_node(
                node_id.clone(),
                "algorithm",
                "algorithm",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut definition_body = DepCollector::new();
            for parameter in &definition.param_bindings {
                definition_body.add_local_name(parameter.name());
            }
            for case in &definition.cases {
                definition_body.collect_atomic_fact(&case.condition);
                definition_body.collect_obj(&case.return_stmt.value);
            }
            if let Some(default_return) = definition.default_return.as_ref() {
                definition_body.collect_obj(&default_return.value);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
        }
    }

    pub(super) fn add_structs(&mut self, environment: &ExecEnv) {
        let mut structs = environment
            .definitions
            .structure_definitions
            .iter()
            .collect::<Vec<_>>();
        structs.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in structs {
            let node_id = definition_id("struct", name);
            self.ensure_node(
                node_id.clone(),
                "struct",
                "structure",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut signature = DepCollector::new();
            let mut well_definedness = DepCollector::new();
            if let Some((params, dom_facts)) = definition.param_def_with_dom.as_ref() {
                signature.collect_param_def_with_type_deps(params);
                signature.add_param_def_with_type(params);
                well_definedness.add_param_def_with_type(params);
                for fact in dom_facts {
                    well_definedness.collect_quantifier_free_fact(fact);
                }
            }
            for field in &definition.fields {
                signature.collect_obj(&field.field_type);
            }
            self.add_dependency_edges(&node_id, signature, "signature");
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            let mut definition_body = DepCollector::new();
            if let Some((params, _)) = definition.param_def_with_dom.as_ref() {
                definition_body.add_param_def_with_type(params);
            }
            for fact in &definition.equivalent_facts {
                definition_body.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, definition_body, "definition");
        }
    }

    pub(super) fn add_templates(&mut self, environment: &ExecEnv) {
        let mut templates = environment
            .definitions
            .template_definitions
            .iter()
            .collect::<Vec<_>>();
        templates.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in templates {
            let node_id = definition_id("template", name);
            self.ensure_node(
                node_id.clone(),
                "template",
                "template",
                name,
                true,
                Some(&definition.line_file),
                Some(&format!("template {}", name)),
            );
            let mut signature = DepCollector::new();
            signature.collect_param_def_with_type_deps(&definition.template_arg_def);
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            well_definedness.add_param_def_with_type(&definition.template_arg_def);
            for fact in &definition.template_arg_dom {
                well_definedness.collect_quantifier_free_fact(fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");

            let mut definition_body = DepCollector::new();
            definition_body.add_param_def_with_type(&definition.template_arg_def);
            collect_template_definition_dependencies(
                &mut definition_body,
                &definition.template_def_stmt,
            );
            self.add_dependency_edges(&node_id, definition_body, "definition");
        }
    }

    pub(super) fn add_theorems(&mut self, environment: &ExecEnv) {
        let mut theorems = environment
            .definitions
            .theorem_definitions
            .iter()
            .collect::<Vec<_>>();
        theorems.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in theorems {
            let node_id = definition_id("theorem", name);
            self.ensure_node(
                node_id.clone(),
                "theorem",
                "theorem",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut signature = DepCollector::new();
            if let Fact::ForallFact(forall_fact) = &definition.fact {
                signature.collect_param_def_with_type_deps(&forall_fact.typed_parameters);
                signature.add_param_def_with_type(&forall_fact.typed_parameters);
                for fact in forall_fact.then_facts.iter() {
                    signature.collect_exist_or_and_chain_atomic_fact(fact);
                }
            } else {
                signature.collect_fact(&definition.fact);
            }
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            if let Fact::ForallFact(forall_fact) = &definition.fact {
                well_definedness.add_param_def_with_type(&forall_fact.typed_parameters);
                for fact in forall_fact.dom_facts.iter() {
                    well_definedness.collect_fact(fact);
                }
            } else {
                well_definedness.collect_fact(&definition.fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");
        }

        let mut axioms = environment
            .definitions
            .axiom_definitions
            .iter()
            .collect::<Vec<_>>();
        axioms.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in axioms {
            let node_id = definition_id("theorem", name);
            self.ensure_node(
                node_id.clone(),
                "theorem",
                "axiom",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut signature = DepCollector::new();
            signature.collect_param_def_with_type_deps(&definition.forall_fact.typed_parameters);
            signature.add_param_def_with_type(&definition.forall_fact.typed_parameters);
            for fact in definition.forall_fact.then_facts.iter() {
                signature.collect_exist_or_and_chain_atomic_fact(fact);
            }
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            well_definedness.add_param_def_with_type(&definition.forall_fact.typed_parameters);
            for fact in definition.forall_fact.dom_facts.iter() {
                well_definedness.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");
        }
    }

    pub(super) fn add_strategies(&mut self, environment: &ExecEnv) {
        let mut strategies = environment
            .definitions
            .strategy_definitions
            .iter()
            .collect::<Vec<_>>();
        strategies.sort_by(|left, right| left.0.cmp(right.0));
        for (name, definition) in strategies {
            let node_id = definition_id("strategy", name);
            self.ensure_node(
                node_id.clone(),
                "strategy",
                "strategy",
                name,
                true,
                Some(&definition.line_file),
                Some(&definition.to_string()),
            );
            let mut signature = DepCollector::new();
            signature.collect_param_def_with_type_deps(&definition.forall_fact.typed_parameters);
            signature.add_param_def_with_type(&definition.forall_fact.typed_parameters);
            for fact in definition.forall_fact.then_facts.iter() {
                signature.collect_exist_or_and_chain_atomic_fact(fact);
            }
            self.add_dependency_edges(&node_id, signature, "signature");

            let mut well_definedness = DepCollector::new();
            well_definedness.add_param_def_with_type(&definition.forall_fact.typed_parameters);
            for fact in definition.forall_fact.dom_facts.iter() {
                well_definedness.collect_fact(fact);
            }
            self.add_dependency_edges(&node_id, well_definedness, "well_definedness");
        }
    }
}
