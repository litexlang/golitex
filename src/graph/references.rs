use super::math_graph::{GraphReference, MathGraph, MathNode};
use super::helper::{fact_line, source_path};
use crate::ast::fact::Fact;
use crate::ast::names::AtomicName;
use crate::ast::obj::IdentifierObj;
use crate::exec_env::ExecEnv;
use crate::runtime::{FactId, Runtime};
use crate::store_fact_and_infer::StoreFactAndInferResult;

impl MathGraph {
    pub(super) fn reference_fact(&mut self, id: &FactId, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, _: &mut Vec<String>) {
        if let Some(node) = self.fact_node(*id, runtime, locals) {
            refs.push(GraphReference::new(node, "depends_on"));
        } else {
            // Unstored certificate subjects have IDs too; only real stored
            // sources may become cited fact nodes.
        }
    }

    pub(super) fn fact_node(&mut self, id: FactId, runtime: &Runtime, locals: &[&ExecEnv]) -> Option<String> {
        if let Some(node) = self.fact_nodes.get(&id) {
            return Some(node.clone());
        }
        for env in locals.iter().rev() {
            if let Some(fact) = env.facts.facts_by_id.get(&id) {
                let scope = self.scope(env, true);
                return Some(self.insert_fact(fact, runtime, scope, "local"));
            }
        }
        for env in runtime.execution_environments_stack.iter().rev() {
            if let Some(fact) = env.facts.facts_by_id.get(&id) {
                let scope = self.scope(env, false);
                return Some(self.insert_fact(fact, runtime, scope, "external"));
            }
        }
        for export in runtime.global_module_manager.root_exports() {
            if let Some(fact) = export.exec_env.facts.facts_by_id.get(&id) {
                let source = self.current_source.clone();
                self.current_source = export.path.display().to_string();
                let scope = self.scope(&export.exec_env, false);
                let node = self.insert_fact(fact, runtime, scope, "external");
                self.current_source = source;
                return Some(node);
            }
        }
        for module in runtime.global_module_manager.imports() {
            for export in &module.export_files_and_their_env {
                if let Some(fact) = export.exec_env.facts.facts_by_id.get(&id) {
                    let source = self.current_source.clone();
                    self.current_source = export.path.display().to_string();
                    let scope = self.scope(&export.exec_env, false);
                    let node = self.insert_fact(fact, runtime, scope, "external");
                    self.current_source = source;
                    return Some(node);
                }
            }
        }
        None
    }

    fn insert_fact(&mut self, fact: &Fact, runtime: &Runtime, scope: String, origin: &str) -> String {
        let id = format!("fact:{}", fact.fact_id());
        let line = fact_line(fact);
        let source = line.map(|line| source_path(line, runtime, &self.current_source)).unwrap_or_else(|| self.current_source.clone());
        let mut node = MathNode::new(id.clone(), "fact", fact.readable_string(), source, scope, origin);
        node.line = line.map(|line| line.line);
        node.published = !node.scope.starts_with("local:");
        let id = self.add_node(node);
        self.fact_nodes.insert(fact.fact_id(), id.clone());
        id
    }

    pub(super) fn collect_store(&mut self, stored: &StoreFactAndInferResult, runtime: &Runtime, locals: &[&ExecEnv], _: &mut Vec<GraphReference>, outputs: &mut Vec<String>) {
        let mut direct = Vec::new();
        self.collect_stored_ids(&stored.store.stored_fact_ids(), runtime, locals, &mut Vec::new(), &mut direct);
        outputs.extend(direct.iter().cloned());
        let mut infer_refs = Vec::new();
        let mut infer_outputs = Vec::new();
        super::walk_generated::walk_infer_fact_result(&stored.infer, self, runtime, locals, &mut infer_refs, &mut infer_outputs);
        for id in stored.infer.stored_fact_ids() {
            if let Some(node) = self.fact_node(id, runtime, locals) {
                if let Some(index) = self.node_index.get(&node).copied() {
                    self.nodes[index].inferred = true;
                    self.nodes[index].origin = if self.nodes[index].scope.starts_with("local:") && self.current_origin == "verified" { "local".into() } else { self.current_origin.clone() };
                    self.nodes[index].published = !self.nodes[index].scope.starts_with("local:");
                    self.nodes[index].history_available = true;
                }
                for source in &direct {
                    self.edge(source, &node, "inferred_from");
                }
                for reference in &infer_refs {
                    self.edge(&reference.id, &node, "inferred_from");
                }
            }
        }
    }

    pub(super) fn collect_stored_ids(&mut self, ids: &[FactId], runtime: &Runtime, locals: &[&ExecEnv], _: &mut Vec<GraphReference>, outputs: &mut Vec<String>) {
        for id in ids {
            if let Some(node) = self.fact_node(*id, runtime, locals) {
                if let Some(index) = self.node_index.get(&node).copied() {
                    if self.nodes[index].kind == "fact" {
                        self.nodes[index].origin = if self.nodes[index].scope.starts_with("local:") && self.current_origin == "verified" { "local".into() } else { self.current_origin.clone() };
                    }
                    self.nodes[index].published = !self.nodes[index].scope.starts_with("local:");
                    self.nodes[index].history_available = true;
                }
                if !outputs.contains(&node) {
                    outputs.push(node);
                }
            }
        }
    }

    pub(super) fn collect_assumption(&mut self, value: &crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult, runtime: &Runtime, locals: &[&ExecEnv], _: &mut Vec<GraphReference>, _: &mut Vec<String>) {
        let origin = self.current_origin.clone();
        self.current_origin = "assumption".into();
        self.collect_store(&value.store_and_infer, runtime, locals, &mut Vec::new(), &mut Vec::new());
        self.current_origin = origin;
    }

    pub(super) fn collect_bound_parameters(&mut self, ids: &[FactId], runtime: &Runtime, locals: &[&ExecEnv]) {
        let origin = self.current_origin.clone();
        self.current_origin = "assumption".into();
        self.collect_stored_ids(ids, runtime, locals, &mut Vec::new(), &mut Vec::new());
        self.current_origin = origin;
    }

    pub(super) fn reference_builtin_theorem(&mut self, value: &crate::execute::execute_by_stmt::BuiltinThmApplication, refs: &mut Vec<GraphReference>) {
        use crate::builtin_theorem::BuiltinTheoremId;
        let name = value.theorem.as_str();
                let origin = match value.theorem {
            BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily | BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromPointwise => "foundation",
            _ => "builtin",
        };
        let id = self.declare("builtin", "thm", name, format!("Builtin theorem: {name}"), 0, "<builtin>".into(), origin, true);
        refs.push(GraphReference::new(id, "theorem_instance"));
    }

    pub(super) fn reference_name(&mut self, name: &AtomicName, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, _: &mut Vec<String>) {
        self.reference_name_forms(name, runtime, locals, refs, &["prop", "abstract_prop"]);
    }

    pub(super) fn reference_struct_name(&mut self, name: &AtomicName, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, _: &mut Vec<String>) {
        self.reference_name_forms(name, runtime, locals, refs, &["struct"]);
    }

    pub(super) fn reference_template_name(&mut self, name: &AtomicName, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, _: &mut Vec<String>) {
        self.reference_name_forms(name, runtime, locals, refs, &["template"]);
    }

    fn reference_name_forms(&mut self, name: &AtomicName, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, forms: &[&str]) {
        let env = match name {
            AtomicName::Plain { .. } => None,
            AtomicName::WithExportFileId { export_file_id, .. } => runtime.finished_export_exec_env(None, *export_file_id),
            AtomicName::WithModAndExportFileId { global_mod_id, export_file_id, .. } => runtime.finished_export_exec_env(Some(*global_mod_id), *export_file_id),
        };
        let live = match name {
            AtomicName::Plain { .. } => true,
            AtomicName::WithExportFileId { export_file_id, .. } => runtime.code_source.is_live_root_export(*export_file_id),
            AtomicName::WithModAndExportFileId { global_mod_id, export_file_id, .. } => runtime.code_source.is_live_imported_export(*global_mod_id, *export_file_id),
        };
        if let Some(env) = env {
            let source = self.current_source.clone();
            self.current_source = self.env_source(env, runtime);
            self.register_declarations(env, runtime, false, false);
            let scope = self.scope(env, false);
            self.add_declaration_references(&scope, name.local_name(), refs, forms);
            self.current_source = source;
            return;
        }
        if !live { return; }
        // Plain references inside a retained proof scope resolve inner-first.
        for env in locals.iter().rev() {
            self.register_declarations(env, runtime, true, true);
            let scope = self.scope(env, true);
            if self.add_declaration_references(&scope, name.local_name(), refs, forms) {
                return;
            }
        }
        for env in runtime.execution_environments_stack.iter().rev() {
            self.register_declarations(env, runtime, false, true);
            let scope = self.scope(env, false);
            if self.add_declaration_references(&scope, name.local_name(), refs, forms) {
                return;
            }
        }
    }

    fn add_declaration_references(&self, scope: &str, name: &str, refs: &mut Vec<GraphReference>, forms: &[&str]) -> bool {
        let mut found = false;
        for kind in forms {
            if let Some(id) = self.declaration_nodes.get(&(scope.into(), (*kind).into(), name.into())) {
                refs.push(GraphReference::new(id.clone(), "uses_definition"));
                found = true;
            }
        }
        found
    }

    pub(super) fn reference_identifier(&mut self, name: &IdentifierObj, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>, _: &mut Vec<String>) {
        if let IdentifierObj::Plain { id, name } = name {
            for env in locals.iter().rev() {
                if let Some(definition) = env.definitions.identifiers.get(name) {
                    if super::declarations::identifier_binding_id(definition, name) == Some(*id) {
                        if let Some((label, statement, line)) = super::declarations::identifier_description(definition) {
                            let scope = self.scope(env, true);
                            let source = source_path(&line, runtime, &self.current_source);
                            let origin = if matches!(definition, crate::exec_env::StoredIdentifierDefinition::TrustHave(_)) { "trusted" } else { "definition" };
                            let node = self.declare(&scope, "object", &label, statement, line.line, source, origin, false);
                            refs.push(GraphReference::new(node, "uses_definition"));
                        }
                        return;
                    }
                }
            }
        }
        if let Some(definition) = runtime.stored_identifier_definition_visible(name) {
            if let Some((label, statement, line)) = super::declarations::identifier_description(definition) {
                let source = source_path(&line, runtime, &self.current_source);
                let scope = super::helper::file_scope(&line.origin, &source);
                let origin = if matches!(definition, crate::exec_env::StoredIdentifierDefinition::TrustHave(_)) { "trusted" } else if source == self.current_source { "definition" } else { "external" };
                let id = self.declare(&scope, "object", &label, statement, line.line, source, origin, false);
                refs.push(GraphReference::new(id, "uses_definition"));
            }
        }
    }

    pub(super) fn reference_theorem_call(&mut self, call: &crate::ast::stmt::TheoremCall, runtime: &Runtime, locals: &[&ExecEnv], refs: &mut Vec<GraphReference>) {
        let mut found = Vec::new();
        self.reference_name_forms(&call.name, runtime, locals, &mut found, &["thm", "axiom"]);
        for reference in found {
            refs.push(GraphReference::new(reference.id, "theorem_instance"));
        }
        if let crate::ast::stmt::TheoremCallArguments::Parenthesized(args) = &call.arguments {
            for arg in args {
                super::walk_generated::walk_obj(arg, self, runtime, locals, refs, &mut Vec::new());
            }
        }
    }
}
