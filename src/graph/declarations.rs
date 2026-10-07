//! Accepted declarations are mathematical nodes; command applications are not.
use super::helper::source_path;
use super::math_graph::{MathGraph, MathNode};
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::DefinitionStmt;
use crate::exec_env::{ExecEnv, StoredIdentifierDefinition};
use crate::runtime::Runtime;

impl MathGraph {
    pub(super) fn declare(&mut self, scope: &str, form: &str, name: &str, statement: String, line: usize, source: String, origin: &str, published: bool) -> String {
        let key = (scope.into(), form.into(), name.into());
        if let Some(id) = self.declaration_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("declaration:{}", self.declaration_nodes.len());
        let kind = if form == "thm" || form == "axiom" { "thm" } else { "definition" };
        let mut node = MathNode::new(id.clone(), kind, name.into(), source, scope.into(), origin);
        node.name = Some(name.into());
        node.statement = statement;
        node.line = Some(line);
        node.published = published;
        node.history_available = origin != "external";
        let id = self.add_node(node);
        self.declaration_nodes.insert(key, id.clone());
        id
    }

    pub(super) fn env_source(&self, env: &ExecEnv, runtime: &Runtime) -> String {
        if let Some(view) = &env.session_view {
            let line = SourceLine::new(0, view.code_source.clone());
            source_path(&line, runtime, &self.current_source)
        } else {
            self.current_source.clone()
        }
    }

    pub(super) fn register_declarations(&mut self, env: &ExecEnv, runtime: &Runtime, local: bool, history_available: bool) {
        let scope = self.scope(env, local);
        if !self.registered_scopes.insert(scope.clone()) {
            return;
        }
        let memory = &env.definitions;
        let mut statements: Vec<DefinitionStmt> = Vec::new();
        for def in memory.predicate_definitions.values() { statements.push(DefinitionStmt::DefPropStmt(def.clone())); }
        for def in memory.abstract_predicate_definitions.values() { statements.push(DefinitionStmt::DefAbstractPropStmt(def.clone())); }
        for def in memory.structure_definitions.values() { statements.push(DefinitionStmt::DefStructStmt(def.clone())); }
        for def in memory.template_definitions.values() { statements.push(DefinitionStmt::DefTemplateStmt(def.clone())); }
        for def in memory.theorem_definitions.values() { statements.push(DefinitionStmt::DefThmStmt(def.clone())); }
        for def in memory.axiom_definitions.values() { statements.push(DefinitionStmt::AxiomStmt(def.clone())); }
        for def in memory.strategy_definitions.values() { statements.push(DefinitionStmt::DefStrategyStmt(def.clone())); }
        for def in memory.algorithm_definitions.values() {
            match def {
                crate::exec_env::StoredDefAlgo::ByCases(s) => statements.push(DefinitionStmt::DefAlgoByCasesStmt(s.clone())),
                crate::exec_env::StoredDefAlgo::ByInduc(s) => statements.push(DefinitionStmt::DefAlgoByInducStmt(s.clone())),
            }
        }
        statements.sort_by_key(|stmt| declaration_header(stmt).map(|(_, name, line, _)| (line.line, name.clone())));
        let mut declared = Vec::new();
        for stmt in &statements {
            if let Some((form, name, line, text)) = declaration_header(stmt) {
                let source = source_path(line, runtime, &self.current_source);
                let origin = if form == "axiom" { "axiom" } else if !history_available { "external" } else if form == "thm" { "verified" } else { "definition" };
                let id = self.declare(&scope, form, name, text, line.line, source, origin, !local);
                if let DefinitionStmt::DefThmStmt(thm) = stmt {
                    self.fact_nodes.insert(thm.fact.fact_id(), id.clone());
                }
                if let DefinitionStmt::AxiomStmt(axiom) = stmt {
                    self.fact_nodes.insert(axiom.forall_fact.fact_id, id.clone());
                }
                declared.push((id, stmt));
            }
        }
        let saved_statement = self.current_statement.clone();
        let mut objects = memory.identifiers.values().collect::<Vec<_>>();
        objects.sort_by_key(|value| identifier_description(value).map(|(name, _, line)| (line.line, name)));
        for value in objects {
            if let Some((name, text, line)) = identifier_description(value) {
                let source = source_path(&line, runtime, &self.current_source);
                let origin = if matches!(value, StoredIdentifierDefinition::TrustHave(_)) { "trusted" } else if history_available { "definition" } else { "external" };
                self.current_statement = text.clone();
                let id = self.declare(&scope, "object", &name, text, line.line, source, origin, !local);
                let mut refs = Vec::new();
                let locals: Vec<&ExecEnv> = if local { vec![env] } else { Vec::new() };
                super::walk_generated::walk_stored_identifier_definition(value, self, runtime, &locals, &mut refs, &mut Vec::new());
                for reference in refs { self.edge(&reference.id, &id, "definition_reference"); }
            }
        }
        for (id, stmt) in declared {
            self.current_statement = self.nodes[self.node_index[&id]].statement.clone();
            let mut refs = Vec::new();
            let mut outputs = Vec::new();
            let locals: Vec<&ExecEnv> = if local { vec![env] } else { Vec::new() };
            match stmt {
                DefinitionStmt::DefPropStmt(s) => super::walk_generated::walk_def_prop_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefAbstractPropStmt(s) => super::walk_generated::walk_def_abstract_prop_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefStructStmt(s) => super::walk_generated::walk_def_struct_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefTemplateStmt(s) => super::walk_generated::walk_def_template_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefThmStmt(s) => super::walk_generated::walk_def_thm_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::AxiomStmt(s) => super::walk_generated::walk_axiom_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefStrategyStmt(s) => super::walk_generated::walk_def_strategy_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefAlgoByCasesStmt(s) => super::walk_generated::walk_def_algo_by_cases_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefAlgoByInducStmt(s) => super::walk_generated::walk_def_algo_by_induc_stmt(s, self, runtime, &locals, &mut refs, &mut outputs),
                DefinitionStmt::DefineObj(_) | DefinitionStmt::HaveFnEqualStmt(_) | DefinitionStmt::HaveFnEqualCaseByCaseStmt(_) | DefinitionStmt::HaveFnByInducStmt(_) | DefinitionStmt::HaveFnByForallExistUniqueStmt(_) => {}
            }
            for reference in refs { self.edge(&reference.id, &id, "definition_reference"); }
        }
        self.current_statement = saved_statement;
    }
}

fn declaration_header(stmt: &DefinitionStmt) -> Option<(&str, &String, &SourceLine, String)> {
    match stmt {
        DefinitionStmt::DefPropStmt(s) => Some(("prop", &s.name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefAbstractPropStmt(s) => Some(("abstract_prop", &s.name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefStructStmt(s) => Some(("struct", &s.name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefTemplateStmt(s) => Some(("template", &s.template_name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefThmStmt(s) => Some(("thm", &s.name, &s.line_file, format!("thm {}:\n    ? {}", s.name, s.fact.readable_string()))),
        DefinitionStmt::AxiomStmt(s) => Some(("axiom", &s.name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefStrategyStmt(s) => Some(("strategy", &s.name, &s.line_file, format!("strategy {}:\n    ? {}", s.name, crate::ast::fact::Fact::ForallFact(s.forall_fact.clone()).readable_string()))),
        DefinitionStmt::DefAlgoByCasesStmt(s) => Some(("algo", &s.name.name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefAlgoByInducStmt(s) => Some(("algo", &s.name.name, &s.line_file, s.readable_string())),
        DefinitionStmt::DefineObj(_) | DefinitionStmt::HaveFnEqualStmt(_) | DefinitionStmt::HaveFnEqualCaseByCaseStmt(_) | DefinitionStmt::HaveFnByInducStmt(_) | DefinitionStmt::HaveFnByForallExistUniqueStmt(_) => None,
    }
}

pub(super) fn identifier_description(definition: &StoredIdentifierDefinition) -> Option<(String, String, SourceLine)> {
    let (name, text, line) = match definition {
        StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveObjEqual((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveObjByExistFacts((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::TrustHave((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveByReplacementAxiom((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::LetObj((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveFnEqual((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveFnEqualCaseByCase((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveFnByForallExistUnique((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::HaveFnByInduc((n, s)) => (n, s.readable_string(), &s.line_file),
        StoredIdentifierDefinition::ParamType(_) => return None,
    };
    Some((name.clone(), text, line.clone()))
}

pub(super) fn identifier_binding_id(definition: &StoredIdentifierDefinition, name: &str) -> Option<crate::runtime::IdentifierId> {
    let params = match definition {
        StoredIdentifierDefinition::ParamType((bound, _)) => return Some(bound.id),
        StoredIdentifierDefinition::LetObj((_, s)) => return Some(s.name.id),
        StoredIdentifierDefinition::HaveFnEqual((_, s)) => return Some(s.name.id),
        StoredIdentifierDefinition::HaveByReplacementAxiom((_, s)) => return Some(s.name.id),
        StoredIdentifierDefinition::HaveObjEqual((_, s)) => &s.param_def,
        StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((_, s)) => &s.param_def,
        StoredIdentifierDefinition::HaveObjByExistFacts((_, s)) => &s.param_def,
        StoredIdentifierDefinition::TrustHave((_, s)) => &s.param_def,
        StoredIdentifierDefinition::HaveFnEqualCaseByCase((_, s)) => return Some(s.name.id),
        StoredIdentifierDefinition::HaveFnByForallExistUnique((_, s)) => return Some(s.name.id),
        StoredIdentifierDefinition::HaveFnByInduc((_, s)) => return Some(s.name.id),
    };
    for group in &params.groups {
        for parameter in &group.params {
            if parameter.name == name { return Some(parameter.id); }
        }
    }
    None
}
