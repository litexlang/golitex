//! Export-time mathematical entities. This never owns or mutates verifier state.
use crate::knowledge_base::JsonValue;
use std::collections::{HashMap, HashSet};

pub struct MathGraph {
    pub(super) nodes: Vec<MathNode>,
    pub(super) edges: Vec<MathEdge>,
    pub(super) node_index: HashMap<String, usize>,
    pub(super) fact_nodes: HashMap<crate::runtime::FactId, String>,
    pub(super) declaration_nodes: HashMap<(String, String, String), String>,
    pub(super) scopes: HashMap<(String, usize), String>,
    pub(super) registered_scopes: HashSet<String>,
    pub(super) diagnostics: Vec<JsonValue>,
    pub(super) current_source: String,
    pub(super) current_owner: String,
    pub(super) current_statement: String,
    pub(super) current_origin: String,
    pub(super) current_group: usize,
    pub(super) next_group: usize,
    pub(super) language: crate::launch_command::OutputLanguage,
}

pub(super) struct MathNode {
    pub id: String,
    pub kind: String,
    pub name: Option<String>,
    pub label: String,
    pub statement: String,
    pub source: String,
    pub line: Option<usize>,
    pub scope: String,
    pub origin: String,
    pub inferred: bool,
    pub published: bool,
    pub history_available: bool,
}

pub(super) struct MathEdge {
    pub from: String,
    pub to: String,
    pub kind: String,
    pub group: usize,
    pub statement: String,
    pub source: String,
}

pub(super) struct GraphReference {
    pub id: String,
    pub kind: String,
}

impl GraphReference {
    pub fn new(id: String, kind: &str) -> Self {
        Self { id, kind: kind.into() }
    }
}

impl MathNode {
    pub fn new(id: String, kind: &str, label: String, source: String, scope: String, origin: &str) -> Self {
        Self {
            id, kind: kind.into(), name: None, statement: label.clone(), label,
            source, scope, origin: origin.into(), line: None, inferred: false,
            published: false, history_available: false,
        }
    }
}

impl MathGraph {
    pub fn new(language: crate::launch_command::OutputLanguage) -> Self {
        Self {
            nodes: Vec::new(), edges: Vec::new(), node_index: HashMap::new(),
            fact_nodes: HashMap::new(), declaration_nodes: HashMap::new(),
            scopes: HashMap::new(), registered_scopes: HashSet::new(),
            diagnostics: Vec::new(), current_source: String::new(),
            current_owner: String::new(),
            current_statement: String::new(), current_origin: "verified".into(),
            current_group: 0, next_group: 1, language,
        }
    }

    pub(super) fn add_node(&mut self, node: MathNode) -> String {
        let id = node.id.clone();
        if !self.node_index.contains_key(&id) {
            self.node_index.insert(id.clone(), self.nodes.len());
            self.nodes.push(node);
        }
        id
    }

    pub(super) fn edge(&mut self, from: &str, to: &str, kind: &str) {
        if from == to || self.edges.iter().any(|e| e.from == from && e.to == to && e.kind == kind && e.group == self.current_group) {
            return;
        }
        self.edges.push(MathEdge {
            from: from.into(), to: to.into(), kind: kind.into(),
            group: self.current_group, statement: self.current_statement.clone(),
            source: self.current_source.clone(),
        });
    }

    pub(super) fn scope(&mut self, env: &crate::exec_env::ExecEnv, local: bool) -> String {
        let owner = if local {
            self.current_owner.clone()
        } else {
            super::helper::file_scope(env.session_view.as_ref().map(|view| &view.code_source).unwrap_or(&crate::runtime::CodeSource::StandaloneFile), &self.current_source)
        };
        let key = (owner.clone(), env as *const _ as usize);
        if let Some(scope) = self.scopes.get(&key) {
            return scope.clone();
        }
        let scope = if local {
            format!("local:{}", self.scopes.len())
        } else {
            owner
        };
        self.scopes.insert(key, scope.clone());
        scope
    }

    pub fn diagnostic(&mut self, message: String) {
        self.diagnostics.push(super::helper::object(vec![
            ("source", super::helper::string(&self.current_source)),
            ("statement", super::helper::string(&self.current_statement)),
            ("message", super::helper::string(message)),
        ]));
    }
}
