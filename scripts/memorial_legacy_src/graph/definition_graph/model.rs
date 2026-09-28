//! Definition graph nodes, edges, and builder state.

use super::*;

pub(super) struct DefinitionGraphNode {
    pub(super) id: String,
    pub(super) kind: String,
    pub(super) definition_kind: String,
    pub(super) name: String,
    pub(super) label: String,
    pub(super) defined: bool,
    pub(super) semantic_role: String,
    pub(super) litex_form: String,
    pub(super) knowledge_status: String,
    pub(super) trust_kind: Option<String>,
    pub(super) line_file: Option<LineFile>,
    pub(super) statement: Option<String>,
}

#[derive(Clone)]
pub(super) struct DefinitionGraphEdge {
    pub(super) from: String,
    pub(super) to: String,
    pub(super) kind: String,
    pub(super) reference_kind: String,
    pub(super) count: usize,
}

pub(super) struct DefinitionGraphBuilder {
    pub(super) nodes: Vec<DefinitionGraphNode>,
    pub(super) node_index: HashMap<String, usize>,
    pub(super) edges: Vec<DefinitionGraphEdge>,
    pub(super) edge_index: HashMap<String, usize>,
    pub(super) active_canonical_name: Option<String>,
    pub(super) canonical_name_by_source: HashMap<String, String>,
}
