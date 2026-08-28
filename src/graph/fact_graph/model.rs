//! Fact graph nodes, edges, and builder state.

use super::*;

pub(super) struct FactGraphNode {
    pub(super) id: String,
    pub(super) kind: String,
    pub(super) label: String,
    pub(super) fact_kind: Option<String>,
    pub(super) line_file: Option<LineFile>,
    pub(super) statement: Option<String>,
    pub(super) reason: Option<String>,
}

pub(super) struct FactGraphEdge {
    pub(super) from: String,
    pub(super) to: String,
    pub(super) kind: String,
    pub(super) count: usize,
}

pub(super) struct FactGraphBuilder {
    pub(super) nodes: Vec<FactGraphNode>,
    pub(super) node_index: HashMap<String, usize>,
    pub(super) edges: Vec<FactGraphEdge>,
    pub(super) edge_index: HashMap<String, usize>,
    pub(super) trust_node_by_line: HashMap<String, String>,
    pub(super) theorem_node_by_line: HashMap<String, String>,
    pub(super) claim_node_by_line: HashMap<String, String>,
}
