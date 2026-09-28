//! Result graph nodes, edges, and visitor state.

use super::*;

#[derive(Clone, Debug)]
pub(super) struct ResultGraphNode {
    pub(super) id: String,
    pub(super) kind: String,
    pub(super) role: String,
    pub(super) label: String,
    pub(super) fact_id: Option<FactId>,
}

#[derive(Clone, Debug)]
pub(super) struct ResultGraphEdge {
    pub(super) from: String,
    pub(super) to: String,
    pub(super) kind: String,
    pub(super) order: usize,
}

/// A pure projection of the recursive statement result tree.
///
/// This graph never looks facts or proof routes up in `Runtime`. Statement
/// nesting comes from result fields, and cross-statement proof dependencies
/// use `FactId` or the exact shared memo node.
pub(in super::super) struct ResultGraph {
    pub(super) nodes: Vec<ResultGraphNode>,
    pub(super) node_index: HashMap<String, usize>,
    pub(super) edges: Vec<ResultGraphEdge>,
    pub(super) shared_fact_nodes: HashMap<usize, String>,
    pub(super) shared_wd_obj_nodes: HashMap<usize, String>,
    pub(super) expanded_nodes: HashSet<String>,
}
