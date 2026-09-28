//! Graph construction from statement results.

use super::*;

impl ResultGraph {
    pub fn from_stmt_results(stmt_results: &[StmtResult]) -> Self {
        let mut graph = Self {
            nodes: Vec::new(),
            node_index: HashMap::new(),
            edges: Vec::new(),
            shared_fact_nodes: HashMap::new(),
            shared_wd_obj_nodes: HashMap::new(),
            expanded_nodes: HashSet::new(),
        };

        for (index, result) in stmt_results.iter().enumerate() {
            graph.add_stmt_result(result, format!("stmt:{index}"));
        }
        graph
    }
}
