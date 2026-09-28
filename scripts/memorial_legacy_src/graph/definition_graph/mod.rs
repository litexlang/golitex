use super::result_graph_execution::DepCollector;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::rc::Rc;

const DEFINITION_GRAPH_NAME: &str = "litex-definition-graph";
const DEFINITION_GRAPH_VERSION: &str = "0.3";

mod analysis;
mod construction;
mod definition_inventory;
mod dependency_edges;
mod edge_rendering;
mod entrypoints;
mod model;
mod node_metadata;
mod node_rendering;
mod rendering;
mod result_provenance;

use analysis::*;
pub use entrypoints::render_definition_graph_from_stmt_results;
pub(super) use entrypoints::{
    definition_graph_file_target, definition_graph_repository_target,
    definition_graph_target_error_output, render_definition_graph_result,
};
use model::*;
