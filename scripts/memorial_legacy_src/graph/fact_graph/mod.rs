use crate::prelude::*;
use std::collections::{HashMap, HashSet};

const FACT_GRAPH_NAME: &str = "litex-fact-graph";
const FACT_GRAPH_VERSION: &str = "0.2";

mod analysis;
mod edge_collection;
mod edge_rendering;
mod entrypoints;
mod graph_mutation;
mod model;
mod node_collection;
mod node_rendering;
mod rendering;
mod source_resolution;

use analysis::*;
pub(super) use entrypoints::fact_graph_target_error_output;
pub use entrypoints::render_fact_graph_from_stmt_results;
use model::*;
