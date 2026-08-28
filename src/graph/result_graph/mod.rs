use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

mod construction;
mod fact_proofs;
mod fact_well_definedness;
mod inference_edges;
mod model;
mod object_well_definedness;
mod rendering;
mod roles;
mod statement_results;

pub(super) use model::ResultGraph;
use model::{ResultGraphEdge, ResultGraphNode};
use roles::*;
