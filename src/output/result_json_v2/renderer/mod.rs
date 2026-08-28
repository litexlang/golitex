use crate::output::json_value::{render_json_value, JsonValue};
use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

use super::helpers::*;

mod algorithm_definitions;
mod binder_well_definedness;
mod builtin_proofs;
mod by_statements;
mod cases_and_contradiction;
mod claims_and_theorems;
mod commands;
mod definitions;
mod fact_statements;
mod fact_storage;
mod fact_verification;
mod fact_well_definedness;
mod inductive_functions;
mod iteration_well_definedness;
mod known_forall;
mod model;
mod object_well_definedness;
mod proof_blocks;
mod shared_facts;
mod statement_dispatch;
mod structure_definitions;
mod template_instantiation;
mod tuple_functions;
mod witnesses;

pub use model::display_stmt_result_json_v2;
pub(super) use model::StmtResultJsonV2;
use model::SCHEMA;
