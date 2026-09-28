//! Kernel-generated surface names for new_pipeline.
//!
//! User source cannot start with `__` (tokenizer / name validation). Temporary
//! params and printable fact names use one shape each:
//! - identifier / binder: `__param_<IdentifierId>`
//! - fact name (when needed): `__fact_<FactId>`

use super::runtime::Runtime;
use super::runtime_ids::{FactId, IdentifierId};
use crate::ast::names::BoundName;

pub const INTERNAL_PARAM_PREFIX: &str = "__param_";
pub const INTERNAL_FACT_PREFIX: &str = "__fact_";

pub fn format_internal_param_name(id: IdentifierId) -> String {
    format!("{}{}", INTERNAL_PARAM_PREFIX, id.value())
}

pub fn format_internal_fact_name(id: FactId) -> String {
    format!("{}{}", INTERNAL_FACT_PREFIX, id.value())
}

impl Runtime {
    /// Allocate a fresh binder: `BoundName { id, name: __param_<id> }`.
    pub fn fresh_internal_param(&mut self) -> BoundName {
        let id = self.global_ids.allocate_identifier_id();
        BoundName::new(id, format_internal_param_name(id))
    }

    /// Allocate a FactId and a printable internal fact name `__fact_<id>`.
    pub fn fresh_internal_fact_name(&mut self) -> (String, FactId) {
        let id = self.global_ids.allocate_fact_id();
        (format_internal_fact_name(id), id)
    }
}
