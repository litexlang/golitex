//! Structural substitution (instantiation) for `Obj` and `Fact` in new_pipeline.
//!
//! ## Why these are `Runtime` methods
//!
//! Instantiation **builds new facts**. Every new fact must receive a fresh
//! [`FactId`] by calling [`crate::new_pipeline::runtime::Ids::allocate_fact_id`],
//! which lives on [`Runtime::ids`] and advances the session counter. That is the
//! reason the public entry points are `Runtime::inst_*` rather than free
//! functions or methods on AST types alone.
//!
//! Object-only walks still go through `Runtime` so callers use one API and so
//! nested fact bodies (e.g. inside set builders) can allocate ids the same way.
//!
//! Pure structural replace: no `ExecEnv` or definition-table lookup.
//! Substitution keys are [`IdentifierId`] for plain binders/refs.

mod capture;
mod error;
mod fact;
mod obj;
mod param;

#[cfg(test)]
mod tests;

pub use error::InstError;
pub use fact::quantifier_free_fact_to_fact;
pub(crate) use capture::collect_free_plain_ids;

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::Runtime;

impl Runtime {
    pub fn inst_obj(
        &mut self,
        obj: &Obj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<Obj, InstError> {
        self.inst_obj_rec(obj, param_to_arg_map)
    }

    pub fn inst_fact(
        &mut self,
        fact: &Fact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<Fact, InstError> {
        self.inst_fact_rec(fact, param_to_arg_map)
    }

    pub fn inst_atomic_fact(
        &mut self,
        atomic: &AtomicFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<AtomicFact, InstError> {
        self.inst_atomic_fact_rec(atomic, param_to_arg_map)
    }

    pub fn inst_quantifier_free_fact(
        &mut self,
        fact: &QuantifierFreeFact,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<QuantifierFreeFact, InstError> {
        self.inst_quantifier_free_fact_rec(fact, param_to_arg_map)
    }
}
