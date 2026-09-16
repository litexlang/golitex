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

mod capture;
mod error;
mod fact;
mod mode;
mod obj;
mod param;

#[cfg(test)]
mod tests;

pub use error::InstError;
pub use fact::quantifier_free_fact_to_fact;
pub use mode::SubstitutionMode;

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::Runtime;

pub(crate) struct InstCtx<'a> {
    pub rt: &'a mut Runtime,
    pub subst: HashMap<String, Obj>,
    pub mode: SubstitutionMode,
    pub fresh_counter: u64,
    pub binder_renames: HashMap<String, String>,
}

impl InstCtx<'_> {
    pub fn inst_obj(&mut self, obj: &Obj) -> Result<Obj, InstError> {
        obj::inst_obj(self, obj)
    }
}

impl Runtime {
    pub fn inst_obj(
        &mut self,
        obj: &Obj,
        subst: &HashMap<String, Obj>,
        mode: SubstitutionMode,
    ) -> Result<Obj, InstError> {
        let mut ctx = InstCtx {
            rt: self,
            subst: subst.clone(),
            mode,
            fresh_counter: 0,
            binder_renames: HashMap::new(),
        };
        ctx.inst_obj(obj)
    }

    pub fn inst_fact(
        &mut self,
        fact: &Fact,
        subst: &HashMap<String, Obj>,
        mode: SubstitutionMode,
    ) -> Result<Fact, InstError> {
        let mut ctx = InstCtx {
            rt: self,
            subst: subst.clone(),
            mode,
            fresh_counter: 0,
            binder_renames: HashMap::new(),
        };
        fact::inst_fact(&mut ctx, fact)
    }

    pub fn inst_atomic_fact(
        &mut self,
        atomic: &AtomicFact,
        subst: &HashMap<String, Obj>,
        mode: SubstitutionMode,
    ) -> Result<AtomicFact, InstError> {
        let mut ctx = InstCtx {
            rt: self,
            subst: subst.clone(),
            mode,
            fresh_counter: 0,
            binder_renames: HashMap::new(),
        };
        fact::inst_atomic_fact(&mut ctx, atomic)
    }

    pub fn inst_quantifier_free_fact(
        &mut self,
        fact: &QuantifierFreeFact,
        subst: &HashMap<String, Obj>,
        mode: SubstitutionMode,
    ) -> Result<QuantifierFreeFact, InstError> {
        let mut ctx = InstCtx {
            rt: self,
            subst: subst.clone(),
            mode,
            fresh_counter: 0,
            binder_renames: HashMap::new(),
        };
        fact::inst_quantifier_free_fact(&mut ctx, fact)
    }
}
