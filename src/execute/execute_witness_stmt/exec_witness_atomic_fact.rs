//! `witness $P(args) from ws…` — introduce `$P` via its sole ordinary `exist` clause.
//!
//! Mathematical contract:
//! - resolve concrete prop (reject abstract_prop / missing);
//! - sole definition clause must be ordinary `exist` (reject `exist!` / `not exist` /
//!   multi-clause / non-exist);
//! - instantiate clause with call args;
//! - run the same exist-witness obligation checks as `witness exist` (no store of exist);
//! - store `$P` via `store_fact_and_infer` (definition inference may expose the exist).
//!
//! Example:
//!   prop has_copy(a R):
//!       exist x R st {x = a}
//!   witness $has_copy(2) from 2
//!   // stores `$has_copy(2)`; inference may expose `exist x R st {x = 2}`

use std::collections::HashMap;

use crate::ast::fact::{
    exist_shaped_fact_from_fact, exist_shaped_fact_to_fact, AtomicFact, ExistShapedFact, Fact,
};
use crate::ast::obj::Obj;
use crate::ast::stmt::WitnessAtomicFact;
use super::exec_witness_exist_fact::{
    ExecWitnessExistFactStmtFailed, WitnessExistCheckSuccess,
};
use crate::runtime::{IdentifierId, Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecWitnessAtomicFactStmtResult {
    Success(ExecWitnessAtomicFactStmtSuccessResult),
    Failed(ExecWitnessAtomicFactStmtFailed),
}

impl ExecWitnessAtomicFactStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecWitnessAtomicFactStmtFailed {
    AbstractProp,
    PropNotFound,
    BadDefinition(String),
    Instantiate(String),
    ExistCheck(ExecWitnessExistFactStmtFailed),
}

pub struct ExecWitnessAtomicFactStmtSuccessResult {
    pub statement: WitnessAtomicFact,
    pub projected_exist: ExistShapedFact,
    pub exist_check: WitnessExistCheckSuccess,
    pub store_and_infer_result: StoreFactAndInferResult,
}

impl Runtime {
    // Pipeline: resolve prop → project sole ordinary exist → inst with call args
    // → exist-witness checks (no store) → store `$P`.
    pub(in crate::execute) fn exec_witness_atomic_fact(
        &mut self,
        stmt: &WitnessAtomicFact,
    ) -> RuntimeResult<ExecWitnessAtomicFactStmtResult> {
        let prop_name = stmt.atomic_fact.predicate.local_name();

        if self.def_abstract_prop_visible_in_stack(prop_name).is_some() {
            return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                ExecWitnessAtomicFactStmtFailed::AbstractProp,
            ));
        }

        let Some(definition) = self.def_prop_visible_in_stack(prop_name).cloned() else {
            return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                ExecWitnessAtomicFactStmtFailed::PropNotFound,
            ));
        };

        let projected = match project_sole_ordinary_exist_clause(&definition.iff_facts) {
            Ok(family) => family,
            Err(msg) => {
                return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                    ExecWitnessAtomicFactStmtFailed::BadDefinition(msg),
                ));
            }
        };

        let param_ids = definition.typed_parameters.ordered_param_ids();
        if param_ids.len() != stmt.atomic_fact.body.len() {
            return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                ExecWitnessAtomicFactStmtFailed::BadDefinition(format!(
                    "prop `{prop_name}` expects {} argument(s), got {}",
                    param_ids.len(),
                    stmt.atomic_fact.body.len()
                )),
            ));
        }

        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in param_ids.into_iter().zip(stmt.atomic_fact.body.iter()) {
            subst.insert(id, arg.clone());
        }

        let projected_exist = match self.inst_fact(&exist_shaped_fact_to_fact(&projected), &subst) {
            Ok(instantiated) => match exist_shaped_fact_from_fact(&instantiated) {
                Some(family) => family,
                None => {
                    return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                        ExecWitnessAtomicFactStmtFailed::Instantiate(
                            "instantiated prop clause is not an exist family".to_string(),
                        ),
                    ));
                }
            },
            Err(err) => {
                return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                    ExecWitnessAtomicFactStmtFailed::Instantiate(err.to_string()),
                ));
            }
        };

        let exist_check =
            match self.check_witness_exist_obligations(&projected_exist, &stmt.witnesses)? {
                Ok(check) => check,
                Err(failed) => {
                    return Ok(ExecWitnessAtomicFactStmtResult::Failed(
                        ExecWitnessAtomicFactStmtFailed::ExistCheck(failed),
                    ));
                }
            };

        let atomic_as_fact =
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(stmt.atomic_fact.clone()));
        let store_and_infer_result = self.store_fact_and_infer(&atomic_as_fact)?;

        Ok(ExecWitnessAtomicFactStmtResult::Success(
            ExecWitnessAtomicFactStmtSuccessResult {
                statement: stmt.clone(),
                projected_exist,
                exist_check,
                store_and_infer_result,
            },
        ))
    }
}

fn project_sole_ordinary_exist_clause(iff_facts: &[Fact]) -> Result<ExistShapedFact, String> {
    if iff_facts.len() != 1 {
        return Err(format!(
            "witness `$P` requires exactly one definition clause, got {}",
            iff_facts.len()
        ));
    }
    match exist_shaped_fact_from_fact(&iff_facts[0]) {
        Some(ExistShapedFact::Exist(p)) => Ok(ExistShapedFact::Exist(p)),
        Some(ExistShapedFact::ExistUnique(_)) => Err(
            "witness `$P` does not support an `exist!` definition clause; use explicit `witness exist! …` then `by def`"
                .to_string(),
        ),
        Some(ExistShapedFact::NotExist(_)) => Err(
            "witness `$P` cannot introduce a `not exist` definition clause".to_string(),
        ),
        None => Err(
            "witness `$P` requires the sole definition clause to be ordinary `exist`".to_string(),
        ),
    }
}
