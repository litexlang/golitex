//! `obtain x, y from $P(args)` — eliminate via a concrete prop's sole exist clause.
//!
//! Mathematical contract:
//! - `$P(args)` must verify in the current environment.
//! - `P` must be a concrete `prop` (not `abstract_prop`) whose definition has
//!   exactly one positive `exist` / `exist!` clause (reject `not exist`,
//!   non-exist, and multi-clause definitions).
//! - Instantiate that clause with the call arguments, then run ordinary
//!   existential elimination (`apply_obtain_from_known_exist_family`).
//!
//! Example:
//!   prop has_copy(a R):
//!       exist x R st {x = a}
//!   $has_copy(2)
//!   obtain copy from $has_copy(2)
//!   // stores `copy $in R` and `copy = 2`

use std::collections::HashMap;

use crate::ast::fact::{
    exist_shaped_fact_from_fact, exist_shaped_fact_to_fact, AtomicFact, ExistShapedFact, Fact,
};
use crate::ast::obj::Obj;
use crate::ast::stmt::ObtainObjFromAtomicFact;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::execute_obtain_obj_from_exist_fact_stmt::ExecObtainObjFromExistFactStmtFailed;
use crate::runtime::{IdentifierId, Runtime, RuntimeResult};

pub enum ExecObtainObjFromAtomicFactStmtFailed {
    AbstractProp,
    PropNotFound,
    BadDefinition(String),
    AtomicVerifyFailed(VerifyFactResult),
    Instantiate(String),
    Apply(ExecObtainObjFromExistFactStmtFailed),
}

pub struct ExecObtainObjFromAtomicFactStmtSuccessResult {
    pub statement: ObtainObjFromAtomicFact,
    pub verify_atomic: VerifyFactResult,
    pub projected_exist: ExistShapedFact,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

pub enum ExecObtainObjFromAtomicFactStmtResult {
    Success(ExecObtainObjFromAtomicFactStmtSuccessResult),
    Failed(ExecObtainObjFromAtomicFactStmtFailed),
}

impl ExecObtainObjFromAtomicFactStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // Pipeline: resolve prop → project sole exist → inst with call args
    // → verify `$P` → apply existential eliminator.
    pub(super) fn exec_obtain_obj_from_atomic_fact_stmt(
        &mut self,
        stmt: &ObtainObjFromAtomicFact,
    ) -> RuntimeResult<ExecObtainObjFromAtomicFactStmtResult> {
        let prop_name = stmt.fact.predicate.local_name();

        if self.def_abstract_prop_visible_in_stack(prop_name).is_some() {
            return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                ExecObtainObjFromAtomicFactStmtFailed::AbstractProp,
            ));
        }

        let Some(definition) = self.def_prop_visible_in_stack(prop_name).cloned() else {
            return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                ExecObtainObjFromAtomicFactStmtFailed::PropNotFound,
            ));
        };

        let projected = match project_sole_positive_exist_clause(&definition.iff_facts) {
            Ok(family) => family,
            Err(msg) => {
                return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                    ExecObtainObjFromAtomicFactStmtFailed::BadDefinition(msg),
                ));
            }
        };

        let param_ids = definition.typed_parameters.ordered_param_ids();
        if param_ids.len() != stmt.fact.body.len() {
            return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                ExecObtainObjFromAtomicFactStmtFailed::BadDefinition(format!(
                    "prop `{prop_name}` expects {} argument(s), got {}",
                    param_ids.len(),
                    stmt.fact.body.len()
                )),
            ));
        }

        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in param_ids.into_iter().zip(stmt.fact.body.iter()) {
            subst.insert(id, arg.clone());
        }

        let projected_exist = match self.inst_fact(&exist_shaped_fact_to_fact(&projected), &subst) {
            Ok(instantiated) => match exist_shaped_fact_from_fact(&instantiated) {
                Some(family) => family,
                None => {
                    return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                        ExecObtainObjFromAtomicFactStmtFailed::Instantiate(
                            "instantiated prop clause is not an exist family".to_string(),
                        ),
                    ));
                }
            },
            Err(err) => {
                return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                    ExecObtainObjFromAtomicFactStmtFailed::Instantiate(err.to_string()),
                ));
            }
        };

        let verify_state = VerifyState {
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };
        let atomic_as_fact = Fact::AtomicFact(AtomicFact::NormalAtomicFact(stmt.fact.clone()));
        let verify_atomic = self.verify_fact(&atomic_as_fact, verify_state)?;
        if verify_atomic.is_failed() {
            return Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                ExecObtainObjFromAtomicFactStmtFailed::AtomicVerifyFailed(verify_atomic),
            ));
        }

        match self.apply_obtain_from_known_exist_family(&projected_exist, &stmt.equal_tos)? {
            Ok(store_and_infer_result) => Ok(ExecObtainObjFromAtomicFactStmtResult::Success(
                ExecObtainObjFromAtomicFactStmtSuccessResult {
                    statement: stmt.clone(),
                    verify_atomic,
                    projected_exist,
                    store_and_infer_result,
                },
            )),
            Err(failed) => Ok(ExecObtainObjFromAtomicFactStmtResult::Failed(
                ExecObtainObjFromAtomicFactStmtFailed::Apply(failed),
            )),
        }
    }
}

fn project_sole_positive_exist_clause(
    iff_facts: &[Fact],
) -> Result<ExistShapedFact, String> {
    if iff_facts.len() != 1 {
        return Err(format!(
            "obtain from `$P` requires exactly one definition clause, got {}",
            iff_facts.len()
        ));
    }
    match exist_shaped_fact_from_fact(&iff_facts[0]) {
        Some(ExistShapedFact::Exist(p)) => Ok(ExistShapedFact::Exist(p)),
        Some(ExistShapedFact::ExistUnique(p)) => Ok(ExistShapedFact::ExistUnique(p)),
        Some(ExistShapedFact::NotExist(_)) => Err(
            "obtain from `$P` cannot eliminate a `not exist` definition clause".to_string(),
        ),
        None => Err(
            "obtain from `$P` requires the sole definition clause to be `exist` or `exist!`"
                .to_string(),
        ),
    }
}
