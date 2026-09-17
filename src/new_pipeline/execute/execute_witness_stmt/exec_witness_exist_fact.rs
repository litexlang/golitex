//! Pipeline: count → exist WD → witness WD → type checks → body checks → [exist!] → store.
//!
//! No local binder env and no proof body. Body facts are verified after substituting
//! binders with witness objects; earlier body successes are not stored for later ones.
//! Example:
//!   0 $in R
//!   0 = 0
//!   witness exist x R st {x = 0} from 0

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{AtomicFact, ExistFact, Fact, InFact, PlainExistFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::ast::stmt::{WitnessExistFact, WitnessStmt};
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeFactCheckResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyExistFactFailed,
    VerifyExistFactResult, VerifyExistUniqueFactResult, VerifyFactResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

pub enum ExecWitnessStmtResult {
    WitnessExistFact(ExecWitnessExistFactStmtResult),
}

impl ExecWitnessStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::WitnessExistFact(r) => r.is_failed(),
        }
    }
}

pub enum ExecWitnessExistFactStmtResult {
    Success(ExecWitnessExistFactStmtSuccessResult),
    Failed(ExecWitnessExistFactStmtFailed),
}

impl ExecWitnessExistFactStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub enum ExecWitnessExistFactStmtFailed {
    WitnessCountMismatch,
    ExistFactWellDefined(FailToVerifyFactWellDefinedResult),
    WitnessObjWellDefined(VerifyObjWellDefinedResult),
    WitnessType(VerifyFactResult),
    BodyCheck(VerifyFactResult),
    BodyInstantiate,
    Uniqueness(VerifyFactResult),
}

// field order = stage order
pub struct ExecWitnessExistFactStmtSuccessResult {
    pub statement: WitnessExistFact,
    pub exist_fact_well_defined: FactWellDefinedProof,
    pub witness_obj_well_defined: Vec<VerifyObjWellDefinedResult>,
    pub witness_type_checks: Vec<ParamTypeFactCheckResult>,
    pub body_checks: Vec<VerifyFactResult>,
    pub uniqueness_check: Option<VerifyFactResult>,
    pub store_and_infer_result: StoreFactAndInferResult,
}

impl Runtime {
    pub(in crate::new_pipeline::execute) fn exec_witness_stmt(
        &mut self,
        stmt: &WitnessStmt,
    ) -> RuntimeResult<ExecWitnessStmtResult> {
        match stmt {
            WitnessStmt::WitnessExistFact(exist) => Ok(ExecWitnessStmtResult::WitnessExistFact(
                self.exec_witness_exist_fact(exist)?,
            )),
            WitnessStmt::WitnessAtomicFact(_) | WitnessStmt::WitnessNonemptySet(_) => {
                Err(RuntimeError::Unsupported(
                    "new_pipeline witness: only `witness exist … from …` is wired".to_string(),
                ))
            }
        }
    }

    // Mathematical contract: concrete witnesses satisfy param types and the
    // substituted exist body; then the exist fact is stored. No binder scope.
    pub(in crate::new_pipeline::execute) fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> RuntimeResult<ExecWitnessExistFactStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        let plain = match &stmt.exist_fact_in_witness {
            ExistFact::PlainExistFact(p) | ExistFact::ExistUniqueFact(p) => p,
            ExistFact::NotExistFact(_) => {
                return Err(RuntimeError::Unsupported(
                    "witness exist: `not exist` cannot be introduced by witness".to_string(),
                ));
            }
        };

        let expected = plain
            .typed_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>();
        if expected != stmt.equal_tos.len() {
            return Ok(ExecWitnessExistFactStmtResult::Failed(
                ExecWitnessExistFactStmtFailed::WitnessCountMismatch,
            ));
        }

        let exist_fact_well_defined = match self
            .wrap_exist_fact_wd(&stmt.exist_fact_in_witness, verify_state.clone())?
        {
            VerifyFactWellDefinedResult::Success(proof) => proof,
            VerifyFactWellDefinedResult::Failed(reason) => {
                return Ok(ExecWitnessExistFactStmtResult::Failed(
                    ExecWitnessExistFactStmtFailed::ExistFactWellDefined(reason),
                ));
            }
        };

        let mut witness_obj_well_defined = Vec::with_capacity(stmt.equal_tos.len());
        for witness in &stmt.equal_tos {
            let wd = self.verify_obj_well_definedness(witness, verify_state.clone())?;
            if wd.is_failed() {
                return Ok(ExecWitnessExistFactStmtResult::Failed(
                    ExecWitnessExistFactStmtFailed::WitnessObjWellDefined(wd),
                ));
            }
            witness_obj_well_defined.push(wd);
        }

        let witness_type_checks = match self.verify_witness_param_type_checks(
            plain,
            &stmt.equal_tos,
            verify_state.clone(),
        )? {
            Ok(checks) => checks,
            Err(failed) => {
                return Ok(ExecWitnessExistFactStmtResult::Failed(failed));
            }
        };

        let body_checks =
            match self.verify_witness_body_checks(plain, &stmt.equal_tos, verify_state.clone())? {
                Ok(checks) => checks,
                Err(failed) => {
                    return Ok(ExecWitnessExistFactStmtResult::Failed(failed));
                }
            };

        let uniqueness_check = if matches!(
            &stmt.exist_fact_in_witness,
            ExistFact::ExistUniqueFact(_)
        ) {
            // Uniqueness forall builder is not ported to new_pipeline yet.
            let FactWellDefinedProof::ExistFact(well_defined_proof) = exist_fact_well_defined
            else {
                return Err(RuntimeError::InternalBug(
                    "witness exist!: exist WD proof must be ExistFact".to_string(),
                ));
            };
            return Ok(ExecWitnessExistFactStmtResult::Failed(
                ExecWitnessExistFactStmtFailed::Uniqueness(VerifyFactResult::ExistFact(Box::new(
                    VerifyExistFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(
                        VerifyExistFactFailed::FailToSearchProof {
                            fact: stmt.exist_fact_in_witness.clone(),
                            well_defined_proof,
                        },
                    )),
                ))),
            ));
        } else {
            None
        };

        let exist_as_fact = Fact::ExistFact(stmt.exist_fact_in_witness.clone());
        let store_and_infer_result = self.store_fact_and_infer(&exist_as_fact)?;

        Ok(ExecWitnessExistFactStmtResult::Success(
            ExecWitnessExistFactStmtSuccessResult {
                statement: stmt.clone(),
                exist_fact_well_defined,
                witness_obj_well_defined,
                witness_type_checks,
                body_checks,
                uniqueness_check,
                store_and_infer_result,
            },
        ))
    }

    fn verify_witness_param_type_checks(
        &mut self,
        plain: &PlainExistFact,
        equal_tos: &[Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<ParamTypeFactCheckResult>, ExecWitnessExistFactStmtFailed>> {
        let mut out = Vec::with_capacity(equal_tos.len());
        let mut witness_index = 0;
        for group in &plain.typed_parameters.groups {
            for _param in &group.params {
                let witness = &equal_tos[witness_index];
                witness_index += 1;
                let check = match &group.param_type {
                    ParamType::Set(_) => ParamTypeFactCheckResult::Set,
                    ParamType::NonemptySet(_) => ParamTypeFactCheckResult::NonemptySet,
                    ParamType::FiniteSet(_) => ParamTypeFactCheckResult::FiniteSet,
                    ParamType::Obj(param_set) => {
                        let fact_id = self.ids.allocate_fact_id();
                        let fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
                            fact_id,
                            element: witness.clone(),
                            set: param_set.clone(),
                            line_file: None,
                        }));
                        let verify_result = self.verify_fact(&fact, verify_state.clone())?;
                        if verify_result.is_failed() {
                            return Ok(Err(ExecWitnessExistFactStmtFailed::WitnessType(
                                verify_result,
                            )));
                        }
                        ParamTypeFactCheckResult::Obj(verify_result)
                    }
                };
                out.push(check);
            }
        }
        Ok(Ok(out))
    }

    fn verify_witness_body_checks(
        &mut self,
        plain: &PlainExistFact,
        equal_tos: &[Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<VerifyFactResult>, ExecWitnessExistFactStmtFailed>> {
        let mut subst = HashMap::new();
        let mut witness_index = 0;
        for group in &plain.typed_parameters.groups {
            for param in &group.params {
                subst.insert(param.id, equal_tos[witness_index].clone());
                witness_index += 1;
            }
        }

        let mut body_checks = Vec::with_capacity(plain.facts.len());
        for body_fact in &plain.facts {
            let instantiated = match self.inst_quantifier_free_fact(body_fact, &subst) {
                Ok(qf) => quantifier_free_fact_to_fact(qf),
                Err(_) => {
                    return Ok(Err(ExecWitnessExistFactStmtFailed::BodyInstantiate));
                }
            };
            let verify_result = self.verify_fact(&instantiated, verify_state.clone())?;
            if verify_result.is_failed() {
                return Ok(Err(ExecWitnessExistFactStmtFailed::BodyCheck(verify_result)));
            }
            body_checks.push(verify_result);
        }
        Ok(Ok(body_checks))
    }
}
