//! Pipeline: count → exist WD → witness WD → witness type → local(proof → body → [exist!]) → store.
//!
//! Optional indented proof body runs in a local env (full Stmt, claim-style).
//! Substituted body obligations are verified after the proof steps in that same local.
//! Example (flat):
//!   witness exist x R st {x = 0} from 0
//! Example (with body):
//!   witness exist u R st {0 < u, u < 1} from 1 / 2:
//!       0 < 1 / 2
//!       1 / 2 < 1

use std::collections::HashMap;

use crate::ast::fact::{exist_shaped_fact_to_fact, AtomicFact, ExistShapedFact, Fact, PlainExistFact};
use crate::ast::obj::Obj;
use crate::ast::stmt::{Stmt, WitnessExistFact, WitnessStmt};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, VerifyFactResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_proof_block_stmt::{run_proof_body_stmts, ProofBlockBodyFailed};
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

use super::exec_witness_atomic_fact::ExecWitnessAtomicFactStmtResult;
use super::exec_witness_nonempty_set::ExecWitnessNonemptySetStmtResult;

pub enum ExecWitnessStmtResult {
    WitnessExistFact(ExecWitnessExistFactStmtResult),
    WitnessAtomicFact(ExecWitnessAtomicFactStmtResult),
    WitnessNonemptySet(ExecWitnessNonemptySetStmtResult),
}

impl ExecWitnessStmtResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::WitnessExistFact(r) => r.is_failed(),
            Self::WitnessAtomicFact(r) => r.is_failed(),
            Self::WitnessNonemptySet(r) => r.is_failed(),
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
    WitnessTypeInstantiate(String),
    WitnessType(VerifyFactResult),
    IntroduceBinders(crate::execute::introduce_typed_parameters::IntroduceTypedParametersFailed),
    ProofBody(ProofBlockBodyFailed),
    BodyCheck(VerifyFactResult),
    BodyInstantiate,
    Uniqueness(VerifyFactResult),
}

// Ambient WD stages before the local proof scope (shared by exist / `$P`).
pub struct WitnessExistAmbientSuccess {
    pub exist_fact_well_defined: FactWellDefinedProof,
    pub witness_obj_well_defined: Vec<VerifyObjWellDefinedResult>,
    pub witness_type_checks: Vec<VerifyFactResult>,
}

// Obligation stages after proof_steps inside the local env.
pub struct WitnessExistObligationSuccess {
    pub body_checks: Vec<VerifyFactResult>,
    pub uniqueness_check: Option<VerifyFactResult>,
}

// Stage order: ambient → proof_steps → obligations → local_env → store.
pub struct ExecWitnessExistFactStmtSuccessResult {
    pub statement: WitnessExistFact,
    pub ambient: WitnessExistAmbientSuccess,
    pub proof_steps: Vec<ExecStmtResult>,
    pub obligations: WitnessExistObligationSuccess,
    pub local_env: Box<ExecEnv>,
    pub store_and_infer_result: StoreFactAndInferResult,
}

impl Runtime {
    pub(in crate::execute) fn exec_witness_stmt(
        &mut self,
        stmt: &WitnessStmt,
    ) -> RuntimeResult<ExecWitnessStmtResult> {
        match stmt {
            WitnessStmt::WitnessExistFact(exist) => Ok(ExecWitnessStmtResult::WitnessExistFact(
                self.exec_witness_exist_fact(exist)?,
            )),
            WitnessStmt::WitnessAtomicFact(atomic) => Ok(ExecWitnessStmtResult::WitnessAtomicFact(
                self.exec_witness_atomic_fact(atomic)?,
            )),
            WitnessStmt::WitnessNonemptySet(nonempty) => {
                Ok(ExecWitnessStmtResult::WitnessNonemptySet(
                    self.exec_witness_nonempty_set(nonempty)?,
                ))
            }
        }
    }

    // Mathematical contract: concrete witnesses satisfy param types and the
    // substituted exist body (after optional local proof); then store the exist.
    pub(in crate::execute) fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> RuntimeResult<ExecWitnessExistFactStmtResult> {
        match self.run_witness_exist_with_proof(
            &stmt.exist_shaped_fact_in_witness,
            &stmt.equal_tos,
            &stmt.proof,
         crate::execute::execute_fact_stmt::VerifyState::top_level())? {
            Ok((ambient, proof_steps, obligations, local_env)) => {
                let exist_as_fact = exist_shaped_fact_to_fact(&stmt.exist_shaped_fact_in_witness);
                let store_and_infer_result = self.store_fact_and_infer(&exist_as_fact, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
                Ok(ExecWitnessExistFactStmtResult::Success(
                    ExecWitnessExistFactStmtSuccessResult {
                        statement: stmt.clone(),
                        ambient,
                        proof_steps,
                        obligations,
                        local_env,
                        store_and_infer_result,
                    },
                ))
            }
            Err(failed) => Ok(ExecWitnessExistFactStmtResult::Failed(failed)),
        }
    }

    // Shared by `witness exist` and `witness $P`: ambient WD and concrete
    // witness typing, then a local proof of the substituted body.
    // Before the proof body, bind exist params and store `param = witness` so the
    // body can mention binder names (legacy parity), e.g.
    //   witness exist m R st {m = 0} from 0:
    //       m = 0
    pub(in crate::execute) fn run_witness_exist_with_proof(
        &mut self,
        exist_fact: &ExistShapedFact,
        equal_tos: &[Obj],
        proof: &[Stmt],
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<
        Result<
            (
                WitnessExistAmbientSuccess,
                Vec<ExecStmtResult>,
                WitnessExistObligationSuccess,
                Box<ExecEnv>,
            ),
            ExecWitnessExistFactStmtFailed,
        >,
    > {
        let verify_state = VerifyState::top_level();

        let plain = match exist_fact {
            ExistShapedFact::Exist(p) | ExistShapedFact::ExistUnique(p) => p,
            ExistShapedFact::NotExist(_) => {
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
        if expected != equal_tos.len() {
            return Ok(Err(ExecWitnessExistFactStmtFailed::WitnessCountMismatch));
        }

        let ambient = match self.check_witness_exist_ambient(exist_fact, equal_tos, verify_state.clone())?
        {
            Ok(a) => a,
            Err(failed) => return Ok(Err(failed)),
        };

        let need_uniqueness = matches!(exist_fact, ExistShapedFact::ExistUnique(_));
        let (local_outcome, local_env) = self.run_in_local_env_and_take_env(|rt| {
            // Nested local may bind the same surface names as an ambient obtain;
            // define_typed_parameters checks the top env only.
            match rt.introduce_typed_parameters(&plain.typed_parameters, verify_state.clone())? {
                Ok(_) => {}
                Err(failed) => {
                    return Ok(Err(ExecWitnessExistFactStmtFailed::IntroduceBinders(failed)));
                }
            }
            {
                let mut witness_index = 0;
                for group in &plain.typed_parameters.groups {
                    for param in &group.params {
                        let witness = &equal_tos[witness_index];
                        witness_index += 1;
                        let left = Obj::Identifier(rt.identifier_obj_for_stored_mention(param));
                        let equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(
                            crate::ast::fact::EqualFact {
                                fact_id: rt.global_ids.allocate_fact_id(),
                                left,
                                right: witness.clone(),
                                line_file: plain.line_file.clone(),
                            },
                        ));
                        rt.store_fact_and_infer(&equal_fact, verify_state)?;
                    }
                }
            }
            let proof_steps = match run_proof_body_stmts(rt, proof)? {
                Ok(steps) => steps,
                Err(failed) => {
                    return Ok(Err(ExecWitnessExistFactStmtFailed::ProofBody(failed)));
                }
            };
            match rt.check_witness_exist_obligations_after_proof(
                plain,
                equal_tos,
                need_uniqueness,
                verify_state.clone(),
            )? {
                Ok(obligations) => Ok(Ok((proof_steps, obligations))),
                Err(failed) => Ok(Err(failed)),
            }
        })?;

        match local_outcome {
            Ok((proof_steps, obligations)) => {
                Ok(Ok((ambient, proof_steps, obligations, local_env)))
            }
            Err(failed) => Ok(Err(failed)),
        }
    }

    fn check_witness_exist_ambient(
        &mut self,
        exist_fact: &ExistShapedFact,
        equal_tos: &[Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<WitnessExistAmbientSuccess, ExecWitnessExistFactStmtFailed>> {
        let exist_fact_well_defined =
            match self.wrap_exist_fact_wd(exist_fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => proof,
                VerifyFactWellDefinedResult::Failed(reason) => {
                    return Ok(Err(ExecWitnessExistFactStmtFailed::ExistFactWellDefined(
                        reason,
                    )));
                }
            };

        let mut witness_obj_well_defined = Vec::with_capacity(equal_tos.len());
        for witness in equal_tos {
            let wd = self.verify_obj_well_definedness(witness, verify_state.clone())?;
            if wd.is_failed() {
                return Ok(Err(
                    ExecWitnessExistFactStmtFailed::WitnessObjWellDefined(wd),
                ));
            }
            witness_obj_well_defined.push(wd);
        }

        // This check must precede introduction of the existential binders.
        // Otherwise their assumed types and `param = witness` can prove the
        // very witness type being checked (e.g. x in {1}, x = 0 ⊢ 0 in {1}).
        let type_facts = self
            .type_facts_for_typed_arguments(&exist_fact.plain().typed_parameters, equal_tos)
            .map_err(ExecWitnessExistFactStmtFailed::WitnessTypeInstantiate);
        let type_facts = match type_facts {
            Ok(facts) => facts,
            Err(failed) => return Ok(Err(failed)),
        };
        let mut witness_type_checks = Vec::with_capacity(type_facts.len());
        for fact in &type_facts {
            let check = self.verify_fact(fact, verify_state.clone())?;
            if check.is_failed() {
                return Ok(Err(ExecWitnessExistFactStmtFailed::WitnessType(check)));
            }
            witness_type_checks.push(check);
        }

        Ok(Ok(WitnessExistAmbientSuccess {
            exist_fact_well_defined,
            witness_obj_well_defined,
            witness_type_checks,
        }))
    }

    fn check_witness_exist_obligations_after_proof(
        &mut self,
        plain: &PlainExistFact,
        equal_tos: &[Obj],
        need_uniqueness: bool,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<WitnessExistObligationSuccess, ExecWitnessExistFactStmtFailed>> {
        let body_checks =
            match self.verify_witness_body_checks(plain, equal_tos, verify_state.clone())? {
                Ok(checks) => checks,
                Err(failed) => return Ok(Err(failed)),
            };

        let uniqueness_check = if need_uniqueness {
            let uniqueness = self.build_exist_unique_uniqueness_forall_fact(plain)?;
            let uniqueness_as_fact = Fact::ForallFact(uniqueness);
            let verify_result = self.verify_fact(&uniqueness_as_fact, verify_state)?;
            if verify_result.is_failed() {
                return Ok(Err(ExecWitnessExistFactStmtFailed::Uniqueness(
                    verify_result,
                )));
            }
            Some(verify_result)
        } else {
            None
        };

        Ok(Ok(WitnessExistObligationSuccess {
            body_checks,
            uniqueness_check,
        }))
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
