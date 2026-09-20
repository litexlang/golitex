//! `template` definition: check body under local params, then store globally.
//!
//! Pipeline stages (field order matches Success):
//! 1. introduce typed params in local env
//! 2. WD + store each domain fact as assumption
//! 3. exec wired body have / trust-have form
//! 4. close local env into the result (not merged)
//! 5. store the template definition in the parent ExecEnv
//!
//! Example:
//!   template<S set>:
//!       have carrier_copy set = S
//!   // S bound locally; body checked; carrier_copy stored as template globally

use crate::new_pipeline::ast::stmt::{DefTemplateStmt, TemplateDefEnum};
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, StoreFactAndInferResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::execute::execute_have_fn_equal_stmt::{
    ExecHaveFnEqualStmtFailed, ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult,
};
use crate::new_pipeline::execute::execute_have_obj_by_exist_facts_stmt::{
    ExecHaveObjByExistFactsStmtFailed, ExecHaveObjByExistFactsStmtResult,
    ExecHaveObjByExistFactsStmtSuccessResult,
};
use crate::new_pipeline::execute::execute_have_obj_equal_stmt::{
    ExecHaveObjEqualStmtFailed, ExecHaveObjEqualStmtResult, ExecHaveObjEqualStmtSuccessResult,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::{
    ExecHaveObjInNonemptySetStmtFailed, ExecHaveObjInNonemptySetStmtResult,
    ExecHaveObjInNonemptySetStmtSuccessResult,
};
use crate::new_pipeline::execute::execute_unsafe_stmt::{
    ExecTrustHaveStmtFailed, ExecTrustHaveStmtResult, ExecTrustHaveStmtSuccessResult,
};
use crate::new_pipeline::execute::IntroduceTypedParametersResult;
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::parse::keywords::TEMPLATE;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

pub enum ExecDefTemplateStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    DomainFact(FailToVerifyFactWellDefinedResult),
    BodyHaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtFailed),
    BodyHaveObjEqual(ExecHaveObjEqualStmtFailed),
    BodyHaveObjByExistFacts(ExecHaveObjByExistFactsStmtFailed),
    BodyHaveFnEqual(ExecHaveFnEqualStmtFailed),
    BodyTrustHave(ExecTrustHaveStmtFailed),
    UnsupportedBody(String),
}

pub enum ExecTemplateDefBodyResult {
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtSuccessResult),
    HaveObjEqual(ExecHaveObjEqualStmtSuccessResult),
    HaveObjByExistFacts(ExecHaveObjByExistFactsStmtSuccessResult),
    HaveFnEqual(ExecHaveFnEqualStmtSuccessResult),
    TrustHave(ExecTrustHaveStmtSuccessResult),
}

pub struct AssumedTemplateDomFactResult {
    pub well_defined: FactWellDefinedProof,
    pub store_and_infer: StoreFactAndInferResult,
}

pub struct ExecDefTemplateStmtSuccessResult {
    pub statement: DefTemplateStmt,
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumedTemplateDomFactResult>,
    pub body: ExecTemplateDefBodyResult,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecDefTemplateStmtResult {
    Success(ExecDefTemplateStmtSuccessResult),
    Failed(ExecDefTemplateStmtFailed),
}

impl ExecDefTemplateStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

struct LocalParts {
    introduced_params: IntroduceTypedParametersResult,
    assumed_dom_facts: Vec<AssumedTemplateDomFactResult>,
    body: ExecTemplateDefBodyResult,
}

impl Runtime {
    // Mathematical contract: a template is checked under a temporary parameter
    // environment; only the template definition escapes to the parent.
    // Example:
    //   template<S set>:
    //       have carrier_copy set = S
    pub(in crate::new_pipeline::execute) fn exec_def_template_stmt(
        &mut self,
        def_template: &DefTemplateStmt,
    ) -> RuntimeResult<ExecDefTemplateStmtResult> {
        self.ensure_def_template_name_free(&def_template.template_name)?;

        let (local_outcome, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.exec_def_template_stmt_in_local(def_template)
        })?;

        let parts = match local_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(ExecDefTemplateStmtResult::Failed(failed)),
        };

        self.top_exec_env_mut()
            .store_def_template(def_template.clone());

        Ok(ExecDefTemplateStmtResult::Success(
            ExecDefTemplateStmtSuccessResult {
                statement: def_template.clone(),
                introduced_params: parts.introduced_params,
                assumed_dom_facts: parts.assumed_dom_facts,
                body: parts.body,
                local_env,
            },
        ))
    }

    fn ensure_def_template_name_free(&self, name: &str) -> RuntimeResult<()> {
        if self.def_template_visible_in_stack(name).is_some() {
            return Err(RuntimeError::InternalBug(format!(
                "name `{name}` is already used in this scope as {TEMPLATE}"
            )));
        }
        Ok(())
    }

    fn exec_def_template_stmt_in_local(
        &mut self,
        def_template: &DefTemplateStmt,
    ) -> RuntimeResult<Result<LocalParts, ExecDefTemplateStmtFailed>> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        let introduced_params = match self
            .introduce_typed_parameters(&def_template.template_arg_def, verify_state.clone())?
        {
            Ok(result) => result,
            Err(failed) => {
                return Ok(Err(ExecDefTemplateStmtFailed::ParamType(failed)));
            }
        };

        let mut assumed_dom_facts = Vec::with_capacity(def_template.template_arg_dom.len());
        for dom in &def_template.template_arg_dom {
            let fact = quantifier_free_fact_to_fact(dom.clone());
            let well_defined = match self.verify_fact_well_definedness(&fact, verify_state.clone())?
            {
                VerifyFactWellDefinedResult::Success(proof) => proof,
                VerifyFactWellDefinedResult::Failed(reason) => {
                    return Ok(Err(ExecDefTemplateStmtFailed::DomainFact(reason)));
                }
            };
            let store_and_infer = self.store_fact_and_infer(&fact)?;
            assumed_dom_facts.push(AssumedTemplateDomFactResult {
                well_defined,
                store_and_infer,
            });
        }

        let body = match self.exec_template_def_body(&def_template.template_def_stmt)? {
            Ok(body) => body,
            Err(failed) => return Ok(Err(failed)),
        };

        Ok(Ok(LocalParts {
            introduced_params,
            assumed_dom_facts,
            body,
        }))
    }

    fn exec_template_def_body(
        &mut self,
        body: &TemplateDefEnum,
    ) -> RuntimeResult<Result<ExecTemplateDefBodyResult, ExecDefTemplateStmtFailed>> {
        match body {
            TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => {
                match self.exec_have_obj_in_nonempty_set_stmt(stmt)? {
                    ExecHaveObjInNonemptySetStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveObjInNonemptySet(ok)))
                    }
                    ExecHaveObjInNonemptySetStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveObjInNonemptySet(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveObjEqualStmt(stmt) => {
                match self.exec_have_obj_equal_stmt(stmt)? {
                    ExecHaveObjEqualStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveObjEqual(ok)))
                    }
                    ExecHaveObjEqualStmtResult::Failed(failed) => {
                        Ok(Err(ExecDefTemplateStmtFailed::BodyHaveObjEqual(failed)))
                    }
                }
            }
            TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => {
                match self.exec_have_obj_by_exist_facts_stmt(stmt)? {
                    ExecHaveObjByExistFactsStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveObjByExistFacts(ok)))
                    }
                    ExecHaveObjByExistFactsStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveObjByExistFacts(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveFnEqualStmt(stmt) => {
                match self.exec_have_fn_equal_stmt(stmt)? {
                    ExecHaveFnEqualStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveFnEqual(ok)))
                    }
                    ExecHaveFnEqualStmtResult::Failed(failed) => {
                        Ok(Err(ExecDefTemplateStmtFailed::BodyHaveFnEqual(failed)))
                    }
                }
            }
            TemplateDefEnum::TrustHaveStmt(stmt) => match self.exec_trust_have_stmt(stmt)? {
                ExecTrustHaveStmtResult::Success(ok) => {
                    Ok(Ok(ExecTemplateDefBodyResult::TrustHave(ok)))
                }
                ExecTrustHaveStmtResult::Failed(failed) => {
                    Ok(Err(ExecDefTemplateStmtFailed::BodyTrustHave(failed)))
                }
            },
            TemplateDefEnum::ObtainObjFromExistFact(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `obtain` from exist fact is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::ObtainObjFromAtomicFact(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `obtain` from atomic fact is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::ObtainObjFromThm(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `obtain` from thm is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have fn` case-by-case is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveFnByInducStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have fn` by induc is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have fn` by forall-exist-unique is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveTupleStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have` tuple is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveCartStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have` cart is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveSeqStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have` seq is not wired yet".to_string(),
                ),
            )),
            TemplateDefEnum::HaveFiniteSeqStmt(_) => Ok(Err(
                ExecDefTemplateStmtFailed::UnsupportedBody(
                    "template body `have` finite_seq is not wired yet".to_string(),
                ),
            )),
        }
    }
}
