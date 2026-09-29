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

use crate::ast::stmt::{DefTemplateStmt, TemplateDefEnum};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, StoreFactAndInferResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_have_fn_by_induc_stmt::{
    ExecHaveFnByInducStmtFailed, ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult,
};
use crate::execute::execute_have_fn_by_forall_exist_unique_stmt::{
    ExecHaveFnByForallExistUniqueStmtFailed, ExecHaveFnByForallExistUniqueStmtResult,
    ExecHaveFnByForallExistUniqueStmtSuccessResult,
};
use crate::execute::execute_have_fn_equal_case_by_case_stmt::{
    ExecHaveFnEqualCaseByCaseStmtFailed, ExecHaveFnEqualCaseByCaseStmtResult,
    ExecHaveFnEqualCaseByCaseStmtSuccessResult,
};
use crate::execute::execute_have_fn_equal_stmt::{
    ExecHaveFnEqualStmtFailed, ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult,
};
use crate::execute::execute_have_obj_by_exist_facts_stmt::{
    ExecHaveObjByExistFactsStmtFailed, ExecHaveObjByExistFactsStmtResult,
    ExecHaveObjByExistFactsStmtSuccessResult,
};
use crate::execute::execute_have_by_replacement_axiom_stmt::{
    ExecHaveByReplacementAxiomStmtFailed, ExecHaveByReplacementAxiomStmtResult,
    ExecHaveByReplacementAxiomStmtSuccessResult,
};
use crate::execute::execute_obtain_obj_from_atomic_fact_stmt::{
    ExecObtainObjFromAtomicFactStmtFailed, ExecObtainObjFromAtomicFactStmtResult,
    ExecObtainObjFromAtomicFactStmtSuccessResult,
};
use crate::execute::execute_obtain_obj_from_exist_fact_stmt::{
    ExecObtainObjFromExistFactStmtFailed, ExecObtainObjFromExistFactStmtResult,
    ExecObtainObjFromExistFactStmtSuccessResult,
};
use crate::execute::execute_have_obj_equal_stmt::{
    ExecHaveObjEqualStmtFailed, ExecHaveObjEqualStmtResult, ExecHaveObjEqualStmtSuccessResult,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::{
    ExecHaveObjInNonemptySetStmtFailed, ExecHaveObjInNonemptySetStmtResult,
    ExecHaveObjInNonemptySetStmtSuccessResult,
};
use crate::execute::execute_unsafe_stmt::{
    ExecTrustHaveStmtFailed, ExecTrustHaveStmtResult, ExecTrustHaveStmtSuccessResult,
};
use crate::execute::{
    IntroduceTypedParametersFailed, IntroduceTypedParametersResult,
};
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::parse::keywords::TEMPLATE;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};

pub enum ExecDefTemplateStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
    DomainFact(FailToVerifyFactWellDefinedResult),
    BodyHaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtFailed),
    BodyHaveObjEqual(ExecHaveObjEqualStmtFailed),
    BodyHaveObjByExistFacts(ExecHaveObjByExistFactsStmtFailed),
    BodyHaveByReplacementAxiom(ExecHaveByReplacementAxiomStmtFailed),
    BodyObtainObjFromExistFact(ExecObtainObjFromExistFactStmtFailed),
    BodyObtainObjFromAtomicFact(ExecObtainObjFromAtomicFactStmtFailed),
    BodyHaveFnEqual(ExecHaveFnEqualStmtFailed),
    BodyHaveFnEqualCaseByCase(ExecHaveFnEqualCaseByCaseStmtFailed),
    BodyHaveFnByForallExistUnique(ExecHaveFnByForallExistUniqueStmtFailed),
    BodyHaveFnByInduc(ExecHaveFnByInducStmtFailed),
    BodyTrustHave(ExecTrustHaveStmtFailed),
    UnsupportedBody(String),
}

pub enum ExecTemplateDefBodyResult {
    HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtSuccessResult),
    HaveObjEqual(ExecHaveObjEqualStmtSuccessResult),
    HaveObjByExistFacts(ExecHaveObjByExistFactsStmtSuccessResult),
    HaveByReplacementAxiom(ExecHaveByReplacementAxiomStmtSuccessResult),
    ObtainObjFromExistFact(ExecObtainObjFromExistFactStmtSuccessResult),
    ObtainObjFromAtomicFact(ExecObtainObjFromAtomicFactStmtSuccessResult),
    HaveFnEqual(ExecHaveFnEqualStmtSuccessResult),
    HaveFnEqualCaseByCase(ExecHaveFnEqualCaseByCaseStmtSuccessResult),
    HaveFnByForallExistUnique(ExecHaveFnByForallExistUniqueStmtSuccessResult),
    HaveFnByInduc(ExecHaveFnByInducStmtSuccessResult),
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
    pub(in crate::execute) fn exec_def_template_stmt(
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
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
                    builtin_strategy_depth_remaining: VerifyState::BUILTIN_STRATEGY_DEPTH_LIMIT,
};

        let introduced_params = match self
            .introduce_typed_parameters(&def_template.template_arg_def, verify_state.clone())?
        {
            Ok(result) => result,
            Err(IntroduceTypedParametersFailed::ParamType(failed)) => {
                return Ok(Err(ExecDefTemplateStmtFailed::ParamType(failed)));
            }
            Err(IntroduceTypedParametersFailed::AutoOpenStructLayer { failed, .. }) => {
                return Ok(Err(ExecDefTemplateStmtFailed::AutoOpenStructLayer(failed)));
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
            TemplateDefEnum::HaveByReplacementAxiomStmt(stmt) => {
                match self.exec_have_by_replacement_axiom_stmt(stmt)? {
                    ExecHaveByReplacementAxiomStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveByReplacementAxiom(ok)))
                    }
                    ExecHaveByReplacementAxiomStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveByReplacementAxiom(failed),
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
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => {
                match self.exec_have_fn_equal_case_by_case_stmt(stmt)? {
                    ExecHaveFnEqualCaseByCaseStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveFnEqualCaseByCase(ok)))
                    }
                    ExecHaveFnEqualCaseByCaseStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveFnEqualCaseByCase(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => {
                match self.exec_have_fn_by_forall_exist_unique_stmt(stmt)? {
                    ExecHaveFnByForallExistUniqueStmtResult::Success(ok) => Ok(Ok(
                        ExecTemplateDefBodyResult::HaveFnByForallExistUnique(ok),
                    )),
                    ExecHaveFnByForallExistUniqueStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveFnByForallExistUnique(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveFnByInducStmt(stmt) => {
                match self.exec_have_fn_by_induc_stmt(stmt)? {
                    ExecHaveFnByInducStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::HaveFnByInduc(ok)))
                    }
                    ExecHaveFnByInducStmtResult::Failed(failed) => {
                        Ok(Err(ExecDefTemplateStmtFailed::BodyHaveFnByInduc(failed)))
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
            TemplateDefEnum::ObtainObjFromExistFact(stmt) => {
                match self.exec_obtain_obj_from_exist_fact_stmt(stmt)? {
                    ExecObtainObjFromExistFactStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::ObtainObjFromExistFact(ok)))
                    }
                    ExecObtainObjFromExistFactStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyObtainObjFromExistFact(failed),
                    )),
                }
            }
            TemplateDefEnum::ObtainObjFromAtomicFact(stmt) => {
                match self.exec_obtain_obj_from_atomic_fact_stmt(stmt)? {
                    ExecObtainObjFromAtomicFactStmtResult::Success(ok) => {
                        Ok(Ok(ExecTemplateDefBodyResult::ObtainObjFromAtomicFact(ok)))
                    }
                    ExecObtainObjFromAtomicFactStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyObtainObjFromAtomicFact(failed),
                    )),
                }
            }
        }
    }
}
