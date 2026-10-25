//! `template` definition: check body under local params, then store globally.
//!
//! Pipeline stages (field order matches Success):
//! 1. introduce typed params in local env
//! 2. WD + store each domain fact as assumption
//! 3. exec wired body have / trust-have form
//! 4. close local env into the result (not merged)
//! 5. store the template definition in the parent ExecEnv
//! 6. publish body definition facts under template binders and premises
//!
//! Example:
//!   template<S set>:
//!       have carrier_copy set = S
//!   // S bound locally; body checked; carrier_copy stored as template globally

use super::store_template_definition_facts::StoreTemplateDefinitionFactResult;
use crate::ast::stmt::{DefTemplateStmt, TemplateDefEnum};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::{
    FailToVerifyFactWellDefinedResult, VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
    VerifyState,
};
use crate::execute::execute_have_by_replacement_axiom_stmt::{
    ExecHaveByReplacementAxiomStmtFailed, ExecHaveByReplacementAxiomStmtResult,
};
use crate::execute::execute_have_fn_by_forall_exist_unique_stmt::{
    ExecHaveFnByForallExistUniqueStmtFailed, ExecHaveFnByForallExistUniqueStmtResult,
};
use crate::execute::execute_have_fn_by_induc_stmt::{
    ExecHaveFnByInducStmtFailed, ExecHaveFnByInducStmtResult,
};
use crate::execute::execute_have_fn_equal_case_by_case_stmt::{
    ExecHaveFnEqualCaseByCaseStmtFailed, ExecHaveFnEqualCaseByCaseStmtResult,
};
use crate::execute::execute_have_fn_equal_stmt::{
    ExecHaveFnEqualStmtFailed, ExecHaveFnEqualStmtResult,
};
use crate::execute::execute_have_obj_by_exist_facts_stmt::{
    ExecHaveObjByExistFactsStmtFailed, ExecHaveObjByExistFactsStmtResult,
};
use crate::execute::execute_have_obj_equal_stmt::{
    ExecHaveObjEqualStmtFailed, ExecHaveObjEqualStmtResult,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::{
    ExecHaveObjInNonemptySetStmtFailed, ExecHaveObjInNonemptySetStmtResult,
};
use crate::execute::execute_obtain_obj_from_atomic_fact_stmt::{
    ExecObtainObjFromAtomicFactStmtFailed, ExecObtainObjFromAtomicFactStmtResult,
};
use crate::execute::execute_obtain_obj_from_exist_fact_stmt::{
    ExecObtainObjFromExistFactStmtFailed, ExecObtainObjFromExistFactStmtResult,
};
use crate::execute::execute_unsafe_stmt::{ExecTrustHaveStmtFailed, ExecTrustHaveStmtResult};
use crate::execute::{
    ExecDefineObjStmtResult, ExecDefinitionStmtResult, ExecStmtResult, ExecTrustBoundaryStmtResult,
    IntroduceTypedParametersFailed, IntroduceTypedParametersResult,
};
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::parse::keywords::TEMPLATE;
use crate::runtime::{Runtime, RuntimeResult};

pub enum ExecDefTemplateStmtFailed {
    NameClash(String),
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

pub type AssumeDomFactResult = crate::execute::execute_fact_stmt::AssumeDomFactResult;

pub struct ExecDefTemplateStmtSuccessResult {
    pub statement: DefTemplateStmt,
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub body: Box<ExecStmtResult>,
    pub local_env: Box<ExecEnv>,
    pub definition_facts: Vec<StoreTemplateDefinitionFactResult>,
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
    assumed_dom_facts: Vec<AssumeDomFactResult>,
    body: Box<ExecStmtResult>,
}

impl Runtime {
    // Mathematical contract: a template is checked under a temporary parameter
    // environment; its definition facts escape only under the template's
    // binders and premises. Parameter assumptions remain local.
    // Example:
    //   template<S set>:
    //       have carrier_copy set = S
    pub(in crate::execute) fn exec_def_template_stmt(
        &mut self,
        def_template: &DefTemplateStmt,
    ) -> RuntimeResult<ExecDefTemplateStmtResult> {
        if let Some(msg) = self.def_template_name_clash(&def_template.template_name) {
            return Ok(ExecDefTemplateStmtResult::Failed(
                ExecDefTemplateStmtFailed::NameClash(msg),
            ));
        }

        let (local_outcome, local_env) = self
            .run_in_local_env_and_take_env(|rt| rt.exec_def_template_stmt_in_local(def_template))?;

        let parts = match local_outcome {
            Ok(parts) => parts,
            Err(failed) => return Ok(ExecDefTemplateStmtResult::Failed(failed)),
        };

        self.top_exec_env_mut()
            .store_def_template(def_template.clone());

        let definition_facts = self.store_template_definition_facts(
            def_template,
            &parts.body,
            &local_env,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;

        Ok(ExecDefTemplateStmtResult::Success(
            ExecDefTemplateStmtSuccessResult {
                statement: def_template.clone(),
                introduced_params: parts.introduced_params,
                assumed_dom_facts: parts.assumed_dom_facts,
                body: parts.body,
                local_env,
                definition_facts,
            },
        ))
    }

    fn def_template_name_clash(&self, name: &str) -> Option<String> {
        if self.def_template_visible_in_stack(name).is_some() {
            return Some(format!(
                "name `{name}` is already used in this scope as {TEMPLATE}"
            ));
        }
        None
    }

    fn exec_def_template_stmt_in_local(
        &mut self,
        def_template: &DefTemplateStmt,
    ) -> RuntimeResult<Result<LocalParts, ExecDefTemplateStmtFailed>> {
        let verify_state = VerifyState::top_level();

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
            let well_defined =
                match self.verify_fact_well_definedness(&fact, verify_state.clone())? {
                    VerifyFactWellDefinedResult::Success(proof) => proof,
                    VerifyFactWellDefinedResult::Failed(reason) => {
                        return Ok(Err(ExecDefTemplateStmtFailed::DomainFact(reason)));
                    }
                };
            let store_and_infer = self.store_fact_and_infer(
                &fact,
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            )?;
            assumed_dom_facts.push(AssumeDomFactResult {
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
    ) -> RuntimeResult<Result<Box<ExecStmtResult>, ExecDefTemplateStmtFailed>> {
        match body {
            TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => {
                match self.exec_have_obj_in_nonempty_set_stmt(stmt)? {
                    ExecHaveObjInNonemptySetStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                                ExecHaveObjInNonemptySetStmtResult::Success(ok),
                            ),
                        )),
                    ))),
                    ExecHaveObjInNonemptySetStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveObjInNonemptySet(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveObjEqualStmt(stmt) => {
                match self.exec_have_obj_equal_stmt(stmt)? {
                    ExecHaveObjEqualStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::HaveObjEqual(
                                ExecHaveObjEqualStmtResult::Success(ok),
                            ),
                        )),
                    ))),
                    ExecHaveObjEqualStmtResult::Failed(failed) => {
                        Ok(Err(ExecDefTemplateStmtFailed::BodyHaveObjEqual(failed)))
                    }
                }
            }
            TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => {
                match self.exec_have_obj_by_exist_facts_stmt(stmt)? {
                    ExecHaveObjByExistFactsStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::HaveObjByExistFacts(
                                ExecHaveObjByExistFactsStmtResult::Success(ok),
                            ),
                        )),
                    ))),
                    ExecHaveObjByExistFactsStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveObjByExistFacts(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveByReplacementAxiomStmt(stmt) => {
                match self.exec_have_by_replacement_axiom_stmt(stmt)? {
                    ExecHaveByReplacementAxiomStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::HaveByReplacementAxiom(
                                ExecHaveByReplacementAxiomStmtResult::Success(ok),
                            ),
                        )),
                    ))),
                    ExecHaveByReplacementAxiomStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveByReplacementAxiom(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveFnEqualStmt(stmt) => match self.exec_have_fn_equal_stmt(stmt)? {
                ExecHaveFnEqualStmtResult::Success(ok) => Ok(Ok(Box::new(
                    ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
                        ExecHaveFnEqualStmtResult::Success(ok),
                    )),
                ))),
                ExecHaveFnEqualStmtResult::Failed(failed) => {
                    Ok(Err(ExecDefTemplateStmtFailed::BodyHaveFnEqual(failed)))
                }
            },
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => {
                match self.exec_have_fn_equal_case_by_case_stmt(stmt)? {
                    ExecHaveFnEqualCaseByCaseStmtResult::Success(ok) => {
                        Ok(Ok(Box::new(ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                                ExecHaveFnEqualCaseByCaseStmtResult::Success(ok),
                            ),
                        ))))
                    }
                    ExecHaveFnEqualCaseByCaseStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveFnEqualCaseByCase(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => {
                match self.exec_have_fn_by_forall_exist_unique_stmt(stmt)? {
                    ExecHaveFnByForallExistUniqueStmtResult::Success(ok) => {
                        Ok(Ok(Box::new(ExecStmtResult::Definition(
                            ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                                ExecHaveFnByForallExistUniqueStmtResult::Success(ok),
                            ),
                        ))))
                    }
                    ExecHaveFnByForallExistUniqueStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyHaveFnByForallExistUnique(failed),
                    )),
                }
            }
            TemplateDefEnum::HaveFnByInducStmt(stmt) => {
                match self.exec_have_fn_by_induc_stmt(stmt)? {
                    ExecHaveFnByInducStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                            ExecHaveFnByInducStmtResult::Success(ok),
                        )),
                    ))),
                    ExecHaveFnByInducStmtResult::Failed(failed) => {
                        Ok(Err(ExecDefTemplateStmtFailed::BodyHaveFnByInduc(failed)))
                    }
                }
            }
            TemplateDefEnum::TrustHaveStmt(stmt) => match self.exec_trust_have_stmt(stmt)? {
                ExecTrustHaveStmtResult::Success(ok) => Ok(Ok(Box::new(ExecStmtResult::Trust(
                    ExecTrustBoundaryStmtResult::TrustHaveStmt(ExecTrustHaveStmtResult::Success(
                        ok,
                    )),
                )))),
                ExecTrustHaveStmtResult::Failed(failed) => {
                    Ok(Err(ExecDefTemplateStmtFailed::BodyTrustHave(failed)))
                }
            },
            TemplateDefEnum::ObtainObjFromExistFact(stmt) => {
                match self.exec_obtain_obj_from_exist_fact_stmt(stmt)? {
                    ExecObtainObjFromExistFactStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                                ExecObtainObjFromExistFactStmtResult::Success(ok),
                            ),
                        )),
                    ))),
                    ExecObtainObjFromExistFactStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyObtainObjFromExistFact(failed),
                    )),
                }
            }
            TemplateDefEnum::ObtainObjFromAtomicFact(stmt) => {
                match self.exec_obtain_obj_from_atomic_fact_stmt(stmt)? {
                    ExecObtainObjFromAtomicFactStmtResult::Success(ok) => Ok(Ok(Box::new(
                        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                                ExecObtainObjFromAtomicFactStmtResult::Success(ok),
                            ),
                        )),
                    ))),
                    ExecObtainObjFromAtomicFactStmtResult::Failed(failed) => Ok(Err(
                        ExecDefTemplateStmtFailed::BodyObtainObjFromAtomicFact(failed),
                    )),
                }
            }
        }
    }
}
