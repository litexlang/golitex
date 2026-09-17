use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::well_defined_result::FailToVerifyForallFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::new_pipeline::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

pub enum VerifyForallFactResult {
    Success(VerifyForallFactSuccess),
    Failed(VerifyForallFactFailed),
}

// forall local-proof pipeline (field order = stage order).
// `local_env` is the closed binder scope; it is not merged into the parent.
// The parent stores the whole forall only after this verify succeeds.
pub struct VerifyForallFactSuccess {
    pub fact: ForallFact,
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub proved_then_facts: Vec<ProveAndStoreThenFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub enum VerifyForallFactFailed {
    FailToVerifyWellDefined(FailToVerifyForallFactWellDefinedResult),
    // A then-fact failed (child may itself be WD or search soft miss).
    FailToSearchProof {
        fact: ForallFact,
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        proved_then_facts: Vec<ProveAndStoreThenFactResult>,
        failed_then_index: usize,
        failed_then: VerifyFactResult,
        local_env: Box<ExecEnv>,
    },
}

impl VerifyForallFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// Dom: assume (WD + store), do not prove truth.
pub struct AssumeDomFactResult {
    pub well_defined: FactWellDefinedProof,
    pub store_and_infer: StoreFactAndInferResult,
}

// Then: prove, then local-store (option 2).
pub struct ProveAndStoreThenFactResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer: StoreFactAndInferResult,
}

pub fn forall_fact_result_from_success(
    fact: &ForallFact,
    introduced_params: IntroduceTypedParametersResult,
    assumed_dom_facts: Vec<AssumeDomFactResult>,
    proved_then_facts: Vec<ProveAndStoreThenFactResult>,
    local_env: Box<ExecEnv>,
) -> VerifyFactResult {
    VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult::Success(
        VerifyForallFactSuccess {
            fact: fact.clone(),
            introduced_params,
            assumed_dom_facts,
            proved_then_facts,
            local_env,
        },
    )))
}

pub fn forall_fact_result_from_wd_fail(
    reason: FailToVerifyForallFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult::Failed(
        VerifyForallFactFailed::FailToVerifyWellDefined(reason),
    )))
}

pub fn forall_fact_result_from_then_fail(
    fact: &ForallFact,
    introduced_params: IntroduceTypedParametersResult,
    assumed_dom_facts: Vec<AssumeDomFactResult>,
    proved_then_facts: Vec<ProveAndStoreThenFactResult>,
    failed_then_index: usize,
    failed_then: VerifyFactResult,
    local_env: Box<ExecEnv>,
) -> VerifyFactResult {
    VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult::Failed(
        VerifyForallFactFailed::FailToSearchProof {
            fact: fact.clone(),
            introduced_params,
            assumed_dom_facts,
            proved_then_facts,
            failed_then_index,
            failed_then,
            local_env,
        },
    )))
}
