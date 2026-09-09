use crate::prelude::*;

pub struct VerifyForallFactResult {
    pub fact: ForallFact,
    pub well_defined_proof: ForallFactWellDefinedProof,

    pub local_param_def_results: LocalParameterDefinitionResult,
    pub assumption_results: Vec<AssumptionResult>,

    pub local_env: Environment, // 在验证forall的时候，会开个局部环境，然后在里面做操作，我们把这个局部环境保留在result的，意义是，我们的searched_proof里可能会出现存在局部环境里的事实，这样我们就能知道它cite的是哪个事实了。
    pub verify_result_of_then_facts: Vec<VerifyFactResult>,
}

pub struct ForallFactSearchedProof {
    pub proof_of_each_then_fact: Vec<VerifyFactResult>,
}
