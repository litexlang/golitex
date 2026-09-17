use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

// Shared known-forall application certificate (equality and non-equality).
// `cite` is the same handle as in KnownForallConclusionMemory.
pub struct SearchProofByKnownForallFact {
    pub cite: crate::new_pipeline::exec_env::ForallConclusionCite,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
