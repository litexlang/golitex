use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::prelude::*;

pub enum AtomicExceptEqualityFactSearchProofByBuiltinAlgebraicRewrite {
    OrderDual(AtomicExceptEqualityFactSearchProofByBuiltinOrderDual),
}

pub struct AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_builtin_algebraic_rewrite(
        &mut self,
        _fact: &AtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinAlgebraicRewrite>> {
        Ok(None)
    }
}
