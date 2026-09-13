use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;


pub enum NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite {
    OrderDual(NonEquationalAtomicFactSearchProofByBuiltinOrderDual),
}

pub struct NonEquationalAtomicFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}
