use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;


pub enum NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2 {
    OrderDual(NonEquationalAtomicFactSearchProofByBuiltinOrderDual2),
}

pub struct NonEquationalAtomicFactSearchProofByBuiltinOrderDual2 {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult2,
}
