use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;


pub enum NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2 {
    OrderDual(NonEquationalAtomicFactSearchProofByBuiltinOrderDual2),
}

pub struct NonEquationalAtomicFactSearchProofByBuiltinOrderDual2 {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult2,
}
