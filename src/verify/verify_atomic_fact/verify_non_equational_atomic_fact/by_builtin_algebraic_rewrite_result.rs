use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

use crate::verify_rewrite::FactStmt;

pub enum NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite {
    OrderDual(NonEquationalAtomicFactSearchProofByBuiltinOrderDual),
}

pub struct NonEquationalAtomicFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: FactStmt,
    pub proof_of_alternate_fact: VerifyFactResult,
}
