use crate::prelude::*;
use crate::verify_rewrite::VerifyState;
use crate::verify_rewrite::FactStmt;

pub struct CacheSearchProof {
    pub fact: FactStmt,
    pub cite_fact_id: FactId,
}
