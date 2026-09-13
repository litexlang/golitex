use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;

pub struct CacheSearchProof {
    pub fact: Fact,
    pub cite_fact_id: FactId,
}
