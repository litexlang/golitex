use super::ForallFact;
use crate::new_pipeline::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotForallFact {
    pub fact_id: FactId,
    pub forall_fact: ForallFact,
}
