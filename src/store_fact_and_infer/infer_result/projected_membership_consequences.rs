use crate::ast::fact::InFact;
use crate::store_fact_and_infer::InferInFactResult;

/// Consequences of one freshly stored positive membership, in execution order.
pub struct ProjectedMembershipConsequences {
    pub membership: InFact,
    pub inferences: Vec<InferInFactResult>,
}
