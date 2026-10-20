use super::InferInFactResult;
use crate::ast::fact::InFact;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

/// Definition conversion, direct stores of the converted memberships, then
/// exactly one ordinary inference pass on the native carrier. Consequences of
/// that pass are store-only, just as when the native carrier was written out.
pub struct InferTemplateMembershipResult {
    pub source_fact_id: FactId,
    pub expansions: Vec<InFact>,
    pub stores: Vec<StoreInferredFactResult>,
    pub native_rules: Vec<InferInFactResult>,
}
