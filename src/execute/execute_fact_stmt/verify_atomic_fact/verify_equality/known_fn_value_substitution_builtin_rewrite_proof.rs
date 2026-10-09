use crate::prelude::*;

// A single original-tree substitution followed by checked residual equality.
// Each cited equation has an original FnObj as one exact endpoint; citations
// are unique in left-to-right traversal order. No inserted value is revisited.
pub struct KnownFnValueSubstitutionBuiltinRewriteProof {
    pub rewritten_left: Obj,
    pub rewritten_right: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    pub residual_equal: VerifyFactResult,
}

impl KnownFnValueSubstitutionBuiltinRewriteProof {
    pub fn new(
        rewritten_left: Obj,
        rewritten_right: Obj,
        cited_equal_fact_ids: Vec<FactId>,
        residual_equal: VerifyFactResult,
    ) -> Self {
        Self {
            rewritten_left,
            rewritten_right,
            cited_equal_fact_ids,
            residual_equal,
        }
    }
}
