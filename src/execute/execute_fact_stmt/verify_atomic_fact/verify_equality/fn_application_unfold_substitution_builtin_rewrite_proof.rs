use super::by_object_definition::by_fn_application::normalize_function_body::AnonymousFunctionBodyExpansionProof;
use crate::prelude::*;

// Each source is an actual stored head-to-anonymous-function equality.
// Checked beta steps in original left-to-right scalar-tree order. Each
// outermost call is visited once; inserted bodies and call arguments are leaves.
pub struct FnApplicationUnfoldSubstitutionBuiltinRewriteProof {
    pub expansions: Vec<AnonymousFunctionBodyExpansionProof>,
    pub rewritten_left: Obj,
    pub rewritten_right: Obj,
    pub residual_equal: VerifyFactResult,
}

impl FnApplicationUnfoldSubstitutionBuiltinRewriteProof {
    pub fn new(
        expansions: Vec<AnonymousFunctionBodyExpansionProof>,
        rewritten_left: Obj,
        rewritten_right: Obj,
        residual_equal: VerifyFactResult,
    ) -> Self {
        Self {
            expansions,
            rewritten_left,
            rewritten_right,
            residual_equal,
        }
    }
}
