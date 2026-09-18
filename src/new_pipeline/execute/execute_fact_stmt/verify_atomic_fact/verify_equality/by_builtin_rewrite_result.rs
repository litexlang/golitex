use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::runtime_ids::FactId;

// Builtin rewrite for EqualFact.
//
// Only ClosedNumericEqualSubstitution is allowed: rewrite toward a stored
// closed numeric representative. Do not add a general known-equality
// subterm substitution here (that is not congruence and is forbidden).
// True constructor-wise / pointwise equality belongs elsewhere, not in rewrite.
//
// Dispatcher: `search_equal_fact_proof_by_builtin_rewrite`.
pub enum EqualitySearchProofByBuiltinRewrite {
    ClosedNumericEqualSubstitution(ClosedNumericEqualSubstitutionBuiltinRewriteProof),
}

// Closed-numeric index substitution: a non-closed object indexed under
// ClosedNumericEqual is rewritten to its closed numeric representative
// (including as a subterm), then the residual equality is proved without rewrite.
// Mathematical property: congruence toward a stored closed numeric form —
// if `a = closed` is known and indexed, then F[a] = F[closed] for supported F.
// All matching ClosedNumericEqual entries that appear in the goal are applied
// together so multi-variable goals work in one rewrite step.
//
// Example:
//   have a R = 10
//   have b R = 20
//   a + b = 30
// rewrite both sides' `a`/`b` to 10/20, then Calculation proves `10 + 20 = 30`.
pub struct ClosedNumericEqualSubstitutionBuiltinRewriteProof {
    pub rewritten_left: Obj,
    pub rewritten_right: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
    // Prove rewritten_left = rewritten_right with can_use_rewrite = false.
    pub residual_equal: VerifyFactResult,
}
