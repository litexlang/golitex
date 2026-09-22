use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::runtime_ids::FactId;

// Builtin rewrite for EqualFact.
//
// Why this stage exists:
//   Calculation (and similar builtins) only fire on closed numeric trees.
//   After `have a R = 10`, the goal may still mention `a` (not closed). This
//   rewrite substitutes known_closed_numeric_equal representatives into the
//   goal, then proves the residual with rewrite off — an explicit certificate
//   instead of legacy opaque resolve_obj.
//
// Allowed here: only ClosedNumericEqualSubstitution (see `ClosedNumericExpr`
// for what "closed numeric" means). No general known-equality subterm rewrite.
// Constructor-wise / pointwise equality belongs elsewhere, not in rewrite.
//
// Dispatcher: `search_equal_fact_proof_by_builtin_rewrite`.
pub enum EqualitySearchProofByBuiltinRewrite {
    ClosedNumericEqualSubstitution(ClosedNumericEqualSubstitutionBuiltinRewriteProof),
}

// Closed-numeric index substitution: a non-closed object indexed under
// known_closed_numeric_equal is rewritten to its `ClosedNumericExpr` representative
// (including as a subterm), then the residual equality is proved without rewrite.
// Mathematical property: if `a = closed` is known and indexed, then F[a] = F[closed]
// for supported F. All matching entries in the goal are applied in one step.
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
