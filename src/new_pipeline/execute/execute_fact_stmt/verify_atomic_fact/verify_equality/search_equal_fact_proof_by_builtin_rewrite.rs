use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin rewrite for EqualFact.
//
// Replaces legacy opaque `Runtime::resolve_obj`: any object change must be an
// explicit rewrite step with cites in the Result, not a silent pre-processing.
//
// Mathematical idea (future): rewrite left and/or right by substituting known
// equalities under a common context, then the remaining goal is proved by an
// earlier stage (e.g. Calculation).
//
// Example (future, not wired yet):
//   known `a = 1`
//   goal  `a + 1 = 2`
//   rewrite left `a + 1` → `1 + 1`, then Calculation proves `1 + 1 = 2`.
//
// Search currently always returns None.
pub enum EqualitySearchProofByBuiltinRewrite {
    CongruenceSubstitution(CongruenceSubstitutionBuiltinRewriteProof),
}

// Placeholder payload for congruence substitution.
// When wired: rewritten sides + cited generating EqualFact ids.
pub struct CongruenceSubstitutionBuiltinRewriteProof {
    pub rewritten_left: Obj,
    pub rewritten_right: Obj,
    pub cited_equal_fact_ids: Vec<FactId>,
}

impl Runtime {
    // Placeholder search for equality builtin rewrite.
    // See EqualitySearchProofByBuiltinRewrite.
    pub fn search_equal_fact_proof_by_builtin_rewrite(
        &mut self,
        _fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRewrite>> {
        Ok(None)
    }
}
