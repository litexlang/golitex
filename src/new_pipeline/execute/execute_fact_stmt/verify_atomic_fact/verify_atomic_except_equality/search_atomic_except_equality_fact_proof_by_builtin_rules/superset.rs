use crate::new_pipeline::ast::fact::SupersetFact;
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::subset::standard_set_is_subset_eq;

// Standard number sets form a fixed inclusion chain.
// Example: prove `R $supset N`, `Q $supset Z`.
//
// Every set is a superset of itself.
// Example: prove `A $supset A`.
pub enum SupersetFactSearchProofByBuiltinRule {
    StandardSetSuperset(StandardSetSupersetBuiltinRuleProof),
    SupersetReflexivity(SupersetReflexivityBuiltinRuleProof),
}

pub struct StandardSetSupersetBuiltinRuleProof {
    pub left: StandardSet,
    pub right: StandardSet,
}

pub struct SupersetReflexivityBuiltinRuleProof {}

impl Runtime {
    // Builtin: zero-premise superset rules for standard sets and reflexivity.
    // Example: prove `R $supset N`, `A $supset A`.
    pub fn search_superset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &SupersetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SupersetFactSearchProofByBuiltinRule>> {
        let _ = verify_state;
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) = (&fact.left, &fact.right) {
            if standard_set_is_subset_eq(right, left) {
                return Ok(Some(
                    SupersetFactSearchProofByBuiltinRule::StandardSetSuperset(
                        StandardSetSupersetBuiltinRuleProof {
                            left: left.clone(),
                            right: right.clone(),
                        },
                    ),
                ));
            }
        }

        if fact.left == fact.right {
            return Ok(Some(
                SupersetFactSearchProofByBuiltinRule::SupersetReflexivity(
                    SupersetReflexivityBuiltinRuleProof {},
                ),
            ));
        }

        Ok(None)
    }
}
