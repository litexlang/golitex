use crate::new_pipeline::ast::fact::IsNonemptySetFact;
use crate::new_pipeline::ast::obj::{Obj, StandardSet, SetFormer, SetOperator};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Standard numeric carriers are nonempty.
// Example: prove `$is_nonempty_set(R)`, `$is_nonempty_set(Q)`.
//
// A nonempty list set is nonempty by syntax.
// Example: prove `$is_nonempty_set({1, 2})`.
//
// Every power set is nonempty because it contains the empty set.
// Example: prove `$is_nonempty_set(power_set(Z))`.
//
// One-sided real rays are nonempty by construction.
// Example: prove `$is_nonempty_set('[a,))`.
pub enum IsNonemptySetFactSearchProofByBuiltinRule {
    StandardSetNonempty(StandardSetNonemptyBuiltinRuleProof),
    LiteralListSetNonempty(LiteralListSetNonemptyBuiltinRuleProof),
    PowerSetNonempty(PowerSetNonemptyBuiltinRuleProof),
    OneSideInfinityIntervalNonempty(OneSideInfinityIntervalNonemptyBuiltinRuleProof),
}

pub struct StandardSetNonemptyBuiltinRuleProof {
    pub target_set: StandardSet,
}

pub struct LiteralListSetNonemptyBuiltinRuleProof {}

pub struct PowerSetNonemptyBuiltinRuleProof {}

pub struct OneSideInfinityIntervalNonemptyBuiltinRuleProof {}

impl Runtime {
    // Builtin: zero-premise nonempty rules for standard sets, list sets,
    // power sets, and one-sided real rays.
    // Example: prove `$is_nonempty_set(R)`, `$is_nonempty_set({1})`, `$is_nonempty_set('[a,))`.
    pub fn search_is_nonempty_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &IsNonemptySetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsNonemptySetFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::StandardSet(target_set) => Ok(Some(
                IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty(
                    StandardSetNonemptyBuiltinRuleProof {
                        target_set: target_set.clone(),
                    },
                ),
            )),
            Obj::SetFormer(SetFormer::ListSet(list_set)) if !list_set.list.is_empty() => Ok(Some(
                IsNonemptySetFactSearchProofByBuiltinRule::LiteralListSetNonempty(
                    LiteralListSetNonemptyBuiltinRuleProof {},
                ),
            )),
            Obj::SetOperator(SetOperator::PowerSet(_)) => Ok(Some(
                IsNonemptySetFactSearchProofByBuiltinRule::PowerSetNonempty(
                    PowerSetNonemptyBuiltinRuleProof {},
                ),
            )),
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => Ok(Some(
                IsNonemptySetFactSearchProofByBuiltinRule::OneSideInfinityIntervalNonempty(
                    OneSideInfinityIntervalNonemptyBuiltinRuleProof {},
                ),
            )),
            _ => Ok(None),
        }
    }
}
