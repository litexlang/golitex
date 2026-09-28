use crate::ast::fact::NotIsNonemptySetFact;
use crate::ast::obj::{Obj, SetFormer};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// The empty list set is not nonempty.
// Example: prove `not $is_nonempty_set({})`.
pub enum NotIsNonemptySetFactSearchProofByBuiltinRule {
    EmptyListSet(EmptyListSetNotNonemptyBuiltinRuleProof),
}

pub struct EmptyListSetNotNonemptyBuiltinRuleProof {}

impl Runtime {
    // Builtin: `{}` is empty, so it is not a nonempty set.
    // Example: prove `not $is_nonempty_set({})`.
    pub fn search_not_is_nonempty_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotIsNonemptySetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsNonemptySetFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::SetFormer(SetFormer::ListSet(list_set)) if list_set.list.is_empty() => Ok(Some(
                NotIsNonemptySetFactSearchProofByBuiltinRule::EmptyListSet(
                    EmptyListSetNotNonemptyBuiltinRuleProof {},
                ),
            )),
            _ => Ok(None),
        }
    }
}
