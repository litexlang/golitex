use crate::new_pipeline::ast::fact::IsFiniteSetFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// These constructors carry finiteness intrinsically.
// Example: prove `$is_finite_set({1, 2})`, `$is_finite_set(closed_range(1, n))`.
pub enum IsFiniteSetFactSearchProofByBuiltinRule {
    ListSet(ListSetFiniteBuiltinRuleProof),
    ClosedRange(ClosedRangeFiniteBuiltinRuleProof),
    Range(RangeFiniteBuiltinRuleProof),
}

pub struct ListSetFiniteBuiltinRuleProof {}

pub struct ClosedRangeFiniteBuiltinRuleProof {}

pub struct RangeFiniteBuiltinRuleProof {}

impl Runtime {
    // Builtin: list sets and integer ranges are finite by construction.
    // Example: prove `$is_finite_set({1, 2})`, `$is_finite_set(1...n)`.
    pub fn search_is_finite_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &IsFiniteSetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsFiniteSetFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::ListSet(_) => Ok(Some(IsFiniteSetFactSearchProofByBuiltinRule::ListSet(
                ListSetFiniteBuiltinRuleProof {},
            ))),
            Obj::ClosedRange(_) => Ok(Some(IsFiniteSetFactSearchProofByBuiltinRule::ClosedRange(
                ClosedRangeFiniteBuiltinRuleProof {},
            ))),
            Obj::Range(_) => Ok(Some(IsFiniteSetFactSearchProofByBuiltinRule::Range(
                RangeFiniteBuiltinRuleProof {},
            ))),
            _ => Ok(None),
        }
    }
}
