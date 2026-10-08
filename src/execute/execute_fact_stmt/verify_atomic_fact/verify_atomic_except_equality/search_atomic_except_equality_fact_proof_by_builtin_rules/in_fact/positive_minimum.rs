//! A minimum of two checked positive real operands is positive.
use crate::prelude::*;
use super::InFactSearchProofByBuiltinRule;
use super::super::helper::{binary_extremum_operands, BinaryExtremumKind};

pub struct MinPreservesPositiveCarrierProof {
    pub left_positive: VerifyFactResult,
    pub right_positive: VerifyFactResult,
}
impl MinPreservesPositiveCarrierProof {
    pub fn new(left_positive: VerifyFactResult, right_positive: VerifyFactResult) -> Self {
        Self { left_positive, right_positive }
    }
}

impl Runtime {
    pub(super) fn search_positive_minimum(
        &mut self,
        fact: &InFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        if !matches!(&fact.set, Obj::StandardSet(StandardSet::RPos)) { return Ok(None); }
        let Some((BinaryExtremumKind::Minimum, left, right)) = binary_extremum_operands(&fact.element)
        else { return Ok(None); };
        // Example: have a,b R+; have delta R+ = min(a,b).
        // Both refinements are required; no recursive min typing is started.
        let premise: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: left.clone(),
            set: fact.set.clone(), line_file: fact.line_file.clone(),
        }.into();
        let left_positive = self.verify_builtin_rule_premise(&premise, state)?;
        if left_positive.is_failed() { return Ok(None); }
        let premise: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: right.clone(),
            set: fact.set.clone(), line_file: fact.line_file.clone(),
        }.into();
        let right_positive = self.verify_builtin_rule_premise(&premise, state)?;
        if right_positive.is_failed() { return Ok(None); }
        Ok(Some(InFactSearchProofByBuiltinRule::MinPreservesPositiveCarrier(
            MinPreservesPositiveCarrierProof::new(left_positive, right_positive))))
    }
}
