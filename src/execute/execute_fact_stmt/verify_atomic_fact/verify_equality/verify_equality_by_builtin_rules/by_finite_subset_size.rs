use crate::ast::fact::{EqualFact, Fact};
use crate::ast::obj::{FiniteSetSize, FiniteSetStat, Obj};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

pub struct FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
    pub left_finite_proof: VerifyFactResult,
    pub right_finite_proof: VerifyFactResult,
    pub subset_proof: VerifyFactResult,
    pub size_equal_proof: VerifyFactResult,
}

impl Runtime {
    // Finite inclusion is faithful: A ⊆ B and |A| = |B| imply A = B.
    // Both inclusion directions are tried because equality is symmetric.
    // Example: finite A,B; A $subset B; equal sizes => A = B (or B = A).
    pub(super) fn search_equal_fact_builtin_rule_finite_subset_size(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetEqualFromSubsetSizeBuiltinRuleProof>> {
        let child = verify_state.after_builtin_rule();
        let left_finite_proof = self.verify_is_finite_set(&fact.left, child.clone())?;
        if left_finite_proof.is_failed() { return Ok(None); }
        let right_finite_proof = self.verify_is_finite_set(&fact.right, child.clone())?;
        if right_finite_proof.is_failed() { return Ok(None); }
        for (lower, upper) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let subset_proof = self.verify_subset(lower, upper, child.clone())?;
            if subset_proof.is_failed() { continue; }
            let size_equal: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                    set: Box::new(lower.clone()),
                })),
                right: Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                    set: Box::new(upper.clone()),
                })),
                line_file: fact.line_file.clone(),
            }.into();
            let size_equal_proof = self.verify_fact(&size_equal, child.clone())?;
            if size_equal_proof.is_failed() { continue; }
            return Ok(Some(FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
                left_finite_proof,
                right_finite_proof,
                subset_proof,
                size_equal_proof,
            }));
        }
        Ok(None)
    }
}
