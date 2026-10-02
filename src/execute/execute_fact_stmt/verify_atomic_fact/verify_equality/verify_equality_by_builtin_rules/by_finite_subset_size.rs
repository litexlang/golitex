use crate::ast::fact::{EqualFact, Fact, SubsetFact};
use crate::ast::obj::{FiniteSetSize, FiniteSetStat, Obj};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

pub struct FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
    pub size_equal_proof: VerifyFactResult,
    pub subset_proof: VerifyFactResult,
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
        let child = verify_state.clone();
        // The checked cardinality equality carries both finite-set WD proofs.
        // Requiring separately stored is_finite facts would lose compositions
        // where finiteness was proved inside the cardinality object's WD.
        let size_equal: Fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                set: Box::new(fact.left.clone()),
            })),
            right: Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                set: Box::new(fact.right.clone()),
            })),
            line_file: fact.line_file.clone(),
        }
        .into();
        let size_equal_proof = self.verify_builtin_rule_premise(&size_equal, child.clone())?;
        if size_equal_proof.is_failed() {
            return Ok(None);
        }
        for (lower, upper) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let subset: Fact = SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: lower.clone(),
                right: upper.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let subset_proof = self.verify_builtin_rule_premise(&subset, child.clone())?;
            if subset_proof.is_failed() {
                continue;
            }
            return Ok(Some(FiniteSetEqualFromSubsetSizeBuiltinRuleProof {
                size_equal_proof,
                subset_proof,
            }));
        }
        Ok(None)
    }
}
