use super::less_equal::{
    LessEqualFactSearchProofByBuiltinRule, PositiveCommonDivisorLeGcdBuiltinRuleProof,
};
use crate::ast::fact::{DvdFact, Fact, InFact, LessEqualFact};
use crate::ast::obj::{IntegerOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // A positive common integer divisor is at most the positive greatest common
    // divisor. Outer fact WD already checks integer inputs and excludes (0,0).
    // Example: d in N+, $dvd(a,d), $dvd(b,d) imply d <= gcd(a,b).
    pub(super) fn positive_common_divisor_le_gcd_proof(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Obj::IntegerOperator(IntegerOperator::Gcd(gcd)) = &fact.right else {
            return Ok(None);
        };
        let positive = Fact::from(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.left.clone(),
            set: Obj::StandardSet(StandardSet::NPos),
            line_file: fact.line_file.clone(),
        });
        let divisor_in_n_pos_proof = self.verify_builtin_rule_premise(&positive, state)?;
        if divisor_in_n_pos_proof.is_failed() {
            return Ok(None);
        }
        let left = Fact::from(DvdFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *gcd.left.clone(),
            right: fact.left.clone(),
            line_file: fact.line_file.clone(),
        });
        let left_divisibility_proof = self.verify_builtin_rule_premise(&left, state)?;
        if left_divisibility_proof.is_failed() {
            return Ok(None);
        }
        let right = Fact::from(DvdFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *gcd.right.clone(),
            right: fact.left.clone(),
            line_file: fact.line_file.clone(),
        });
        let right_divisibility_proof = self.verify_builtin_rule_premise(&right, state)?;
        if right_divisibility_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::PositiveCommonDivisorLeGcd(
                PositiveCommonDivisorLeGcdBuiltinRuleProof {
                    divisor_in_n_pos_proof,
                    left_divisibility_proof,
                    right_divisibility_proof,
                },
            ),
        ))
    }
}
