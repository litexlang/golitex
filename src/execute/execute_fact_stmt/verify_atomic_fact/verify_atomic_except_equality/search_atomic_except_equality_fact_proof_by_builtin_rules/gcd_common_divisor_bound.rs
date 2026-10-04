use crate::ast::fact::{EqualFact, Fact, InFact, LessEqualFact};
use crate::ast::obj::{IntegerOperator, Mod, Obj, StandardSet};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};
use super::less_equal::{zero_obj, LessEqualFactSearchProofByBuiltinRule, PositiveCommonDivisorLeGcdBuiltinRuleProof};

impl Runtime {
    // A positive common integer divisor is at most the positive greatest common
    // divisor. Outer fact WD already checks integer inputs and excludes (0,0).
    // Example: d in N+, a%d=0, b%d=0 imply d <= gcd(a,b).
    pub(super) fn positive_common_divisor_le_gcd_proof(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Obj::IntegerOperator(IntegerOperator::Gcd(gcd)) = &fact.right else { return Ok(None); };
        let positive = Fact::from(InFact { fact_id:self.global_ids.allocate_fact_id(), element:fact.left.clone(), set:Obj::StandardSet(StandardSet::NPos), line_file:fact.line_file.clone() });
        let divisor_in_n_pos_proof = self.verify_builtin_rule_premise(&positive, state)?;
        if divisor_in_n_pos_proof.is_failed() { return Ok(None); }
        let left = Fact::from(EqualFact { fact_id:self.global_ids.allocate_fact_id(), left:Obj::IntegerOperator(IntegerOperator::Mod(Mod { left:gcd.left.clone(), right:Box::new(fact.left.clone()) })), right:zero_obj(), line_file:fact.line_file.clone() });
        let left_remainder_zero_proof = self.verify_builtin_rule_premise(&left, state)?;
        if left_remainder_zero_proof.is_failed() { return Ok(None); }
        let right = Fact::from(EqualFact { fact_id:self.global_ids.allocate_fact_id(), left:Obj::IntegerOperator(IntegerOperator::Mod(Mod { left:gcd.right.clone(), right:Box::new(fact.left.clone()) })), right:zero_obj(), line_file:fact.line_file.clone() });
        let right_remainder_zero_proof = self.verify_builtin_rule_premise(&right, state)?;
        if right_remainder_zero_proof.is_failed() { return Ok(None); }
        Ok(Some(LessEqualFactSearchProofByBuiltinRule::PositiveCommonDivisorLeGcd(PositiveCommonDivisorLeGcdBuiltinRuleProof { divisor_in_n_pos_proof, left_remainder_zero_proof, right_remainder_zero_proof })))
    }
}
