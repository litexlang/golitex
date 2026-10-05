use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, LessFact};
use crate::ast::obj::{ArithmeticOperator, Literal, Number, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferEqualFactPositiveRealPowerResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: stored `a^x = y` (or swapped) with checked positive real power.
    // Infers: `y $in R+`. First reuse bounded positivity rules for the power;
    // then retain the original positive-base/real-exponent route as fallback.
    // Example: `have a R*`, `have y R = a^2` ⇒ `y $in R+`.
    pub(super) fn infer_equal_fact_positive_real_power(
        &mut self,
        equal_fact: &EqualFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferEqualFactPositiveRealPowerResult>> {
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        if let Some(r) = self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact,
         verify_state)? {
            derived.push(r);
        }
        if let Some(r) = self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.right,
            &equal_fact.left,
            equal_fact,
         verify_state)? {
            derived.push(r);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferEqualFactPositiveRealPowerResult { derived }))
    }
}

impl Runtime {
    fn infer_positive_real_power_membership_to_equal_side(
        &mut self,
        maybe_power: &Obj,
        target: &Obj,
        equal_fact: &EqualFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<StoreFactAndInferResult>> {
        if maybe_power.ir() == target.ir() {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) = maybe_power else {
            return Ok(None);
        };
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let power_positive = AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero.clone(),
            right: maybe_power.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        // A real nonzero square is positive even when its base has unknown sign.
        // Reuse that existing builtin proof before searching for `0 < base`.
        if self
            .verify_atomic_fact(&power_positive, verify_state.capped_at(VerifyStateLevel::BuiltinRule))?
            .is_failed()
        {
            let base_positive = AtomicFact::LessFact(LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: zero,
                right: pow.base.as_ref().clone(),
                line_file: equal_fact.line_file.clone(),
            });
            if self.verify_atomic_fact(&base_positive, verify_state)?.is_failed() {
                return Ok(None);
            }
        }
        let exponent_in_r = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: pow.exponent.as_ref().clone(),
            set: Obj::StandardSet(StandardSet::R),
            line_file: equal_fact.line_file.clone(),
        });
        if self
            .verify_atomic_fact(&exponent_in_r, verify_state)?
            .is_failed()
        {
            return Ok(None);
        }
        let target_in_r_pos = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: target.clone(),
            set: Obj::StandardSet(StandardSet::RPos),
            line_file: equal_fact.line_file.clone(),
        });
        let Some(stored) =
            self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(target_in_r_pos), verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(stored))
    }
}
