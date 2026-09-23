use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, InFact, LessFact};
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Literal, Number, Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferEqualFactPositiveRealPowerResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: stored `a^x = y` (or swapped) with `0 < a` and `x $in R` known/provable.
    // Infers: `y $in R+` (positive base to a real power is positive).
    // Example: `have a R+`, `have x R`, `trust a^x = y` ⇒ `y $in R+`.
    pub(super) fn infer_equal_fact_positive_real_power(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Option<InferEqualFactPositiveRealPowerResult>> {
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        if let Some(r) = self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.left,
            &equal_fact.right,
            equal_fact,
        )? {
            derived.push(r);
        }
        if let Some(r) = self.infer_positive_real_power_membership_to_equal_side(
            &equal_fact.right,
            &equal_fact.left,
            equal_fact,
        )? {
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
    ) -> RuntimeResult<Option<StoreFactAndInferResult>> {
        if maybe_power.ir() == target.ir() {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) = maybe_power else {
            return Ok(None);
        };
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: false,
        };
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let base_positive = AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero,
            right: pow.base.as_ref().clone(),
            line_file: equal_fact.line_file.clone(),
        });
        if self
            .verify_atomic_fact(&base_positive, verify_state.clone())?
            .is_failed()
        {
            return Ok(None);
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
            self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(target_in_r_pos))?
        else {
            return Ok(None);
        };
        Ok(Some(stored))
    }
}
