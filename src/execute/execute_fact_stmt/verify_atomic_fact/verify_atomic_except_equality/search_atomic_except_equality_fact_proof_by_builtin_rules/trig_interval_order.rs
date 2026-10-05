//! Strict sine order on its standard intervals.
use super::less::LessFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, LessEqualFact, LessFact};
use crate::ast::obj::{Obj, TrigOperator};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{half_pi, negative_half_pi, pi_obj, zero_obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct SinPositiveOnOpenPiProof {
    pub lower_bound: VerifyFactResult,
    pub upper_bound: VerifyFactResult,
}

pub struct SinStrictMonotoneOnHalfPiProof {
    pub left_lower_bound: VerifyFactResult,
    pub right_upper_bound: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_sin_interval_order(
        &mut self,
        fact: &LessFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if fact.left.ir() == zero_obj().ir() {
            if let Obj::TrigOperator(TrigOperator::Sin(sin)) = &fact.right {
                // Example: 0<x<pi => 0<sin(x); endpoints are excluded.
                let lower: Fact = LessFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: zero_obj(),
                    right: *sin.arg.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let lower_bound = self.verify_builtin_rule_premise(&lower, state)?;
                if lower_bound.is_failed() {
                    return Ok(None);
                }
                let upper: Fact = LessFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: *sin.arg.clone(),
                    right: pi_obj(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let upper_bound = self.verify_builtin_rule_premise(&upper, state)?;
                if upper_bound.is_failed() {
                    return Ok(None);
                }
                return Ok(Some(LessFactSearchProofByBuiltinRule::SinPositiveOnOpenPi(
                    SinPositiveOnOpenPiProof {
                        lower_bound,
                        upper_bound,
                    },
                )));
            }
        }
        let (Obj::TrigOperator(TrigOperator::Sin(a)), Obj::TrigOperator(TrigOperator::Sin(b))) =
            (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        // Example: -pi/2<=a<b<=pi/2 => sin(a)<sin(b), including endpoints.
        let lower: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: negative_half_pi(),
            right: *a.arg.clone(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let left_lower_bound = self.verify_builtin_rule_premise(&lower, state)?;
        if left_lower_bound.is_failed() {
            return Ok(None);
        }
        let upper: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *b.arg.clone(),
            right: half_pi(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let right_upper_bound = self.verify_builtin_rule_premise(&upper, state)?;
        if right_upper_bound.is_failed() {
            return Ok(None);
        }
        let order: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *a.arg.clone(),
            right: *b.arg.clone(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let argument_order = self.verify_builtin_rule_premise(&order, state)?;
        if argument_order.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::SinStrictMonotoneOnHalfPi(
                SinStrictMonotoneOnHalfPiProof {
                    left_lower_bound,
                    right_upper_bound,
                    argument_order,
                },
            ),
        ))
    }
}
