use super::order_complement::FromKnownOrderComplementBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{AtomicFact, Fact, GreaterFact, InFact};
use crate::ast::obj::{
    Add, ArithmeticOperator, Literal, Mul, Number, Obj, StandardSet,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `a > b`.
pub enum GreaterFactSearchProofByBuiltinRule {
    FromKnownOrderComplement(FromKnownOrderComplementBuiltinRuleProof),
    // Closed numeric comparison by evaluation.
    // Mathematical property: if both sides evaluate to decimals L, R with L > R,
    // then `left > right`.
    // Examples: `2 > 1`, `5 > 1 + 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Strict order dual: known `b < a` proves `a > b`.
    // Mathematical property: `>` is the converse of `<`.
    // Example: known `x < 0` proves `0 > x`.
    FromKnownLess(FromKnownLessBuiltinRuleProof),
    // Right addend congruence (strict): `a > b` ⇒ `a + c > b + c`.
    // Example: known `x > y` proves `x + 1 > y + 1`.
    AddRightCongruenceStrict(AddRightCongruenceStrictBuiltinRuleProof),
    // Left addend congruence (strict): `a > b` ⇒ `c + a > c + b`.
    // Example: known `x > y` proves `1 + x > 1 + y`.
    AddLeftCongruenceStrict(AddLeftCongruenceStrictBuiltinRuleProof),
    // Left multiplication by a positive factor preserves strict order.
    // Mathematical property: `0 < k` and `a > b` ⇒ `k * a > k * b`.
    // Example: known `0 < 2` and `x > y` prove `2 * x > 2 * y`.
    MulLeftPositiveMonotoneStrict(MulLeftPositiveMonotoneStrictBuiltinRuleProof),
    // Right multiplication by a positive factor preserves strict order.
    // Example: known `0 < c` and `a > b` prove `a * c > b * c`.
    MulRightPositiveMonotoneStrict(MulRightPositiveMonotoneStrictBuiltinRuleProof),
    // Positive-real membership implies strict positivity.
    // Mathematical property: `x $in R+` ⇒ `x > 0`.
    // Example: prove `e > 0` from `e $in R+`.
    FromPositiveRealMembership(FromPositiveRealMembershipBuiltinRuleProof),
    // Native Euler constant is strictly positive: `e > 0`.
    NativeEulerGreaterZero(NativeEulerGreaterZeroBuiltinRuleProof),
    // Native Pi constant is strictly positive: `pi > 0`.
    NativePiGreaterZero(NativePiGreaterZeroBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {
    pub left_normal: String,
    pub right_normal: String,
}

pub struct FromKnownLessBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

pub struct AddRightCongruenceStrictBuiltinRuleProof {
    pub premise_proof: VerifyFactResult,
}

pub struct AddLeftCongruenceStrictBuiltinRuleProof {
    pub premise_proof: VerifyFactResult,
}

pub struct MulLeftPositiveMonotoneStrictBuiltinRuleProof {
    pub positive_factor_proof: VerifyFactResult,
    pub order_premise_proof: VerifyFactResult,
}

pub struct MulRightPositiveMonotoneStrictBuiltinRuleProof {
    pub positive_factor_proof: VerifyFactResult,
    pub order_premise_proof: VerifyFactResult,
}

pub struct FromPositiveRealMembershipBuiltinRuleProof {
    pub membership_proof: VerifyFactResult,
}

pub struct NativeEulerGreaterZeroBuiltinRuleProof {}

pub struct NativePiGreaterZeroBuiltinRuleProof {}

impl Runtime {
    // Builtin: known strict less dual, add/mul congruence, R+ membership, native e/pi, then closed decimal.
    // Example: prove `0 > x` from known `x < 0`, or prove `a + c > b + c` from `a > b`.
    pub fn search_greater_fact_proof_by_builtin_rule(
        &mut self,
        fact: &GreaterFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.known_order_complement(fact.clone().into(), verify_state.clone())? {
            return Ok(Some(GreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof)));
        }
        if let Some(premise_proof) = self.known_less_proof(&fact.right, &fact.left) {
            return Ok(Some(GreaterFactSearchProofByBuiltinRule::FromKnownLess(
                FromKnownLessBuiltinRuleProof { premise_proof },
            )));
        }
        if is_zero_obj(&fact.right) {
            if matches!(&fact.left, Obj::Literal(crate::ast::obj::Literal::EulerNumber(_))) {
                return Ok(Some(
                    GreaterFactSearchProofByBuiltinRule::NativeEulerGreaterZero(
                        NativeEulerGreaterZeroBuiltinRuleProof {},
                    ),
                ));
            }
            if matches!(&fact.left, Obj::Literal(crate::ast::obj::Literal::Pi(_))) {
                return Ok(Some(
                    GreaterFactSearchProofByBuiltinRule::NativePiGreaterZero(
                        NativePiGreaterZeroBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(proof) = self.greater_from_positive_real_membership_proof(
                &fact.left,
                verify_state.clone(),
            )? {
                return Ok(Some(proof));
            }
        }
        match (&fact.left, &fact.right) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: left_l,
                    right: left_r,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: right_l,
                    right: right_r,
                })),
            ) => {
                if left_r.as_ref().ir() == right_r.as_ref().ir() {
                    if let Some(proof) = self.greater_add_right_congruence_strict_proof(
                        left_l.as_ref(),
                        right_l.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
                if left_l.as_ref().ir() == right_l.as_ref().ir() {
                    if let Some(proof) = self.greater_add_left_congruence_strict_proof(
                        left_r.as_ref(),
                        right_r.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
            }
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: left_l,
                    right: left_r,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: right_l,
                    right: right_r,
                })),
            ) => {
                if left_l.as_ref().ir() == right_l.as_ref().ir() {
                    if let Some(proof) = self.greater_mul_left_positive_monotone_strict_proof(
                        left_l.as_ref(),
                        left_r.as_ref(),
                        right_r.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
                if left_r.as_ref().ir() == right_r.as_ref().ir() {
                    if let Some(proof) = self.greater_mul_right_positive_monotone_strict_proof(
                        left_r.as_ref(),
                        left_l.as_ref(),
                        right_l.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
            }
            _ => {}
        }
        let Some((cmp, left_normal, right_normal)) =
            compare_closed_objs_by_normalized_decimal(&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if cmp != NumberCompareResult::Greater {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(
                ClosedNumericComparisonBuiltinRuleProof {
                    left_normal,
                    right_normal,
                },
            ),
        ))
    }

    fn greater_add_right_congruence_strict_proof(
        &mut self,
        left_l: &Obj,
        right_l: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let premise = Fact::AtomicFact(AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_l.clone(),
            right: right_l.clone(),
            line_file: None,
        }));
        let premise_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::AddRightCongruenceStrict(
                AddRightCongruenceStrictBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    fn greater_add_left_congruence_strict_proof(
        &mut self,
        left_r: &Obj,
        right_r: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let premise = Fact::AtomicFact(AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_r.clone(),
            right: right_r.clone(),
            line_file: None,
        }));
        let premise_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::AddLeftCongruenceStrict(
                AddLeftCongruenceStrictBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    fn greater_mul_left_positive_monotone_strict_proof(
        &mut self,
        k: &Obj,
        left_a: &Obj,
        right_b: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let positive_factor_proof = self.verify_positive(k, verify_state.clone())?;
        if positive_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = Fact::AtomicFact(AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_a.clone(),
            right: right_b.clone(),
            line_file: None,
        }));
        let order_premise_proof = self.verify_builtin_rule_premise(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::MulLeftPositiveMonotoneStrict(
                MulLeftPositiveMonotoneStrictBuiltinRuleProof {
                    positive_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    fn greater_mul_right_positive_monotone_strict_proof(
        &mut self,
        k: &Obj,
        left_a: &Obj,
        right_b: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let positive_factor_proof = self.verify_positive(k, verify_state.clone())?;
        if positive_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = Fact::AtomicFact(AtomicFact::GreaterFact(GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_a.clone(),
            right: right_b.clone(),
            line_file: None,
        }));
        let order_premise_proof = self.verify_builtin_rule_premise(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::MulRightPositiveMonotoneStrict(
                MulRightPositiveMonotoneStrictBuiltinRuleProof {
                    positive_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    fn greater_from_positive_real_membership_proof(
        &mut self,
        left: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let premise = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: left.clone(),
            set: Obj::StandardSet(StandardSet::RPos),
            line_file: None,
        }));
        let membership_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if membership_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterFactSearchProofByBuiltinRule::FromPositiveRealMembership(
                FromPositiveRealMembershipBuiltinRuleProof { membership_proof },
            ),
        ))
    }
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}
