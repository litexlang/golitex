//! Saved real difference/order bridges. No recursive premise search or publication.
use super::less::{
    LessFactSearchProofByBuiltinRule, LessFromNegativeDifferenceBuiltinRuleProof,
    NegativeDifferenceFromLessBuiltinRuleProof,
};
use super::less_equal::{
    is_zero_obj, zero_obj, LessEqualFactSearchProofByBuiltinRule,
    LessEqualFromNonpositiveDifferenceBuiltinRuleProof,
    NonpositiveDifferenceFromLessEqualBuiltinRuleProof,
};
use super::order_div_mod_bridge_trans::sub_obj;
use crate::ast::fact::{LessEqualFact, LessFact};
use crate::ast::obj::{ArithmeticOperator, Literal, Mul, Neg, Number, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::runtime::{Runtime, RuntimeResult};

// These are fixed spellings of 0-u, not an algebraic normalizer.
pub(super) fn difference_spellings(left: &Obj, right: &Obj) -> Vec<Obj> {
    let mut forms = vec![sub_obj(left, right)];
    if is_zero_obj(left) {
        let minus_one = Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(Obj::Literal(Literal::Number(Number {
                normalized_value: "1".to_string(),
            }))),
        }));
        forms.push(Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(right.clone()),
        })));
        forms.push(Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(minus_one.clone()),
            right: Box::new(right.clone()),
        })));
        forms.push(Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(right.clone()),
            right: Box::new(minus_one),
        })));
    }
    forms
}

fn is_minus_one(obj: &Obj) -> bool {
    match obj {
        Obj::Literal(Literal::Number(n)) => n.normalized_value == "-1",
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) => {
            matches!(n.arg.as_ref(), Obj::Literal(Literal::Number(v)) if v.normalized_value == "1")
        }
        _ => false,
    }
}

pub(super) fn difference_parts(obj: &Obj) -> Option<(Obj, Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) => {
            Some((*s.left.clone(), *s.right.clone()))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) => Some((zero_obj(), *n.arg.clone())),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) if is_minus_one(&m.left) => {
            Some((zero_obj(), *m.right.clone()))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) if is_minus_one(&m.right) => {
            Some((zero_obj(), *m.left.clone()))
        }
        _ => None,
    }
}

impl Runtime {
    // Query only saved premises, canonical weak first; strict facts justify weak order.
    // Return the actual chosen comparison/citation, never fabricate its orientation.
    pub(super) fn known_signed_difference_order(
        &mut self,
        left: &Obj,
        right: &Obj,
        weak: bool,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        if weak {
            if let Some(p) = self.known_less_equal_proof(left, right) {
                return Some(p);
            }
            if let Some(p) = self.known_greater_equal_proof(right, left) {
                return Some(p);
            }
        }
        if let Some(p) = self.known_less_proof(left, right) {
            return Some(p);
        }
        self.known_greater_proof(right, left)
    }

    // a-b < 0 => a < b. Enclosing order WD already establishes real operands.
    pub(super) fn less_from_negative_difference_proof(
        &mut self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        for difference in difference_spellings(&fact.left, &fact.right) {
            if let Some(premise_proof) =
                self.known_signed_difference_order(&difference, &zero_obj(), false)
            {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::LessFromNegativeDifference(
                        LessFromNegativeDifferenceBuiltinRuleProof { premise_proof },
                    ),
                ));
            }
        }
        Ok(None)
    }

    // a < b => a-b < 0; also 0 < u => -u < 0.
    pub(super) fn negative_difference_from_less_proof(
        &mut self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if !is_zero_obj(&fact.right) {
            return Ok(None);
        }
        let Some((left, right)) = difference_parts(&fact.left) else {
            return Ok(None);
        };
        let Some(premise_proof) = self.known_signed_difference_order(&left, &right, false) else {
            return Ok(None);
        };
        Ok(Some(
            LessFactSearchProofByBuiltinRule::NegativeDifferenceFromLess(
                NegativeDifferenceFromLessBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    // a-b <= 0 (or < 0) => a <= b; a weak premise cannot prove strict order.
    pub(super) fn less_equal_from_nonpositive_difference_proof(
        &mut self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        for difference in difference_spellings(&fact.left, &fact.right) {
            if let Some(premise_proof) =
                self.known_signed_difference_order(&difference, &zero_obj(), true)
            {
                return Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonpositiveDifference(
                        LessEqualFromNonpositiveDifferenceBuiltinRuleProof { premise_proof },
                    ),
                ));
            }
        }
        Ok(None)
    }

    // a <= b (or a < b) => a-b <= 0; also 0 <= u => -u <= 0.
    pub(super) fn nonpositive_difference_from_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if !is_zero_obj(&fact.right) {
            return Ok(None);
        }
        let Some((left, right)) = difference_parts(&fact.left) else {
            return Ok(None);
        };
        let Some(premise_proof) = self.known_signed_difference_order(&left, &right, true) else {
            return Ok(None);
        };
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::NonpositiveDifferenceFromLessEqual(
                NonpositiveDifferenceFromLessEqualBuiltinRuleProof { premise_proof },
            ),
        ))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/signed_difference_order/tests.rs"]
mod signed_difference_order_tests;
