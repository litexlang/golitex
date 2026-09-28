//! Stage B wave 6: abs/sign by sign, and ordered min/max equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, LessEqualFact};
use crate::new_pipeline::ast::obj::{
    Abs, ArithmeticOperator, Literal, Max, Min, Mul, Neg, Number, Obj, Sign, Sub,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// --- abs by sign ---

// Builtin AbsNonnegEqualsSelf: abs(a) = a when 0 <= a.
// Example: have a R+; abs(a) = a.
pub struct AbsNonnegEqualsSelfBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin AbsNonposEqualsNegation: abs(a) = 0 - a when a <= 0.
// Example: have a R; trust a <= 0; abs(a) = 0 - a.
pub struct AbsNonposEqualsNegationBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- sign ---

// Builtin SignOfPositive: sign(a) = 1 when 0 < a.
// Example: have a R+; sign(a) = 1.
pub struct SignOfPositiveBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SignOfNegative: sign(a) = 0 - 1 when a < 0.
// Example: have a R; trust a < 0; sign(a) = 0 - 1.
pub struct SignOfNegativeBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- ordered min / max ---

// Builtin MaxRightWhenLessEqual: max(a, b) = b when a <= b.
// Example: have a R; have b R; trust a <= b; max(a, b) = b.
pub struct MaxRightWhenLessEqualBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin MaxLeftWhenLessEqual: max(a, b) = a when b <= a.
// Example: have a R; have b R; trust b <= a; max(a, b) = a.
pub struct MaxLeftWhenLessEqualBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin MinLeftWhenLessEqual: min(a, b) = a when a <= b.
// Example: have a R; have b R; trust a <= b; min(a, b) = a.
pub struct MinLeftWhenLessEqualBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin MinRightWhenLessEqual: min(a, b) = b when b <= a.
// Example: have a R; have b R; trust b <= a; min(a, b) = b.
pub struct MinRightWhenLessEqualBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave6BuiltinRuleProof {
    AbsNonnegEqualsSelf(AbsNonnegEqualsSelfBuiltinRuleProof),
    AbsNonposEqualsNegation(AbsNonposEqualsNegationBuiltinRuleProof),
    SignOfPositive(SignOfPositiveBuiltinRuleProof),
    SignOfNegative(SignOfNegativeBuiltinRuleProof),
    MaxRightWhenLessEqual(MaxRightWhenLessEqualBuiltinRuleProof),
    MaxLeftWhenLessEqual(MaxLeftWhenLessEqualBuiltinRuleProof),
    MinLeftWhenLessEqual(MinLeftWhenLessEqualBuiltinRuleProof),
    MinRightWhenLessEqual(MinRightWhenLessEqualBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave6(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave6BuiltinRuleProof>> {
        let child = verify_state.without_well_defined_storage();
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(p) = self.try_abs_nonneg_equals_self(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave6BuiltinRuleProof::AbsNonnegEqualsSelf(p),
                ));
            }
            if let Some(p) = self.try_abs_nonpos_equals_negation(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave6BuiltinRuleProof::AbsNonposEqualsNegation(p),
                ));
            }
            if let Some(p) = self.try_sign_of_positive(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave6BuiltinRuleProof::SignOfPositive(
                    p,
                )));
            }
            if let Some(p) = self.try_sign_of_negative(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave6BuiltinRuleProof::SignOfNegative(
                    p,
                )));
            }
            if let Some(p) = self.try_max_right_when_less_equal(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave6BuiltinRuleProof::MaxRightWhenLessEqual(p),
                ));
            }
            if let Some(p) = self.try_max_left_when_less_equal(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave6BuiltinRuleProof::MaxLeftWhenLessEqual(p),
                ));
            }
            if let Some(p) = self.try_min_left_when_less_equal(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave6BuiltinRuleProof::MinLeftWhenLessEqual(p),
                ));
            }
            if let Some(p) = self.try_min_right_when_less_equal(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave6BuiltinRuleProof::MinRightWhenLessEqual(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_abs_nonneg_equals_self(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AbsNonnegEqualsSelfBuiltinRuleProof>> {
        let Some(arg) = match_abs(left) else {
            return Ok(None);
        };
        if arg.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonnegative(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(AbsNonnegEqualsSelfBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_abs_nonpos_equals_negation(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AbsNonposEqualsNegationBuiltinRuleProof>> {
        let Some(arg) = match_abs(left) else {
            return Ok(None);
        };
        let Some(inner) = match_negation(right) else {
            return Ok(None);
        };
        if arg.ir() != inner.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonpositive(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(AbsNonposEqualsNegationBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sign_of_positive(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SignOfPositiveBuiltinRuleProof>> {
        let Some(arg) = match_sign(left) else {
            return Ok(None);
        };
        if !is_one_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_positive(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(SignOfPositiveBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sign_of_negative(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SignOfNegativeBuiltinRuleProof>> {
        let Some(arg) = match_sign(left) else {
            return Ok(None);
        };
        if !is_neg_one_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_negative(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(SignOfNegativeBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_max_right_when_less_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<MaxRightWhenLessEqualBuiltinRuleProof>> {
        let Some((a, b)) = match_max(left) else {
            return Ok(None);
        };
        if b.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_less_equal(a, b, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(MaxRightWhenLessEqualBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_max_left_when_less_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<MaxLeftWhenLessEqualBuiltinRuleProof>> {
        let Some((a, b)) = match_max(left) else {
            return Ok(None);
        };
        if a.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_less_equal(b, a, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(MaxLeftWhenLessEqualBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_min_left_when_less_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<MinLeftWhenLessEqualBuiltinRuleProof>> {
        let Some((a, b)) = match_min(left) else {
            return Ok(None);
        };
        if a.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_less_equal(a, b, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(MinLeftWhenLessEqualBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_min_right_when_less_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<MinRightWhenLessEqualBuiltinRuleProof>> {
        let Some((a, b)) = match_min(left) else {
            return Ok(None);
        };
        if b.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_less_equal(b, a, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(MinRightWhenLessEqualBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn verify_less_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }
}

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_sign(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_min(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Min(Min { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_max(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Max(Max { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_negation(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) => Some(arg.as_ref()),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            Some(right.as_ref())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            if is_neg_one_obj(left.as_ref()) {
                Some(right.as_ref())
            } else if is_neg_one_obj(right.as_ref()) {
                Some(left.as_ref())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn is_neg_one_obj(obj: &Obj) -> bool {
    if let Some(inner) = match_negation(obj) {
        return is_one_obj(inner);
    }
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "-1"
    )
}
