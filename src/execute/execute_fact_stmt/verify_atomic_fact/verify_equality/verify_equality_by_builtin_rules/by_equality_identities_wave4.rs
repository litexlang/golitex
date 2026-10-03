//! Stage B wave 4: floor∘ceil / ceil∘floor / sqrt(a²)=|a| equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{
    Abs, ArithmeticOperator, Ceil, ExpLogOperator, Floor, Literal, Number, Obj, Pow, Sqrt,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin FloorOfCeilOfInteger: floor(ceil(n)) = n when n in Z.
// Example: have n Z; floor(ceil(n)) = n.
pub struct FloorOfCeilOfIntegerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin CeilOfFloorOfInteger: ceil(floor(n)) = n when n in Z.
// Example: have n Z; ceil(floor(n)) = n.
pub struct CeilOfFloorOfIntegerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SqrtOfSquareEqualsAbs: sqrt(a^2) = abs(a).
// Example: have a R; sqrt(a^2) = abs(a).
pub struct SqrtOfSquareEqualsAbsBuiltinRuleProof {}

pub enum EqualityIdentitiesWave4BuiltinRuleProof {
    FloorOfCeilOfInteger(FloorOfCeilOfIntegerBuiltinRuleProof),
    CeilOfFloorOfInteger(CeilOfFloorOfIntegerBuiltinRuleProof),
    SqrtOfSquareEqualsAbs(SqrtOfSquareEqualsAbsBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave4(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave4BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(p) = self.try_floor_of_ceil_of_integer(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave4BuiltinRuleProof::FloorOfCeilOfInteger(p),
                ));
            }
            if let Some(p) = self.try_ceil_of_floor_of_integer(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave4BuiltinRuleProof::CeilOfFloorOfInteger(p),
                ));
            }
            if let Some(p) = self.try_sqrt_of_square_equals_abs(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave4BuiltinRuleProof::SqrtOfSquareEqualsAbs(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_floor_of_ceil_of_integer(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FloorOfCeilOfIntegerBuiltinRuleProof>> {
        let Some(arg) = match_floor(left) else {
            return Ok(None);
        };
        let Some(n) = match_ceil(arg) else {
            return Ok(None);
        };
        if n.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_in_integer(n, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(FloorOfCeilOfIntegerBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_ceil_of_floor_of_integer(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CeilOfFloorOfIntegerBuiltinRuleProof>> {
        let Some(arg) = match_ceil(left) else {
            return Ok(None);
        };
        let Some(n) = match_floor(arg) else {
            return Ok(None);
        };
        if n.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_in_integer(n, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(CeilOfFloorOfIntegerBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sqrt_of_square_equals_abs(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<SqrtOfSquareEqualsAbsBuiltinRuleProof>> {
        let Some(arg) = match_sqrt(left) else {
            return Ok(None);
        };
        let Some((base, exp)) = match_pow(arg) else {
            return Ok(None);
        };
        if !is_two_obj(exp) {
            return Ok(None);
        }
        let Some(abs_arg) = match_abs(right) else {
            return Ok(None);
        };
        if base.ir() == abs_arg.ir() {
            return Ok(Some(SqrtOfSquareEqualsAbsBuiltinRuleProof {}));
        }
        Ok(None)
    }
}

fn match_floor(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_ceil(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_sqrt(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_pow(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) => {
            Some((base.as_ref(), exponent.as_ref()))
        }
        _ => None,
    }
}

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn is_two_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
    )
}
