//! Stage B wave 3: min/max / abs∘abs / exp↔ln / floor·ceil / mod-self equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{
    Abs, ArithmeticOperator, Ceil, Exp, ExpLogOperator, Floor, IntegerOperator, Literal, Ln, Max,
    Min, Mod, Number, Obj,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// --- min / max ---

// Builtin MinIdempotent: min(a, a) = a.
// Example: have a R; min(a, a) = a.
pub struct MinIdempotentBuiltinRuleProof {}

// Builtin MaxIdempotent: max(a, a) = a.
// Example: have a R; max(a, a) = a.
pub struct MaxIdempotentBuiltinRuleProof {}

// Builtin MinCommutative: min(a, b) = min(b, a).
// Example: have a R; have b R; min(a, b) = min(b, a).
pub struct MinCommutativeBuiltinRuleProof {}

// Builtin MaxCommutative: max(a, b) = max(b, a).
// Example: have a R; have b R; max(a, b) = max(b, a).
pub struct MaxCommutativeBuiltinRuleProof {}

// --- abs ---

// Builtin AbsAbsAbsorption: abs(abs(a)) = abs(a).
// Example: have a R; abs(abs(a)) = abs(a).
pub struct AbsAbsAbsorptionBuiltinRuleProof {}

// --- exp / ln ---

// Builtin ExpOfLn: exp(ln(x)) = x when 0 < x.
// Example: have x R+; exp(ln(x)) = x.
pub struct ExpOfLnBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LnOfExp: ln(exp(x)) = x.
// Example: have x R; ln(exp(x)) = x.
pub struct LnOfExpBuiltinRuleProof {}

// --- floor / ceil ---

// Builtin FloorOfInteger: floor(n) = n when n in Z.
// Example: have n Z; floor(n) = n.
pub struct FloorOfIntegerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin CeilOfInteger: ceil(n) = n when n in Z.
// Example: have n Z; ceil(n) = n.
pub struct CeilOfIntegerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- mod ---

// Builtin ModSelfZero: a % a = 0 when a != 0.
// Example: have a N+; a % a = 0.
pub struct ModSelfZeroBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave3BuiltinRuleProof {
    MinIdempotent(MinIdempotentBuiltinRuleProof),
    MaxIdempotent(MaxIdempotentBuiltinRuleProof),
    MinCommutative(MinCommutativeBuiltinRuleProof),
    MaxCommutative(MaxCommutativeBuiltinRuleProof),
    AbsAbsAbsorption(AbsAbsAbsorptionBuiltinRuleProof),
    ExpOfLn(ExpOfLnBuiltinRuleProof),
    LnOfExp(LnOfExpBuiltinRuleProof),
    FloorOfInteger(FloorOfIntegerBuiltinRuleProof),
    CeilOfInteger(CeilOfIntegerBuiltinRuleProof),
    ModSelfZero(ModSelfZeroBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave3(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave3BuiltinRuleProof>> {
        let child = verify_state.without_well_defined_storage();
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(p) = self.try_min_idempotent(left, right)? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::MinIdempotent(p)));
            }
            if let Some(p) = self.try_max_idempotent(left, right)? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::MaxIdempotent(p)));
            }
            if let Some(p) = self.try_min_commutative(left, right)? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::MinCommutative(p)));
            }
            if let Some(p) = self.try_max_commutative(left, right)? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::MaxCommutative(p)));
            }
            if let Some(p) = self.try_abs_abs_absorption(left, right)? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::AbsAbsAbsorption(p)));
            }
            if let Some(p) = self.try_exp_of_ln(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::ExpOfLn(p)));
            }
            if let Some(p) = self.try_ln_of_exp(left, right)? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::LnOfExp(p)));
            }
            if let Some(p) = self.try_floor_of_integer(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::FloorOfInteger(p)));
            }
            if let Some(p) = self.try_ceil_of_integer(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::CeilOfInteger(p)));
            }
            if let Some(p) = self.try_mod_self_zero(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave3BuiltinRuleProof::ModSelfZero(p)));
            }
        }
        Ok(None)
    }

    fn try_min_idempotent(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<MinIdempotentBuiltinRuleProof>> {
        let Some((a, b)) = match_min(left) else {
            return Ok(None);
        };
        if a.ir() == b.ir() && a.ir() == right.ir() {
            return Ok(Some(MinIdempotentBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_max_idempotent(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<MaxIdempotentBuiltinRuleProof>> {
        let Some((a, b)) = match_max(left) else {
            return Ok(None);
        };
        if a.ir() == b.ir() && a.ir() == right.ir() {
            return Ok(Some(MaxIdempotentBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_min_commutative(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<MinCommutativeBuiltinRuleProof>> {
        let Some((a, b)) = match_min(left) else {
            return Ok(None);
        };
        let Some((c, d)) = match_min(right) else {
            return Ok(None);
        };
        if a.ir() == d.ir() && b.ir() == c.ir() && a.ir() != b.ir() {
            return Ok(Some(MinCommutativeBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_max_commutative(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<MaxCommutativeBuiltinRuleProof>> {
        let Some((a, b)) = match_max(left) else {
            return Ok(None);
        };
        let Some((c, d)) = match_max(right) else {
            return Ok(None);
        };
        if a.ir() == d.ir() && b.ir() == c.ir() && a.ir() != b.ir() {
            return Ok(Some(MaxCommutativeBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_abs_abs_absorption(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<AbsAbsAbsorptionBuiltinRuleProof>> {
        let Some(inner) = match_abs(left) else {
            return Ok(None);
        };
        let Some(inner_arg) = match_abs(inner) else {
            return Ok(None);
        };
        let Some(right_arg) = match_abs(right) else {
            return Ok(None);
        };
        if inner_arg.ir() == right_arg.ir() {
            return Ok(Some(AbsAbsAbsorptionBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_exp_of_ln(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExpOfLnBuiltinRuleProof>> {
        let Some(arg) = match_exp(left) else {
            return Ok(None);
        };
        let Some(ln_arg) = match_ln(arg) else {
            return Ok(None);
        };
        if ln_arg.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_positive(ln_arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ExpOfLnBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_ln_of_exp(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<LnOfExpBuiltinRuleProof>> {
        let Some(arg) = match_ln(left) else {
            return Ok(None);
        };
        let Some(exp_arg) = match_exp(arg) else {
            return Ok(None);
        };
        if exp_arg.ir() == right.ir() {
            return Ok(Some(LnOfExpBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_floor_of_integer(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FloorOfIntegerBuiltinRuleProof>> {
        let Some(arg) = match_floor(left) else {
            return Ok(None);
        };
        if arg.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_in_integer(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(FloorOfIntegerBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_ceil_of_integer(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CeilOfIntegerBuiltinRuleProof>> {
        let Some(arg) = match_ceil(left) else {
            return Ok(None);
        };
        if arg.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_in_integer(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(CeilOfIntegerBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_mod_self_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ModSelfZeroBuiltinRuleProof>> {
        let Some((dividend, modulus)) = match_mod(left) else {
            return Ok(None);
        };
        if dividend.ir() != modulus.ir() {
            return Ok(None);
        }
        if !is_zero_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_nonzero(modulus, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ModSelfZeroBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
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

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_exp(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_ln(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Ln(Ln { arg })) => Some(arg.as_ref()),
        _ => None,
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

fn match_mod(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
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
