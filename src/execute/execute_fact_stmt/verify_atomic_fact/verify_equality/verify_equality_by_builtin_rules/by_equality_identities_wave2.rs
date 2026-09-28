//! Stage B wave 2: sqrt / abs / log / power-identity / mod equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, LessEqualFact, LessFact,
};
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Div, ExpLogOperator, IntegerOperator, Literal, Log, Mod, Mul,
    Number, Obj, Pow, Sqrt, Sub,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// --- power identities ---

// Builtin OneToAnyPower: 1^a = 1.
// Example: have a R; 1^a = 1.
pub struct OneToAnyPowerBuiltinRuleProof {}

// Builtin ZeroToPosNatPower: 0^n = 0 for n in N+.
// Example: have n N+; 0^n = 0.
pub struct ZeroToPosNatPowerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- sqrt ---

// Builtin SqrtSquare: (sqrt(x))^2 = x for x >= 0.
pub struct SqrtSquareBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SqrtZero: sqrt(0) = 0.
pub struct SqrtZeroBuiltinRuleProof {}

// Builtin SqrtOne: sqrt(1) = 1.
pub struct SqrtOneBuiltinRuleProof {}

// Builtin SqrtOfSquare: sqrt(a^2) = a for a >= 0.
pub struct SqrtOfSquareBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SqrtProduct: sqrt(a*b) = sqrt(a)*sqrt(b) for a,b > 0.
pub struct SqrtProductBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SqrtQuotient: sqrt(a/b) = sqrt(a)/sqrt(b) for a,b > 0.
pub struct SqrtQuotientBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- abs ---

// Builtin AbsOfNegation: abs(0-a) = abs(a).
pub struct AbsOfNegationBuiltinRuleProof {}

// Builtin AbsProduct: abs(a*b) = abs(a)*abs(b).
pub struct AbsProductBuiltinRuleProof {}

// Builtin AbsSquare: abs(a^2) = a^2.
pub struct AbsSquareBuiltinRuleProof {}

// --- log ---

// Builtin LogBaseSelf: log(b,b) = 1 when 1 < b.
pub struct LogBaseSelfBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogOfOne: log(b,1) = 0 when 1 < b.
pub struct LogOfOneBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogOfPowerSameBase: log(b, b^x) = x when 1 < b.
pub struct LogOfPowerSameBaseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogArgPower: log(b, x^y) = y * log(b, x) when 1 < b and 0 < x.
pub struct LogArgPowerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogProduct: log(b, x*y) = log(b,x)+log(b,y) when 1 < b and 0 < x,y.
pub struct LogProductBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogQuotient: log(b, x/y) = log(b,x)-log(b,y) when 1 < b and 0 < x,y.
pub struct LogQuotientBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogReciprocal: log(b, 1/x) = 0 - log(b,x) when 1 < b and 0 < x.
pub struct LogReciprocalBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogChangeOfBase: log(a,x) = log(b,x)/log(b,a) when 1 < a,b and 0 < x.
pub struct LogChangeOfBaseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// --- mod ---

// Builtin ZeroMod: 0 % a = 0 when a != 0.
pub struct ZeroModBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ModOne: a % 1 = 0.
pub struct ModOneBuiltinRuleProof {}

// Builtin OneModAtLeastTwo: 1 % m = 1 when 2 <= m.
pub struct OneModAtLeastTwoBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin NestedSameModAbsorption: (a % m) % m = a % m when m != 0.
pub struct NestedSameModAbsorptionBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave2BuiltinRuleProof {
    OneToAnyPower(OneToAnyPowerBuiltinRuleProof),
    ZeroToPosNatPower(ZeroToPosNatPowerBuiltinRuleProof),
    SqrtSquare(SqrtSquareBuiltinRuleProof),
    SqrtZero(SqrtZeroBuiltinRuleProof),
    SqrtOne(SqrtOneBuiltinRuleProof),
    SqrtOfSquare(SqrtOfSquareBuiltinRuleProof),
    SqrtProduct(SqrtProductBuiltinRuleProof),
    SqrtQuotient(SqrtQuotientBuiltinRuleProof),
    AbsOfNegation(AbsOfNegationBuiltinRuleProof),
    AbsProduct(AbsProductBuiltinRuleProof),
    AbsSquare(AbsSquareBuiltinRuleProof),
    LogBaseSelf(LogBaseSelfBuiltinRuleProof),
    LogOfOne(LogOfOneBuiltinRuleProof),
    LogOfPowerSameBase(LogOfPowerSameBaseBuiltinRuleProof),
    LogArgPower(LogArgPowerBuiltinRuleProof),
    LogProduct(LogProductBuiltinRuleProof),
    LogQuotient(LogQuotientBuiltinRuleProof),
    LogReciprocal(LogReciprocalBuiltinRuleProof),
    LogChangeOfBase(LogChangeOfBaseBuiltinRuleProof),
    ZeroMod(ZeroModBuiltinRuleProof),
    ModOne(ModOneBuiltinRuleProof),
    OneModAtLeastTwo(OneModAtLeastTwoBuiltinRuleProof),
    NestedSameModAbsorption(NestedSameModAbsorptionBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave2BuiltinRuleProof>> {
        let child = verify_state.without_well_defined_storage();
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(p) = self.try_one_to_any_power(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::OneToAnyPower(p)));
            }
            if let Some(p) = self.try_zero_to_pos_nat_power(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::ZeroToPosNatPower(p)));
            }
            if let Some(p) = self.try_sqrt_square(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::SqrtSquare(p)));
            }
            if let Some(p) = self.try_sqrt_zero(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::SqrtZero(p)));
            }
            if let Some(p) = self.try_sqrt_one(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::SqrtOne(p)));
            }
            if let Some(p) = self.try_sqrt_of_square(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::SqrtOfSquare(p)));
            }
            if let Some(p) = self.try_sqrt_product(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::SqrtProduct(p)));
            }
            if let Some(p) = self.try_sqrt_quotient(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::SqrtQuotient(p)));
            }
            if let Some(p) = self.try_abs_of_negation(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::AbsOfNegation(p)));
            }
            if let Some(p) = self.try_abs_product(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::AbsProduct(p)));
            }
            if let Some(p) = self.try_abs_square(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::AbsSquare(p)));
            }
            if let Some(p) = self.try_log_base_self(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogBaseSelf(p)));
            }
            if let Some(p) = self.try_log_of_one(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogOfOne(p)));
            }
            if let Some(p) = self.try_log_of_power_same_base(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogOfPowerSameBase(p)));
            }
            if let Some(p) = self.try_log_arg_power(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogArgPower(p)));
            }
            if let Some(p) = self.try_log_product(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogProduct(p)));
            }
            if let Some(p) = self.try_log_quotient(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogQuotient(p)));
            }
            if let Some(p) = self.try_log_reciprocal(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogReciprocal(p)));
            }
            if let Some(p) = self.try_log_change_of_base(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::LogChangeOfBase(p)));
            }
            if let Some(p) = self.try_zero_mod(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::ZeroMod(p)));
            }
            if let Some(p) = self.try_mod_one(left, right)? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::ModOne(p)));
            }
            if let Some(p) = self.try_one_mod_at_least_two(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave2BuiltinRuleProof::OneModAtLeastTwo(p)));
            }
            if let Some(p) = self.try_nested_same_mod_absorption(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave2BuiltinRuleProof::NestedSameModAbsorption(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_one_to_any_power(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<OneToAnyPowerBuiltinRuleProof>> {
        let Some((base, _exp)) = match_pow(left) else {
            return Ok(None);
        };
        if is_one_obj(base) && is_one_obj(right) {
            return Ok(Some(OneToAnyPowerBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_zero_to_pos_nat_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ZeroToPosNatPowerBuiltinRuleProof>> {
        let Some((base, exp)) = match_pow(left) else {
            return Ok(None);
        };
        if !is_zero_obj(base) || !is_zero_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_in_pos_nat(exp, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ZeroToPosNatPowerBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sqrt_square(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SqrtSquareBuiltinRuleProof>> {
        let Some((base, exp)) = match_pow(left) else {
            return Ok(None);
        };
        if !is_two_obj(exp) {
            return Ok(None);
        }
        let Some(arg) = match_sqrt(base) else {
            return Ok(None);
        };
        if arg.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonnegative(arg, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(SqrtSquareBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sqrt_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<SqrtZeroBuiltinRuleProof>> {
        let Some(arg) = match_sqrt(left) else {
            return Ok(None);
        };
        if is_zero_obj(arg) && is_zero_obj(right) {
            return Ok(Some(SqrtZeroBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_sqrt_one(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<SqrtOneBuiltinRuleProof>> {
        let Some(arg) = match_sqrt(left) else {
            return Ok(None);
        };
        if is_one_obj(arg) && is_one_obj(right) {
            return Ok(Some(SqrtOneBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_sqrt_of_square(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SqrtOfSquareBuiltinRuleProof>> {
        let Some(arg) = match_sqrt(left) else {
            return Ok(None);
        };
        let Some((base, exp)) = match_pow(arg) else {
            return Ok(None);
        };
        if !is_two_obj(exp) || base.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonnegative(right, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(SqrtOfSquareBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sqrt_product(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SqrtProductBuiltinRuleProof>> {
        let Some(arg) = match_sqrt(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: a,
            right: b,
        })) = arg
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: r1,
            right: r2,
        })) = right
        else {
            return Ok(None);
        };
        let pairs = [
            (r1.as_ref(), r2.as_ref(), a.as_ref(), b.as_ref()),
            (r2.as_ref(), r1.as_ref(), a.as_ref(), b.as_ref()),
            (r1.as_ref(), r2.as_ref(), b.as_ref(), a.as_ref()),
            (r2.as_ref(), r1.as_ref(), b.as_ref(), a.as_ref()),
        ];
        for (s1, s2, x, y) in pairs {
            let Some(sx) = match_sqrt(s1) else {
                continue;
            };
            let Some(sy) = match_sqrt(s2) else {
                continue;
            };
            if sx.ir() != x.ir() || sy.ir() != y.ir() {
                continue;
            }
            let px = self.verify_order_positive(x, verify_state.clone())?;
            if px.is_failed() {
                continue;
            }
            let py = self.verify_order_positive(y, verify_state.clone())?;
            if py.is_failed() {
                continue;
            }
            return Ok(Some(SqrtProductBuiltinRuleProof {
                proof_of_requirement_facts: vec![px, py],
            }));
        }
        Ok(None)
    }

    fn try_sqrt_quotient(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SqrtQuotientBuiltinRuleProof>> {
        let Some(arg) = match_sqrt(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: a,
            right: b,
        })) = arg
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: r1,
            right: r2,
        })) = right
        else {
            return Ok(None);
        };
        let Some(sx) = match_sqrt(r1.as_ref()) else {
            return Ok(None);
        };
        let Some(sy) = match_sqrt(r2.as_ref()) else {
            return Ok(None);
        };
        if sx.ir() != a.as_ref().ir() || sy.ir() != b.as_ref().ir() {
            return Ok(None);
        }
        let px = self.verify_order_positive(a.as_ref(), verify_state.clone())?;
        if px.is_failed() {
            return Ok(None);
        }
        let py = self.verify_order_positive(b.as_ref(), verify_state)?;
        if py.is_failed() {
            return Ok(None);
        }
        Ok(Some(SqrtQuotientBuiltinRuleProof {
            proof_of_requirement_facts: vec![px, py],
        }))
    }

    fn try_abs_of_negation(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<AbsOfNegationBuiltinRuleProof>> {
        let Some(arg) = match_abs(left) else {
            return Ok(None);
        };
        let Some(other) = match_abs(right) else {
            return Ok(None);
        };
        // abs(0 - a) = abs(a)
        if let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left: z, right: a })) = arg {
            if is_zero_obj(z.as_ref()) && a.as_ref().ir() == other.ir() {
                return Ok(Some(AbsOfNegationBuiltinRuleProof {}));
            }
        }
        // abs((-1)*a) = abs(a)
        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left: x, right: y })) = arg {
            if (is_neg_one_obj(x.as_ref()) && y.as_ref().ir() == other.ir())
                || (is_neg_one_obj(y.as_ref()) && x.as_ref().ir() == other.ir())
            {
                return Ok(Some(AbsOfNegationBuiltinRuleProof {}));
            }
        }
        Ok(None)
    }

    fn try_abs_product(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<AbsProductBuiltinRuleProof>> {
        let Some(arg) = match_abs(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: a,
            right: b,
        })) = arg
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: r1,
            right: r2,
        })) = right
        else {
            return Ok(None);
        };
        let pairs = [
            (r1.as_ref(), r2.as_ref(), a.as_ref(), b.as_ref()),
            (r2.as_ref(), r1.as_ref(), a.as_ref(), b.as_ref()),
            (r1.as_ref(), r2.as_ref(), b.as_ref(), a.as_ref()),
            (r2.as_ref(), r1.as_ref(), b.as_ref(), a.as_ref()),
        ];
        for (x, y, u, v) in pairs {
            let Some(ax) = match_abs(x) else {
                continue;
            };
            let Some(ay) = match_abs(y) else {
                continue;
            };
            if ax.ir() == u.ir() && ay.ir() == v.ir() {
                return Ok(Some(AbsProductBuiltinRuleProof {}));
            }
        }
        Ok(None)
    }

    fn try_abs_square(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<AbsSquareBuiltinRuleProof>> {
        let Some(arg) = match_abs(left) else {
            return Ok(None);
        };
        let Some((base, exp)) = match_pow(arg) else {
            return Ok(None);
        };
        if !is_two_obj(exp) {
            return Ok(None);
        }
        // right should be a^2 with same base
        let Some((rbase, rexp)) = match_pow(right) else {
            return Ok(None);
        };
        if is_two_obj(rexp) && rbase.ir() == base.ir() {
            return Ok(Some(AbsSquareBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_log_base_self(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogBaseSelfBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        if base.ir() != arg.ir() || !is_one_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_gt_one(base, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogBaseSelfBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_log_of_one(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogOfOneBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        if !is_one_obj(arg) || !is_zero_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_gt_one(base, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogOfOneBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_log_of_power_same_base(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogOfPowerSameBaseBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        let Some((pbase, pexp)) = match_pow(arg) else {
            return Ok(None);
        };
        if pbase.ir() != base.ir() || pexp.ir() != right.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_gt_one(base, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogOfPowerSameBaseBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_log_arg_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogArgPowerBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        let Some((pbase, pexp)) = match_pow(arg) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: m1,
            right: m2,
        })) = right
        else {
            return Ok(None);
        };
        let candidates = [(m1.as_ref(), m2.as_ref()), (m2.as_ref(), m1.as_ref())];
        for (factor, log_side) in candidates {
            if factor.ir() != pexp.ir() {
                continue;
            }
            let Some((lb, la)) = match_log(log_side) else {
                continue;
            };
            if lb.ir() != base.ir() || la.ir() != pbase.ir() {
                continue;
            }
            let pb = self.verify_order_gt_one(base, verify_state.clone())?;
            if pb.is_failed() {
                continue;
            }
            let px = self.verify_order_positive(pbase, verify_state.clone())?;
            if px.is_failed() {
                continue;
            }
            return Ok(Some(LogArgPowerBuiltinRuleProof {
                proof_of_requirement_facts: vec![pb, px],
            }));
        }
        Ok(None)
    }

    fn try_log_product(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogProductBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: a,
            right: b,
        })) = arg
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
            left: s1,
            right: s2,
        })) = right
        else {
            return Ok(None);
        };
        let pairs = [
            (s1.as_ref(), s2.as_ref(), a.as_ref(), b.as_ref()),
            (s2.as_ref(), s1.as_ref(), a.as_ref(), b.as_ref()),
            (s1.as_ref(), s2.as_ref(), b.as_ref(), a.as_ref()),
            (s2.as_ref(), s1.as_ref(), b.as_ref(), a.as_ref()),
        ];
        for (l1, l2, x, y) in pairs {
            let Some((b1, a1)) = match_log(l1) else {
                continue;
            };
            let Some((b2, a2)) = match_log(l2) else {
                continue;
            };
            if b1.ir() != base.ir() || b2.ir() != base.ir() {
                continue;
            }
            if a1.ir() != x.ir() || a2.ir() != y.ir() {
                continue;
            }
            let pb = self.verify_order_gt_one(base, verify_state.clone())?;
            if pb.is_failed() {
                continue;
            }
            let px = self.verify_order_positive(x, verify_state.clone())?;
            if px.is_failed() {
                continue;
            }
            let py = self.verify_order_positive(y, verify_state.clone())?;
            if py.is_failed() {
                continue;
            }
            return Ok(Some(LogProductBuiltinRuleProof {
                proof_of_requirement_facts: vec![pb, px, py],
            }));
        }
        Ok(None)
    }

    fn try_log_quotient(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogQuotientBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: a,
            right: b,
        })) = arg
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: s1,
            right: s2,
        })) = right
        else {
            return Ok(None);
        };
        let Some((b1, a1)) = match_log(s1.as_ref()) else {
            return Ok(None);
        };
        let Some((b2, a2)) = match_log(s2.as_ref()) else {
            return Ok(None);
        };
        if b1.ir() != base.ir() || b2.ir() != base.ir() {
            return Ok(None);
        }
        if a1.ir() != a.as_ref().ir() || a2.ir() != b.as_ref().ir() {
            return Ok(None);
        }
        let pb = self.verify_order_gt_one(base, verify_state.clone())?;
        if pb.is_failed() {
            return Ok(None);
        }
        let px = self.verify_order_positive(a.as_ref(), verify_state.clone())?;
        if px.is_failed() {
            return Ok(None);
        }
        let py = self.verify_order_positive(b.as_ref(), verify_state)?;
        if py.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogQuotientBuiltinRuleProof {
            proof_of_requirement_facts: vec![pb, px, py],
        }))
    }

    fn try_log_reciprocal(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogReciprocalBuiltinRuleProof>> {
        let Some((base, arg)) = match_log(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: num,
            right: den,
        })) = arg
        else {
            return Ok(None);
        };
        if !is_one_obj(num.as_ref()) {
            return Ok(None);
        }
        // right is 0 - log(b,x) or (-1)*log(b,x)
        let log_side = if let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: z,
            right: t,
        })) = right
        {
            if is_zero_obj(z.as_ref()) {
                Some(t.as_ref())
            } else {
                None
            }
        } else if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: x,
            right: y,
        })) = right
        {
            if is_neg_one_obj(x.as_ref()) {
                Some(y.as_ref())
            } else if is_neg_one_obj(y.as_ref()) {
                Some(x.as_ref())
            } else {
                None
            }
        } else {
            None
        };
        let Some(log_side) = log_side else {
            return Ok(None);
        };
        let Some((lb, la)) = match_log(log_side) else {
            return Ok(None);
        };
        if lb.ir() != base.ir() || la.ir() != den.as_ref().ir() {
            return Ok(None);
        }
        let pb = self.verify_order_gt_one(base, verify_state.clone())?;
        if pb.is_failed() {
            return Ok(None);
        }
        let px = self.verify_order_positive(den.as_ref(), verify_state)?;
        if px.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogReciprocalBuiltinRuleProof {
            proof_of_requirement_facts: vec![pb, px],
        }))
    }

    fn try_log_change_of_base(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LogChangeOfBaseBuiltinRuleProof>> {
        let Some((a, x)) = match_log(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: num,
            right: den,
        })) = right
        else {
            return Ok(None);
        };
        let Some((b1, x1)) = match_log(num.as_ref()) else {
            return Ok(None);
        };
        let Some((b2, a2)) = match_log(den.as_ref()) else {
            return Ok(None);
        };
        if x1.ir() != x.ir() || a2.ir() != a.ir() || b1.ir() != b2.ir() {
            return Ok(None);
        }
        let pa = self.verify_order_gt_one(a, verify_state.clone())?;
        if pa.is_failed() {
            return Ok(None);
        }
        let pb = self.verify_order_gt_one(b1, verify_state.clone())?;
        if pb.is_failed() {
            return Ok(None);
        }
        let px = self.verify_order_positive(x, verify_state)?;
        if px.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogChangeOfBaseBuiltinRuleProof {
            proof_of_requirement_facts: vec![pa, pb, px],
        }))
    }

    fn try_zero_mod(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ZeroModBuiltinRuleProof>> {
        let Some((dividend, modulus)) = match_mod(left) else {
            return Ok(None);
        };
        if !is_zero_obj(dividend) || !is_zero_obj(right) {
            return Ok(None);
        }
        let proof = self.verify_order_nonzero(modulus, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ZeroModBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_mod_one(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<ModOneBuiltinRuleProof>> {
        let Some((_dividend, modulus)) = match_mod(left) else {
            return Ok(None);
        };
        if is_one_obj(modulus) && is_zero_obj(right) {
            return Ok(Some(ModOneBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_one_mod_at_least_two(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OneModAtLeastTwoBuiltinRuleProof>> {
        let Some((dividend, modulus)) = match_mod(left) else {
            return Ok(None);
        };
        if !is_one_obj(dividend) || !is_one_obj(right) {
            return Ok(None);
        }
        let goal = Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: two_obj(),
            right: modulus.clone(),
            line_file: None,
        }));
        let proof = self.verify_fact(&goal, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(OneModAtLeastTwoBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_nested_same_mod_absorption(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NestedSameModAbsorptionBuiltinRuleProof>> {
        let Some((inner, outer_mod)) = match_mod(left) else {
            return Ok(None);
        };
        let Some((inner_div, inner_mod)) = match_mod(inner) else {
            return Ok(None);
        };
        if outer_mod.ir() != inner_mod.ir() {
            return Ok(None);
        }
        let Some((r_div, r_mod)) = match_mod(right) else {
            return Ok(None);
        };
        if r_div.ir() != inner_div.ir() || r_mod.ir() != outer_mod.ir() {
            return Ok(None);
        }
        let proof = self.verify_order_nonzero(outer_mod, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(NestedSameModAbsorptionBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn verify_order_in_pos_nat(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        self.verify_in_positive_natural(obj, verify_state)
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

fn match_sqrt(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_log(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Log(Log { base, arg })) => {
            Some((base.as_ref(), arg.as_ref()))
        }
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

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn is_two_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
    )
}

fn is_neg_one_obj(obj: &Obj) -> bool {
    if matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "-1"
    ) {
        return true;
    }
    matches!(
        obj,
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) && is_one_obj(right.as_ref())
    )
}

fn two_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "2".to_string(),
    }))
}
