//! Stage B wave 2: sqrt / abs / log / power-identity / mod equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use super::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, LessEqualFact, LessFact, NotEqualFact, GreaterFact,
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

// Builtin SqrtProduct: sqrt(a*b) = sqrt(a)*sqrt(b) for a,b >= 0.
pub struct SqrtProductBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SqrtQuotient: sqrt(a/b) = sqrt(a)/sqrt(b) for a >= 0, b > 0.
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

// Builtin LogBaseSelf: log(b,b) = 1 when b > 0 and b != 1.
pub struct LogBaseSelfBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogOfOne: log(b,1) = 0 when b > 0 and b != 1.
pub struct LogOfOneBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin LogOfPowerSameBase: log(b, b^x) = x when b > 0 and b != 1.
pub struct LogOfPowerSameBaseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Example: a<1, a>0, x>0, n Z => log(a,x^n)=n*log(a,x).
// Builtin LogArgPower: log(b, x^y) = y * log(b, x) when b>0, b!=1 and 0<x.
pub struct LogArgPowerBuiltinRuleProof {
    pub base_proof: LogAlgebraBaseProof,
    pub argument_positive_proof: VerifyFactResult,
}
impl LogArgPowerBuiltinRuleProof {
    pub fn new(base_proof: LogAlgebraBaseProof, argument_positive_proof: VerifyFactResult) -> Self {
        Self { base_proof, argument_positive_proof }
    }
}

// Example: 0<a<1, x,y R+ => log(a,x*y)=log(a,x)+log(a,y).
// Builtin LogProduct: log(b, x*y) = log(b,x)+log(b,y) when b>0, b!=1 and 0<x,y.
pub struct LogProductBuiltinRuleProof {
    pub base_proof: LogAlgebraBaseProof,
    pub left_argument_positive_proof: VerifyFactResult,
    pub right_argument_positive_proof: VerifyFactResult,
}
impl LogProductBuiltinRuleProof {
    pub fn new(base_proof: LogAlgebraBaseProof, left_argument_positive_proof: VerifyFactResult, right_argument_positive_proof: VerifyFactResult) -> Self {
        Self { base_proof, left_argument_positive_proof, right_argument_positive_proof }
    }
}

// Example: 0<a<1, x,y R+ => log(a,x/y)=log(a,x)-log(a,y).
// Builtin LogQuotient: log(b, x/y) = log(b,x)-log(b,y) when b>0, b!=1 and 0<x,y.
pub struct LogQuotientBuiltinRuleProof {
    pub base_proof: LogAlgebraBaseProof,
    pub numerator_positive_proof: VerifyFactResult,
    pub denominator_positive_proof: VerifyFactResult,
}
impl LogQuotientBuiltinRuleProof {
    pub fn new(base_proof: LogAlgebraBaseProof, numerator_positive_proof: VerifyFactResult, denominator_positive_proof: VerifyFactResult) -> Self {
        Self { base_proof, numerator_positive_proof, denominator_positive_proof }
    }
}

// Example: 0<a<1, x R+ => log(a,1/x)=-log(a,x).
// Builtin LogReciprocal: log(b, 1/x) = 0 - log(b,x) when b>0, b!=1 and 0<x.
pub struct LogReciprocalBuiltinRuleProof {
    pub base_proof: LogAlgebraBaseProof,
    pub argument_positive_proof: VerifyFactResult,
}
impl LogReciprocalBuiltinRuleProof {
    pub fn new(base_proof: LogAlgebraBaseProof, argument_positive_proof: VerifyFactResult) -> Self {
        Self { base_proof, argument_positive_proof }
    }
}

// Builtin LogChangeOfBase: positive nonunit real bases and 0<x.
pub struct LogChangeOfBaseBuiltinRuleProof {
    pub base_proof: LogAlgebraBaseProof,
    pub chosen_base_proof: LogAlgebraBaseProof,
    pub argument_positive_proof: VerifyFactResult,
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

// Builtin ModCompatibleSmallerModulus: a % d = (a % m) % d when m % d = 0.
// Mathematical property: if the larger modulus is a multiple of the smaller,
// nested reduction by the larger modulus does not change remainder mod d.
// Example: forall p Z: p % 2 = (p % 8) % 2.
pub struct ModCompatibleSmallerModulusBuiltinRuleProof {
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
    ModCompatibleSmallerModulus(ModCompatibleSmallerModulusBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave2BuiltinRuleProof>> {
        let child = verify_state;
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
            if let Some(p) =
                self.try_mod_compatible_smaller_modulus(left, right, child.clone())?
            {
                return Ok(Some(
                    EqualityIdentitiesWave2BuiltinRuleProof::ModCompatibleSmallerModulus(p),
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
            let px = self.verify_sqrt_nonnegative_argument(x, verify_state.clone())?;
            if px.is_failed() {
                continue;
            }
            let py = self.verify_sqrt_nonnegative_argument(y, verify_state.clone())?;
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
        let px = self.verify_sqrt_nonnegative_argument(a.as_ref(), verify_state.clone())?;
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

    fn verify_sqrt_nonnegative_argument(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let nonnegative = self.verify_order_nonnegative(obj, verify_state.clone())?;
        if nonnegative.is_failed() {
            // A checked strict bound is sufficient too. Preserve the original
            // positive-input route without asking a lower ceiling to weaken it.
            self.verify_order_positive(obj, verify_state)
        } else {
            Ok(nonnegative)
        }
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
        if let Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) = arg {
            if neg.arg.ir() == other.ir() { return Ok(Some(AbsOfNegationBuiltinRuleProof {})); }
        }
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
        let Some(proof_of_requirement_facts) = self.verify_log_algebra_base(base, verify_state)? else { return Ok(None); };
        Ok(Some(LogBaseSelfBuiltinRuleProof {
            proof_of_requirement_facts,
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
        let Some(proof_of_requirement_facts) = self.verify_log_algebra_base(base, verify_state)? else { return Ok(None); };
        Ok(Some(LogOfOneBuiltinRuleProof {
            proof_of_requirement_facts,
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
        let Some(proof_of_requirement_facts) = self.verify_log_algebra_base(base, verify_state)? else { return Ok(None); };
        Ok(Some(LogOfPowerSameBaseBuiltinRuleProof {
            proof_of_requirement_facts,
        }))
    }

    // Algebraic log identities hold on both positive base ranges, excluding 1.
    // Example: log(1/2,(1/2)^(-3))=-3; monotonicity keeps its own sign premise.
    fn verify_log_algebra_base(&mut self, base: &Obj, state: VerifyState) -> RuntimeResult<Option<Vec<VerifyFactResult>>> {
        // Reuse the same positive, nonunit alternatives as the other log laws.
        // Example: a R+, a<1 => log(a,a)=1, with actual a<1 evidence.
        let Some(base_proof) = self.verify_log_algebra_base_guard(base, state)? else { return Ok(None); };
        Ok(Some(match base_proof {
            LogAlgebraBaseProof::GreaterThanOne(proof) => vec![proof],
            LogAlgebraBaseProof::BelowOne(proof) => vec![proof.positive_proof, proof.less_than_one_proof],
            LogAlgebraBaseProof::PositiveNonunit(proof) => vec![proof.positive_proof, proof.nonunit_proof],
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
            let Some(base_proof) = self.verify_log_algebra_base_guard(base, verify_state)? else {
                continue;
            };
            let px = self.verify_log_algebra_positive(pbase, verify_state.clone())?;
            if px.is_failed() {
                continue;
            }
            return Ok(Some(LogArgPowerBuiltinRuleProof::new(base_proof, px)));
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
            let Some(base_proof) = self.verify_log_algebra_base_guard(base, verify_state)? else {
                continue;
            };
            let px = self.verify_log_algebra_positive(x, verify_state.clone())?;
            if px.is_failed() {
                continue;
            }
            let py = self.verify_log_algebra_positive(y, verify_state.clone())?;
            if py.is_failed() {
                continue;
            }
            return Ok(Some(LogProductBuiltinRuleProof::new(base_proof, px, py)));
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
        let Some(base_proof) = self.verify_log_algebra_base_guard(base, verify_state)? else {
            return Ok(None);
        };
        let px = self.verify_log_algebra_positive(a.as_ref(), verify_state.clone())?;
        if px.is_failed() {
            return Ok(None);
        }
        let py = self.verify_log_algebra_positive(b.as_ref(), verify_state)?;
        if py.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogQuotientBuiltinRuleProof::new(base_proof, px, py)))
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
        // right is 0-log(b,x), (-1)*log(b,x), or -log(b,x)
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
        } else if let Obj::ArithmeticOperator(ArithmeticOperator::Neg(negative)) = right {
            Some(negative.arg.as_ref())
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
        let Some(base_proof) = self.verify_log_algebra_base_guard(base, verify_state)? else {
            return Ok(None);
        };
        let px = self.verify_log_algebra_positive(den.as_ref(), verify_state)?;
        if px.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogReciprocalBuiltinRuleProof::new(base_proof, px)))
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
        let Some(base_proof) = self.verify_log_algebra_base_guard(a, verify_state)? else { return Ok(None); };
        let Some(chosen_base_proof) = self.verify_log_algebra_base_guard(b1, verify_state)? else { return Ok(None); };
        let argument_positive_proof = self.verify_log_algebra_positive(x, verify_state)?;
        if argument_positive_proof.is_failed() { return Ok(None); }
        Ok(Some(LogChangeOfBaseBuiltinRuleProof { base_proof, chosen_base_proof, argument_positive_proof }))
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
        let proof = self.verify_builtin_rule_premise(&goal, verify_state)?;
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

    // When: goal is `a % d = (a % m) % d` and `m % d = 0` is provable.
    // After: nested mod by a multiple of d preserves the remainder mod d.
    // Example: `p % 2 = (p % 8) % 2`.
    fn try_mod_compatible_smaller_modulus(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ModCompatibleSmallerModulusBuiltinRuleProof>> {
        let Some((a_left, d_left)) = match_mod(left) else {
            return Ok(None);
        };
        let Some((inner, d_right)) = match_mod(right) else {
            return Ok(None);
        };
        if d_left.ir() != d_right.ir() {
            return Ok(None);
        }
        let Some((a_inner, m)) = match_mod(inner) else {
            return Ok(None);
        };
        if a_left.ir() != a_inner.ir() {
            return Ok(None);
        }
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let rem = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
            left: Box::new(m.clone()),
            right: Box::new(d_left.clone()),
        }));
        let divisible = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: rem,
            right: zero,
            line_file: None,
        }));
        let divisible_proof = self.verify_builtin_rule_premise(&divisible, verify_state.clone())?;
        if divisible_proof.is_failed() {
            return Ok(None);
        }
        let nonzero_small = self.verify_order_nonzero(d_left, verify_state.clone())?;
        if nonzero_small.is_failed() {
            return Ok(None);
        }
        let nonzero_large = self.verify_order_nonzero(m, verify_state)?;
        if nonzero_large.is_failed() {
            return Ok(None);
        }
        Ok(Some(ModCompatibleSmallerModulusBuiltinRuleProof {
            proof_of_requirement_facts: vec![divisible_proof, nonzero_small, nonzero_large],
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
    // The current parser represents surface (-1) with native Neg.
    // Example: log(a,1/x)=(-1)*log(a,x), with the same legal-base guard.
    if let Obj::ArithmeticOperator(ArithmeticOperator::Neg(negative)) = obj {
        if is_one_obj(&negative.arg) { return true; }
    }
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

#[cfg(test)]
mod principal_root_nonnegative_algebra_tests {
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    use crate::json_output::project_run_detailed;
    use crate::knowledge_base::JsonValue;
    use crate::launch_command::{LaunchCommand, OutputLanguage};
    use crate::runtime::Runtime;
    use crate::tokenize::Tokenizer;

    fn runtime() -> Runtime {
        Runtime::new(LaunchCommand::Eval {
            code: String::new(), session: false, strict: true, language: OutputLanguage::English,
        })
    }

    fn check(rt: &mut Runtime, code: &str, expected: bool) -> JsonValue {
        let run = rt.run_litex_code(code).expect("public Runtime");
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert_eq!(run.success, expected, "{code}");
        project_run_detailed(&run, rt, "eval", None)
    }

    fn find_rule<'a>(value: &'a JsonValue, rule: &str) -> Option<&'a JsonValue> {
        match value {
            JsonValue::Object(fields) => {
                if fields.get("rule").and_then(|v| v.as_str().ok()) == Some(rule) {
                    return Some(value);
                }
                fields.keys_in_order().into_iter().find_map(|key| find_rule(fields.get(&key).unwrap(), rule))
            }
            JsonValue::Array(items) => items.iter().find_map(|v| find_rule(v, rule)),
            _ => None,
        }
    }

    fn requirements(json: &JsonValue, rule: &str) -> Vec<String> {
        let leaf = find_rule(json, rule).expect("actual winning native root rule").as_object().unwrap();
        let values = leaf.get("proof_of_requirement_facts").unwrap().as_array().unwrap();
        assert_eq!(values.len(), 2);
        values.iter().map(|v| {
            let proof = v.as_object().unwrap();
            assert_eq!(proof.get("success"), Some(&JsonValue::Bool(true)));
            assert!(proof.get("searched_proof").is_some());
            proof.get("fact").unwrap().as_str().unwrap().to_owned()
        }).collect()
    }

    #[test]
    fn principal_root_nonnegative_algebra_tracer_retains_checked_requirements() {
        let source = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/equal/by_builtin_rule/principal_root_nonnegative_algebra.lit"));
        let json = check(&mut runtime(), source, true);
        assert_eq!(requirements(&json, "SqrtProduct"), vec!["0 <= a", "0 <= b"]);
        assert_eq!(requirements(&json, "SqrtQuotient"), vec!["0 <= a", "0 < b"]);
    }

    #[test]
    fn principal_root_nonnegative_algebra_preserves_positive_and_reversed_shapes() {
        for code in [
            "forall a,b R:\n    0<a\n    0<b\n    =>:\n        sqrt(a*b)=sqrt(a)*sqrt(b)\n",
            "forall a,b R:\n    0<a\n    0<b\n    =>:\n        sqrt(a/b)=sqrt(a)/sqrt(b)\n",
            "forall a,b R:\n    0<=a\n    0<=b\n    =>:\n        sqrt(b)*sqrt(a)=sqrt(a*b)\n",
            "forall a,b R:\n    0<=a\n    0<b\n    =>:\n        sqrt(a)/sqrt(b)=sqrt(a/b)\n",
            "forall b R:\n    0<b\n    =>:\n        sqrt(0/b)=sqrt(0)/sqrt(b)\n",
        ] {
            check(&mut runtime(), code, true);
        }
    }

    #[test]
    fn principal_root_nonnegative_algebra_rejects_wrong_formulas_and_illegal_domains() {
        for code in [
            "forall a,b R:\n    0<=a\n    0<=b\n    =>:\n        sqrt(a*b)=sqrt(a)+sqrt(b)\n",
            "forall a,b R:\n    0<a\n    0<b\n    =>:\n        sqrt(a/b)=sqrt(b)/sqrt(a)\n",
            "forall a,b R:\n    0<=a\n    0<=b\n    =>:\n        sqrt(a/b)=sqrt(a)/sqrt(b)\n",
            "sqrt((-1)*(-1))=sqrt(-1)*sqrt(-1)\n",
            "sqrt(0/0)=sqrt(0)/sqrt(0)\n",
            "sqrt(i*i)=sqrt(i)*sqrt(i)\n",
        ] {
            check(&mut runtime(), code, false);
        }
    }

    #[test]
    fn principal_root_nonnegative_algebra_cites_actual_nonnegative_assumptions() {
        let code = "forall a,b R:\n    0<=a\n    0<=b\n    =>:\n        sqrt(a*b)=sqrt(a)*sqrt(b)\n";
        let json = check(&mut runtime(), code, true);
        let statement = &json.as_object().unwrap().get("statement_results").unwrap().as_array().unwrap()[0];
        let verify = statement.as_object().unwrap().get("verify").unwrap().as_object().unwrap();
        let assumptions = verify.get("assumed_dom_facts").unwrap().as_array().unwrap();
        let leaf = find_rule(&json, "SqrtProduct").unwrap().as_object().unwrap();
        let requirements = leaf.get("proof_of_requirement_facts").unwrap().as_array().unwrap();
        for (assumption, requirement) in assumptions.iter().zip(requirements) {
            let source = &assumption.as_object().unwrap().get("store_and_infer").unwrap().as_object().unwrap().get("stores").unwrap().as_array().unwrap()[0];
            let source_id = source.as_object().unwrap().get("fact_id").unwrap().as_str().unwrap();
            let proof = requirement.as_object().unwrap().get("searched_proof").unwrap().as_object().unwrap();
            assert_eq!(proof.get("cite_fact_id").unwrap().as_str().unwrap(), source_id);
        }
    }

    #[test]
    fn principal_root_nonnegative_algebra_respects_inherited_search_ceiling() {
        let mut rt = runtime();
        check(&mut rt, "have a,b R+\n0<=a\n0<=b\na*b $in R\nsqrt(a*b) $in R\nsqrt(a) $in R\nsqrt(b) $in R\n", true);
        let tokens = Tokenizer::new().tokenize("sqrt(a*b)=sqrt(a)*sqrt(b)", rt.current_file.clone()).unwrap();
        let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else { panic!("fact") };
        for level in [VerifyStateLevel::Direct, VerifyStateLevel::KnownSpecialProperty] {
            assert!(rt.verify_fact(&goal, VerifyState::new(level)).unwrap().is_failed());
        }
        assert!(!rt.verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule)).unwrap().is_failed());
    }

    #[test]
    fn principal_root_nonnegative_algebra_false_goal_does_not_publish_or_poison_reuse() {
        let mut rt = runtime();
        let wrong = "forall a,b R:\n    0<=a\n    0<=b\n    =>:\n        sqrt(a*b)=sqrt(a)+sqrt(b)\n";
        let valid = "forall a,b R:\n    0<=a\n    0<=b\n    =>:\n        sqrt(a*b)=sqrt(a)*sqrt(b)\n";
        check(&mut rt, wrong, false);
        check(&mut rt, "1=2\n", false);
        check(&mut rt, valid, true);
        check(&mut rt, wrong, false);
        check(&mut rt, valid, true);
        check(&mut rt, "1=2\n", false);
    }
}
