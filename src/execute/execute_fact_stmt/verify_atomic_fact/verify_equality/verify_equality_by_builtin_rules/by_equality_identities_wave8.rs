//! Stage B wave 8: Euclidean / square-sum / odd (-1) power / lcm·gcd leftovers.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::EqualFact;
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, Gcd, IntegerOperator, Lcm, Literal, Mod, Mul, Neg, Number, Obj,
    Pow, Quot, Sub,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin QuotEuclideanDecomposition: a = d * quot(a, d) + (a % d)
// (also accepts quot(a, d) * d on the product side).
// Example: have a Z; have d N+; a = d * quot(a, d) + (a % d).
pub struct QuotEuclideanDecompositionBuiltinRuleProof {}

// Builtin ModDividendMinusRemainderZero: (a - (a % b)) % b = 0.
// Example: have a Z; have b N+; (a - (a % b)) % b = 0.
pub struct ModDividendMinusRemainderZeroBuiltinRuleProof {}

// Builtin SquareSumComponentZero: a = 0 (or b = 0) from known a^2 + b^2 = 0
// (also accepts a * a squares).
// Example: have a R; have b R; trust a^2 + b^2 = 0; a = 0.
pub struct SquareSumComponentZeroBuiltinRuleProof {}

// Builtin MinusOneOddNaturalPower: (-1)^(2 * m + 1) = -1.
// Example: have m N; (-1)^(2 * m + 1) = -1.
pub struct MinusOneOddNaturalPowerBuiltinRuleProof {}

// Builtin LcmGcdProductAbs: lcm(a, b) * gcd(a, b) = abs(a * b).
// Example: have a Z; have b Z; trust a != 0; trust b != 0;
//          trust lcm(a, b) $in N; trust gcd(a, b) $in N+;
//          lcm(a, b) * gcd(a, b) = abs(a * b).
pub struct LcmGcdProductAbsBuiltinRuleProof {}

pub enum EqualityIdentitiesWave8BuiltinRuleProof {
    QuotEuclideanDecomposition(QuotEuclideanDecompositionBuiltinRuleProof),
    ModDividendMinusRemainderZero(ModDividendMinusRemainderZeroBuiltinRuleProof),
    SquareSumComponentZero(SquareSumComponentZeroBuiltinRuleProof),
    MinusOneOddNaturalPower(MinusOneOddNaturalPowerBuiltinRuleProof),
    LcmGcdProductAbs(LcmGcdProductAbsBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave8(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave8BuiltinRuleProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if quot_euclidean_decomposition_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::QuotEuclideanDecomposition(
                        QuotEuclideanDecompositionBuiltinRuleProof {},
                    ),
                ));
            }
            if mod_dividend_minus_remainder_zero_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::ModDividendMinusRemainderZero(
                        ModDividendMinusRemainderZeroBuiltinRuleProof {},
                    ),
                ));
            }
            if minus_one_odd_natural_power_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::MinusOneOddNaturalPower(
                        MinusOneOddNaturalPowerBuiltinRuleProof {},
                    ),
                ));
            }
            if lcm_gcd_product_abs_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave8BuiltinRuleProof::LcmGcdProductAbs(
                        LcmGcdProductAbsBuiltinRuleProof {},
                    ),
                ));
            }
        }
        if self.square_sum_component_zero_shape(fact) {
            return Ok(Some(
                EqualityIdentitiesWave8BuiltinRuleProof::SquareSumComponentZero(
                    SquareSumComponentZeroBuiltinRuleProof {},
                ),
            ));
        }
        Ok(None)
    }

    fn square_sum_component_zero_shape(&self, fact: &EqualFact) -> bool {
        let target = if is_zero_obj(&fact.left) {
            &fact.right
        } else if is_zero_obj(&fact.right) {
            &fact.left
        } else {
            return false;
        };
        let zero = zero_obj();
        let adjacency = self.visible_equivalence_class_adjacency();
        for key in self.equivalence_class_keys(&zero) {
            let Some(neighbors) = adjacency.get(&key) else {
                continue;
            };
            for (_, equal_fact) in neighbors.iter() {
                for side in [&equal_fact.left, &equal_fact.right] {
                    let Some((b1, b2)) = square_sum_bases(side) else {
                        continue;
                    };
                    if b1.ir() == target.ir() || b2.ir() == target.ir() {
                        return true;
                    }
                }
            }
        }
        false
    }
}

fn quot_euclidean_decomposition_shape(dividend: &Obj, decomposition: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: product_side,
        right: rem_side,
    })) = decomposition
    else {
        return false;
    };
    let Some((q_left, q_right)) = match_quot_product(product_side.as_ref()) else {
        return false;
    };
    let Some((r_left, r_right)) = match_mod(rem_side.as_ref()) else {
        return false;
    };
    dividend.ir() == q_left.ir()
        && dividend.ir() == r_left.ir()
        && q_right.ir() == r_right.ir()
}

fn match_quot_product(obj: &Obj) -> Option<(&Obj, &Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj else {
        return None;
    };
    // d * quot(a, d) or quot(a, d) * d
    if let Some((q_left, q_right)) = match_quot(left.as_ref()) {
        if q_right.ir() == right.as_ref().ir() {
            return Some((q_left, q_right));
        }
    }
    if let Some((q_left, q_right)) = match_quot(right.as_ref()) {
        if q_right.ir() == left.as_ref().ir() {
            return Some((q_left, q_right));
        }
    }
    None
}

fn mod_dividend_minus_remainder_zero_shape(remainder: &Obj, zero: &Obj) -> bool {
    if !is_zero_obj(zero) {
        return false;
    }
    let Some((dividend, modulus)) = match_mod(remainder) else {
        return false;
    };
    let Some((a, inner_mod)) = match_sub(dividend) else {
        return false;
    };
    let Some((inner_a, inner_b)) = match_mod(inner_mod) else {
        return false;
    };
    a.ir() == inner_a.ir() && modulus.ir() == inner_b.ir()
}

fn minus_one_odd_natural_power_shape(pow_side: &Obj, neg_one_side: &Obj) -> bool {
    if !is_neg_one_obj(neg_one_side) {
        return false;
    }
    let Some((base, exponent)) = match_pow(pow_side) else {
        return false;
    };
    if !is_neg_one_obj(base) {
        return false;
    }
    // exponent = 2 * m + 1
    let Some((even_part, one)) = match_add(exponent) else {
        return false;
    };
    if !is_one_obj(one) {
        return false;
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = even_part else {
        return false;
    };
    is_two_obj(left.as_ref()) || is_two_obj(right.as_ref())
}

fn lcm_gcd_product_abs_shape(product: &Obj, abs_product: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = product else {
        return false;
    };
    let (lcm_args, gcd_args) = match (left.as_ref(), right.as_ref()) {
        (Obj::IntegerOperator(IntegerOperator::Lcm(Lcm { left: a, right: b })),
         Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left: c, right: d })))
        | (Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left: c, right: d })),
           Obj::IntegerOperator(IntegerOperator::Lcm(Lcm { left: a, right: b }))) => {
            ((a.as_ref(), b.as_ref()), (c.as_ref(), d.as_ref()))
        }
        _ => return false,
    };
    if !(lcm_args.0.ir() == gcd_args.0.ir() && lcm_args.1.ir() == gcd_args.1.ir()) {
        return false;
    }
    let Some(abs_arg) = match_abs(abs_product) else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: p1,
        right: p2,
    })) = abs_arg
    else {
        return false;
    };
    (p1.as_ref().ir() == lcm_args.0.ir() && p2.as_ref().ir() == lcm_args.1.ir())
        || (p1.as_ref().ir() == lcm_args.1.ir() && p2.as_ref().ir() == lcm_args.0.ir())
}

fn square_sum_bases(obj: &Obj) -> Option<(&Obj, &Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = obj else {
        return None;
    };
    let b1 = square_base(left.as_ref())?;
    let b2 = square_base(right.as_ref())?;
    Some((b1, b2))
}

fn square_base(obj: &Obj) -> Option<&Obj> {
    if let Some((base, exp)) = match_pow(obj) {
        if is_two_obj(exp) {
            return Some(base);
        }
    }
    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) = obj {
        if left.as_ref().ir() == right.as_ref().ir() {
            return Some(left.as_ref());
        }
    }
    None
}

fn match_mod(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_quot(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Quot(Quot { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
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

fn match_add(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_sub(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
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

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }))
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
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) => is_one_obj(arg.as_ref()),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            is_one_obj(right.as_ref())
        }
        _ => false,
    }
}
