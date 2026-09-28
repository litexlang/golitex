//! Stage B wave 7: remaining numeric equality leftovers from legacy dispatch.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, NotEqualFact};
use crate::new_pipeline::ast::obj::{
    Abs, Add, ArithmeticOperator, Gcd, IntegerOperator, Literal, Mod, Mul, Neg, Number, Obj, Sign,
    Sub,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin GcdDividesArgument: a % gcd(a, b) = 0 (and symmetrically for b).
// Example: have a Z; have b Z; trust a != 0; trust gcd(a,b) $in N+; trust gcd(a,b) != 0;
//          a % gcd(a, b) = 0.
pub struct GcdDividesArgumentBuiltinRuleProof {}

// Builtin ProductModFactorZero: (a * b) % a = 0 (or (a * b) % b = 0).
// Example: have a N+; have b Z; trust a != 0; let p = a * b; trust p $in Z; (a * b) % a = 0
//          (when WD of the mod expression succeeds).
pub struct ProductModFactorZeroBuiltinRuleProof {}

// Builtin EqualityFromTwoSidedWeakOrder: a = b from a <= b and b <= a.
// Example: have a R; have b R; trust a <= b; trust b <= a; a = b.
pub struct EqualityFromTwoSidedWeakOrderBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin DiffZeroFromEqualOperands: a - b = 0 (or 0 = a - b) from a = b.
// Example: have a R; have b R; trust a = b; a - b = 0.
pub struct DiffZeroFromEqualOperandsBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ZeroProductCancel: b = 0 from a * b = 0 and a != 0 (and symmetric).
// Example: have a R; have b R; trust a * b = 0; trust a != 0; b = 0.
pub struct ZeroProductCancelBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SignOfNegation: sign(0 - a) = 0 - sign(a).
// Example: have a R; trust sign(a) $in R; sign(0 - a) = 0 - sign(a).
pub struct SignOfNegationBuiltinRuleProof {}

// Builtin SignTimesAbsEqualsArg: sign(a) * abs(a) = a.
// Example: have a R; sign(a) * abs(a) = a.
pub struct SignTimesAbsEqualsArgBuiltinRuleProof {}

// Builtin AbsEqualsSignTimesArg: abs(a) = sign(a) * a.
// Example: have a R; trust sign(a) $in R; abs(a) = sign(a) * a.
pub struct AbsEqualsSignTimesArgBuiltinRuleProof {}

// Builtin SignOfProduct: sign(a * b) = sign(a) * sign(b).
// Example: have a R; have b R; trust sign(a) $in R; trust sign(b) $in R;
//          sign(a * b) = sign(a) * sign(b).
pub struct SignOfProductBuiltinRuleProof {}

// Builtin SubtractionFromKnownAddition: a = c - b from known a + b = c.
// Example: have a R; have b R; have c R; trust a + b = c; a = c - b.
pub struct SubtractionFromKnownAdditionBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave7BuiltinRuleProof {
    GcdDividesArgument(GcdDividesArgumentBuiltinRuleProof),
    ProductModFactorZero(ProductModFactorZeroBuiltinRuleProof),
    EqualityFromTwoSidedWeakOrder(EqualityFromTwoSidedWeakOrderBuiltinRuleProof),
    DiffZeroFromEqualOperands(DiffZeroFromEqualOperandsBuiltinRuleProof),
    ZeroProductCancel(ZeroProductCancelBuiltinRuleProof),
    SignOfNegation(SignOfNegationBuiltinRuleProof),
    SignTimesAbsEqualsArg(SignTimesAbsEqualsArgBuiltinRuleProof),
    AbsEqualsSignTimesArg(AbsEqualsSignTimesArgBuiltinRuleProof),
    SignOfProduct(SignOfProductBuiltinRuleProof),
    SubtractionFromKnownAddition(SubtractionFromKnownAdditionBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave7(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave7BuiltinRuleProof>> {
        let child = verify_state.without_well_defined_storage();
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if gcd_divides_argument_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave7BuiltinRuleProof::GcdDividesArgument(
                    GcdDividesArgumentBuiltinRuleProof {},
                )));
            }
            if product_mod_factor_zero_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave7BuiltinRuleProof::ProductModFactorZero(
                        ProductModFactorZeroBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(p) = self.try_sign_of_negation(left, right)? {
                return Ok(Some(EqualityIdentitiesWave7BuiltinRuleProof::SignOfNegation(p)));
            }
            if let Some(p) = self.try_sign_times_abs_equals_arg(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave7BuiltinRuleProof::SignTimesAbsEqualsArg(p),
                ));
            }
            if let Some(p) = self.try_abs_equals_sign_times_arg(left, right)? {
                return Ok(Some(
                    EqualityIdentitiesWave7BuiltinRuleProof::AbsEqualsSignTimesArg(p),
                ));
            }
            if let Some(p) = self.try_sign_of_product(left, right)? {
                return Ok(Some(EqualityIdentitiesWave7BuiltinRuleProof::SignOfProduct(p)));
            }
        }
        if let Some(p) = self.try_equality_from_two_sided_weak_order(fact, child.clone())? {
            return Ok(Some(
                EqualityIdentitiesWave7BuiltinRuleProof::EqualityFromTwoSidedWeakOrder(p),
            ));
        }
        if let Some(p) = self.try_diff_zero_from_equal_operands(fact, child.clone())? {
            return Ok(Some(
                EqualityIdentitiesWave7BuiltinRuleProof::DiffZeroFromEqualOperands(p),
            ));
        }
        if let Some(p) = self.try_zero_product_cancel(fact, child.clone())? {
            return Ok(Some(EqualityIdentitiesWave7BuiltinRuleProof::ZeroProductCancel(
                p,
            )));
        }
        if let Some(p) = self.try_subtraction_from_known_addition(fact, child)? {
            return Ok(Some(
                EqualityIdentitiesWave7BuiltinRuleProof::SubtractionFromKnownAddition(p),
            ));
        }
        Ok(None)
    }

    fn try_sign_of_negation(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<SignOfNegationBuiltinRuleProof>> {
        let Some(arg) = match_sign(left) else {
            return Ok(None);
        };
        let Some(inner) = match_negation(arg) else {
            return Ok(None);
        };
        let Some(neg_sign_arg) = match_negation(right) else {
            return Ok(None);
        };
        let Some(sign_arg) = match_sign(neg_sign_arg) else {
            return Ok(None);
        };
        if inner.ir() == sign_arg.ir() {
            return Ok(Some(SignOfNegationBuiltinRuleProof {}));
        }
        Ok(None)
    }

    fn try_sign_times_abs_equals_arg(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<SignTimesAbsEqualsArgBuiltinRuleProof>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: m1,
            right: m2,
        })) = left
        else {
            return Ok(None);
        };
        let pairs = [(m1.as_ref(), m2.as_ref()), (m2.as_ref(), m1.as_ref())];
        for (s, a) in pairs {
            let Some(sign_arg) = match_sign(s) else {
                continue;
            };
            let Some(abs_arg) = match_abs(a) else {
                continue;
            };
            if sign_arg.ir() == abs_arg.ir() && sign_arg.ir() == right.ir() {
                return Ok(Some(SignTimesAbsEqualsArgBuiltinRuleProof {}));
            }
        }
        Ok(None)
    }

    fn try_abs_equals_sign_times_arg(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<AbsEqualsSignTimesArgBuiltinRuleProof>> {
        let Some(abs_arg) = match_abs(left) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: m1,
            right: m2,
        })) = right
        else {
            return Ok(None);
        };
        let pairs = [(m1.as_ref(), m2.as_ref()), (m2.as_ref(), m1.as_ref())];
        for (s, a) in pairs {
            let Some(sign_arg) = match_sign(s) else {
                continue;
            };
            if sign_arg.ir() == abs_arg.ir() && a.ir() == abs_arg.ir() {
                return Ok(Some(AbsEqualsSignTimesArgBuiltinRuleProof {}));
            }
        }
        Ok(None)
    }

    fn try_sign_of_product(
        &mut self,
        left: &Obj,
        right: &Obj,
    ) -> RuntimeResult<Option<SignOfProductBuiltinRuleProof>> {
        let Some(arg) = match_sign(left) else {
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
            left: m1,
            right: m2,
        })) = right
        else {
            return Ok(None);
        };
        let pairs = [(m1.as_ref(), m2.as_ref()), (m2.as_ref(), m1.as_ref())];
        for (s1, s2) in pairs {
            let Some(x) = match_sign(s1) else {
                continue;
            };
            let Some(y) = match_sign(s2) else {
                continue;
            };
            if (x.ir() == a.ir() && y.ir() == b.ir()) || (x.ir() == b.ir() && y.ir() == a.ir()) {
                return Ok(Some(SignOfProductBuiltinRuleProof {}));
            }
        }
        Ok(None)
    }

    fn try_equality_from_two_sided_weak_order(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityFromTwoSidedWeakOrderBuiltinRuleProof>> {
        // Only cite already-known weak orders. Full verify_fact here re-enters
        // equality search and can stack-overflow on goals like min(a,a)=a.
        let Some(cite_ab) = self.known_less_equal_fact_id(&fact.left, &fact.right) else {
            return Ok(None);
        };
        let Some(cite_ba) = self.known_less_equal_fact_id(&fact.right, &fact.left) else {
            return Ok(None);
        };
        let _ = (cite_ab, cite_ba);
        Ok(Some(EqualityFromTwoSidedWeakOrderBuiltinRuleProof {
            proof_of_requirement_facts: Vec::new(),
        }))
    }

    fn try_diff_zero_from_equal_operands(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<DiffZeroFromEqualOperandsBuiltinRuleProof>> {
        let Some((x, y)) = (if is_zero_obj(&fact.left) {
            match_sub(&fact.right)
        } else if is_zero_obj(&fact.right) {
            match_sub(&fact.left)
        } else {
            None
        }) else {
            return Ok(None);
        };
        let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: x.clone(),
            right: y.clone(),
            line_file: None,
        }));
        let proof = self.verify_fact(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(DiffZeroFromEqualOperandsBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_zero_product_cancel(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ZeroProductCancelBuiltinRuleProof>> {
        let target = if is_zero_obj(&fact.left) {
            &fact.right
        } else if is_zero_obj(&fact.right) {
            &fact.left
        } else {
            return Ok(None);
        };
        let zero = zero_obj();
        let adjacency = self.visible_equivalence_class_adjacency();
        for key in self.equivalence_class_keys(&zero) {
            let Some(neighbors) = adjacency.get(&key) else {
                continue;
            };
            for (_, equal_fact) in neighbors.iter() {
                for side in [&equal_fact.left, &equal_fact.right] {
                    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                        left: f1,
                        right: f2,
                    })) = side
                    else {
                        continue;
                    };
                    for (factor, other) in
                        [(f1.as_ref(), f2.as_ref()), (f2.as_ref(), f1.as_ref())]
                    {
                        if factor.ir() != target.ir() {
                            continue;
                        }
                        let nonzero = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: other.clone(),
                            right: zero.clone(),
                            line_file: None,
                        }));
                        let nz_proof = self.verify_fact(&nonzero, verify_state.clone())?;
                        if nz_proof.is_failed() {
                            continue;
                        }
                        let product_zero = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: side.clone(),
                            right: zero.clone(),
                            line_file: None,
                        }));
                        let pz_proof = self.verify_fact(&product_zero, verify_state.clone())?;
                        if pz_proof.is_failed() {
                            continue;
                        }
                        return Ok(Some(ZeroProductCancelBuiltinRuleProof {
                            proof_of_requirement_facts: vec![pz_proof, nz_proof],
                        }));
                    }
                }
            }
        }
        Ok(None)
    }

    fn try_subtraction_from_known_addition(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubtractionFromKnownAdditionBuiltinRuleProof>> {
        for (target, other) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some((c, b)) = match_sub(other) else {
                continue;
            };
            // target = c - b  from  target + b = c  (or b + target = c)
            let sum1 = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(target.clone()),
                right: Box::new(b.clone()),
            }));
            let sum2 = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: Box::new(b.clone()),
                right: Box::new(target.clone()),
            }));
            for sum in [sum1, sum2] {
                let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: sum,
                    right: c.clone(),
                    line_file: None,
                }));
                let proof = self.verify_fact(&premise, verify_state.clone())?;
                if proof.is_failed() {
                    continue;
                }
                return Ok(Some(SubtractionFromKnownAdditionBuiltinRuleProof {
                    proof_of_requirement_facts: vec![proof],
                }));
            }
        }
        Ok(None)
    }
}

fn gcd_divides_argument_shape(remainder: &Obj, zero: &Obj) -> bool {
    if !is_zero_obj(zero) {
        return false;
    }
    let Some((dividend, modulus)) = match_mod(remainder) else {
        return false;
    };
    let Some((g1, g2)) = match_gcd(modulus) else {
        return false;
    };
    dividend.ir() == g1.ir() || dividend.ir() == g2.ir()
}

fn product_mod_factor_zero_shape(remainder: &Obj, zero: &Obj) -> bool {
    if !is_zero_obj(zero) {
        return false;
    }
    let Some((dividend, modulus)) = match_mod(remainder) else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: a,
        right: b,
    })) = dividend
    else {
        return false;
    };
    modulus.ir() == a.ir() || modulus.ir() == b.ir()
}

fn match_mod(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_gcd(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Gcd(Gcd { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_sign(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign { arg })) => Some(arg.as_ref()),
        _ => None,
    }
}

fn match_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
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

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}
