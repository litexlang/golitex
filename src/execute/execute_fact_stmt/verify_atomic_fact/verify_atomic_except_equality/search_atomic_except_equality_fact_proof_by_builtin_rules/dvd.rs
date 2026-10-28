//! Native divisibility rules. All operands are already WD integers and the
//! divisor is nonzero. Match existing syntax only; never search for a multiplier.
use crate::prelude::*;

pub enum DvdFactSearchProofByBuiltinRule {
    Add(DvdAddProof),
    Subtract(DvdSubtractProof),
    Scale(DvdScaleProof),
    LinearCombination(DvdLinearCombinationProof),

    Zero(DvdZeroProof),
    One(DvdOneProof),
    SelfDivisor(DvdSelfProof),
    ProductFactor(DvdProductFactorProof),
    GcdArgument(DvdGcdArgumentProof),
    LcmArgument(DvdLcmArgumentProof),
    DividendMinusRemainder(DvdDividendMinusRemainderProof),
    GcdCommonDivisor(DvdGcdCommonDivisorProof),
    LcmCommonMultiple(DvdLcmCommonMultipleProof),
    Factorial(DvdFactorialProof),
}
pub struct DvdZeroProof;
pub struct DvdOneProof;
pub struct DvdSelfProof;
pub struct DvdProductFactorProof {
    pub multiplier_integer: VerifyFactResult,
}
pub struct DvdGcdArgumentProof;
pub struct DvdLcmArgumentProof;
pub struct DvdDividendMinusRemainderProof;
pub struct DvdGcdCommonDivisorProof {
    pub divisor_positive: VerifyFactResult,
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}
pub struct DvdLcmCommonMultipleProof {
    pub first_positive: VerifyFactResult,
    pub second_positive: VerifyFactResult,
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}
pub struct DvdFactorialProof {
    pub earlier_natural: VerifyFactResult,
    pub later_natural: VerifyFactResult,
    pub order: VerifyFactResult,
}

pub struct DvdAddProof {
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}
impl DvdAddProof {
    pub fn new(
        first_divisibility: VerifyFactResult,
        second_divisibility: VerifyFactResult,
    ) -> Self {
        Self {
            first_divisibility,
            second_divisibility,
        }
    }
}
pub struct DvdSubtractProof {
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}
impl DvdSubtractProof {
    pub fn new(
        first_divisibility: VerifyFactResult,
        second_divisibility: VerifyFactResult,
    ) -> Self {
        Self {
            first_divisibility,
            second_divisibility,
        }
    }
}
pub struct DvdScaleProof {
    pub multiplier_integer: VerifyFactResult,
    pub divisibility: VerifyFactResult,
}
impl DvdScaleProof {
    pub fn new(multiplier_integer: VerifyFactResult, divisibility: VerifyFactResult) -> Self {
        Self {
            multiplier_integer,
            divisibility,
        }
    }
}
pub struct DvdLinearCombinationProof {
    pub first_coefficient_integer: VerifyFactResult,
    pub second_coefficient_integer: VerifyFactResult,
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}
impl DvdLinearCombinationProof {
    pub fn new(
        first_coefficient_integer: VerifyFactResult,
        second_coefficient_integer: VerifyFactResult,
        first_divisibility: VerifyFactResult,
        second_divisibility: VerifyFactResult,
    ) -> Self {
        Self {
            first_coefficient_integer,
            second_coefficient_integer,
            first_divisibility,
            second_divisibility,
        }
    }
}

impl Runtime {
    pub fn search_dvd_fact_proof_by_builtin_rule(
        &mut self,
        fact: &DvdFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<DvdFactSearchProofByBuiltinRule>> {
        use DvdFactSearchProofByBuiltinRule as P;
        let a = &fact.left;
        let d = &fact.right;
        if a.ir() == dvd_number("0").ir() {
            return Ok(Some(P::Zero(DvdZeroProof)));
        }
        if d.ir() == dvd_number("1").ir() {
            return Ok(Some(P::One(DvdOneProof)));
        }
        if a.ir() == d.ir() {
            return Ok(Some(P::SelfDivisor(DvdSelfProof)));
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = a {
            let other = if product.left.ir() == d.ir() {
                Some(&*product.right)
            } else if product.right.ir() == d.ir() {
                Some(&*product.left)
            } else {
                None
            };
            if let Some(other) = other {
                let multiplier_integer = self.dvd_member(other, StandardSet::Z, state)?;
                if !multiplier_integer.is_failed() {
                    return Ok(Some(P::ProductFactor(DvdProductFactorProof {
                        multiplier_integer,
                    })));
                }
            }
        }
        if let Obj::IntegerOperator(IntegerOperator::Gcd(gcd)) = d {
            if a.ir() == gcd.left.ir() || a.ir() == gcd.right.ir() {
                return Ok(Some(P::GcdArgument(DvdGcdArgumentProof)));
            }
        }
        if let Obj::IntegerOperator(IntegerOperator::Lcm(lcm)) = a {
            if let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = d {
                if abs.arg.ir() == lcm.left.ir() || abs.arg.ir() == lcm.right.ir() {
                    return Ok(Some(P::LcmArgument(DvdLcmArgumentProof)));
                }
            }
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = a {
            if let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = &*sub.right {
                if sub.left.ir() == rem.left.ir() && d.ir() == rem.right.ir() {
                    return Ok(Some(P::DividendMinusRemainder(
                        DvdDividendMinusRemainderProof,
                    )));
                }
            }
        }
        if let Obj::IntegerOperator(IntegerOperator::Gcd(gcd)) = a {
            let divisor_positive = self.dvd_member(d, StandardSet::NPos, state)?;
            if !divisor_positive.is_failed() {
                let first_divisibility = self.dvd_premise(&gcd.left, d, state)?;
                if !first_divisibility.is_failed() {
                    let second_divisibility = self.dvd_premise(&gcd.right, d, state)?;
                    if !second_divisibility.is_failed() {
                        return Ok(Some(P::GcdCommonDivisor(DvdGcdCommonDivisorProof {
                            divisor_positive,
                            first_divisibility,
                            second_divisibility,
                        })));
                    }
                }
            }
        }
        if let Obj::IntegerOperator(IntegerOperator::Lcm(lcm)) = d {
            let first_positive = self.dvd_member(&lcm.left, StandardSet::NPos, state)?;
            if !first_positive.is_failed() {
                let second_positive = self.dvd_member(&lcm.right, StandardSet::NPos, state)?;
                if !second_positive.is_failed() {
                    let first_divisibility = self.dvd_premise(a, &lcm.left, state)?;
                    if !first_divisibility.is_failed() {
                        let second_divisibility = self.dvd_premise(a, &lcm.right, state)?;
                        if !second_divisibility.is_failed() {
                            return Ok(Some(P::LcmCommonMultiple(DvdLcmCommonMultipleProof {
                                first_positive,
                                second_positive,
                                first_divisibility,
                                second_divisibility,
                            })));
                        }
                    }
                }
            }
        }
        if let (
            Obj::IntegerOperator(IntegerOperator::Factorial(n)),
            Obj::IntegerOperator(IntegerOperator::Factorial(m)),
        ) = (a, d)
        {
            let earlier_natural = self.dvd_member(&m.arg, StandardSet::N, state)?;
            if !earlier_natural.is_failed() {
                let later_natural = self.dvd_member(&n.arg, StandardSet::N, state)?;
                if !later_natural.is_failed() {
                    let bound: Fact = LessEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: *m.arg.clone(),
                        right: *n.arg.clone(),
                        line_file: None,
                    }
                    .into();
                    let order = self.verify_builtin_rule_premise(&bound, state)?;
                    if !order.is_failed() {
                        return Ok(Some(P::Factorial(DvdFactorialProof {
                            earlier_natural,
                            later_natural,
                            order,
                        })));
                    }
                }
            }
        }
        // Exact linear combination: the supplied coefficients must be integers.
        // Example: $dvd(a,d),$dvd(b,d),u,v in Z => $dvd(u*a+v*b,d).
        if let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = a {
            if let (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(first)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(second)),
            ) = (&*sum.left, &*sum.right)
            {
                let u = self.dvd_member(&first.left, StandardSet::Z, state)?;
                if !u.is_failed() {
                    let v = self.dvd_member(&second.left, StandardSet::Z, state)?;
                    if !v.is_failed() {
                        let first_divisibility = self.dvd_premise(&first.right, d, state)?;
                        if !first_divisibility.is_failed() {
                            let second_divisibility = self.dvd_premise(&second.right, d, state)?;
                            if !second_divisibility.is_failed() {
                                return Ok(Some(
                                    DvdLinearCombinationProof::new(
                                        u,
                                        v,
                                        first_divisibility,
                                        second_divisibility,
                                    )
                                    .into(),
                                ));
                            }
                        }
                    }
                }
            }
        }
        // Addition and subtraction preserve a common divisor; no multiplier search.
        // Example: $dvd(a,d),$dvd(b,d) => $dvd(a-b,d).
        let pair = match a {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
                Some((&*p.left, &*p.right, true))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
                Some((&*p.left, &*p.right, false))
            }
            _ => None,
        };
        if let Some((first, second, add)) = pair {
            let first = self.dvd_premise(first, d, state)?;
            if !first.is_failed() {
                let second = self.dvd_premise(second, d, state)?;
                if !second.is_failed() {
                    return Ok(Some(if add {
                        DvdAddProof::new(first, second).into()
                    } else {
                        DvdSubtractProof::new(first, second).into()
                    }));
                }
            }
        }
        // Integer scaling preserves divisibility in either product orientation.
        // Example: k in Z, $dvd(a,d) => $dvd(k*a,d).
        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = a {
            for (k, x) in [
                (&*product.left, &*product.right),
                (&*product.right, &*product.left),
            ] {
                let multiplier = self.dvd_member(k, StandardSet::Z, state)?;
                if multiplier.is_failed() {
                    continue;
                }
                let divisibility = self.dvd_premise(x, d, state)?;
                if !divisibility.is_failed() {
                    return Ok(Some(DvdScaleProof::new(multiplier, divisibility).into()));
                }
            }
        }
        Ok(None)
    }

    fn dvd_member(
        &mut self,
        a: &Obj,
        set: StandardSet,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: a.clone(),
            set: Obj::StandardSet(set),
            line_file: None,
        }
        .into();
        self.verify_builtin_rule_premise(&fact, state)
    }

    fn dvd_premise(
        &mut self,
        a: &Obj,
        d: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact: Fact = DvdFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: a.clone(),
            right: d.clone(),
            line_file: None,
        }
        .into();
        self.verify_builtin_rule_premise(&fact, state)
    }
}

fn dvd_number(s: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(s.into())))
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/dvd_unified.rs"]
mod tests;

impl DvdFactSearchProofByBuiltinRule {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::Add(_) => "DvdAdd",
            Self::Subtract(_) => "DvdSubtract",
            Self::Scale(_) => "DvdScale",
            Self::LinearCombination(_) => "DvdLinearCombination",
            Self::Zero(_) => "DvdZero",
            Self::One(_) => "DvdOne",
            Self::SelfDivisor(_) => "DvdSelf",
            Self::ProductFactor(_) => "DvdProductFactor",
            Self::GcdArgument(_) => "DvdGcdArgument",
            Self::LcmArgument(_) => "DvdLcmArgument",
            Self::DividendMinusRemainder(_) => "DvdDividendMinusRemainder",
            Self::GcdCommonDivisor(_) => "DvdGcdCommonDivisor",
            Self::LcmCommonMultiple(_) => "DvdLcmCommonMultiple",
            Self::Factorial(_) => "DvdFactorial",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::Add(_) => "$dvd(a,d), $dvd(b,d) => $dvd(a+b,d)",
            Self::Subtract(_) => "$dvd(a,d), $dvd(b,d) => $dvd(a-b,d)",
            Self::Scale(_) => "k in Z, $dvd(a,d) => $dvd(k*a,d)",
            Self::LinearCombination(_) => "u,v in Z, $dvd(a,d), $dvd(b,d) => $dvd(u*a+v*b,d)",
            Self::Zero(_) => "$dvd(0,d)",
            Self::One(_) => "$dvd(a,1)",
            Self::SelfDivisor(_) => "$dvd(a,a)",
            Self::ProductFactor(_) => "a,k in Z, a!=0 => $dvd(a*k,a)",
            Self::GcdArgument(_) => "$dvd(a,gcd(a,b)); $dvd(b,gcd(a,b))",
            Self::LcmArgument(_) => "$dvd(lcm(a,b),abs(a)); $dvd(lcm(a,b),abs(b))",
            Self::DividendMinusRemainder(_) => "$dvd(a-a%d,d)",
            Self::GcdCommonDivisor(_) => "d in N+, $dvd(a,d), $dvd(b,d) => $dvd(gcd(a,b),d)",
            Self::LcmCommonMultiple(_) => "a,b in N+, $dvd(m,a), $dvd(m,b) => $dvd(m,lcm(a,b))",
            Self::Factorial(_) => "m,n in N, m<=n => $dvd(n!,m!)",
        }
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/common_obj_relations/tests.rs"]
mod common_obj_relations_tests;

impl From<DvdAddProof> for DvdFactSearchProofByBuiltinRule {
    fn from(proof: DvdAddProof) -> Self {
        Self::Add(proof)
    }
}

impl From<DvdSubtractProof> for DvdFactSearchProofByBuiltinRule {
    fn from(proof: DvdSubtractProof) -> Self {
        Self::Subtract(proof)
    }
}

impl From<DvdScaleProof> for DvdFactSearchProofByBuiltinRule {
    fn from(proof: DvdScaleProof) -> Self {
        Self::Scale(proof)
    }
}

impl From<DvdLinearCombinationProof> for DvdFactSearchProofByBuiltinRule {
    fn from(proof: DvdLinearCombinationProof) -> Self {
        Self::LinearCombination(proof)
    }
}
