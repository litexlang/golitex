//! Narrow arithmetic identities; all semantic premises use the builtin entry.
use crate::ast::fact::{AtomicFact, EqualFact, Fact, GreaterEqualFact, InFact, NotEqualFact};
use crate::ast::obj::{ArithmeticOperator as A, ExpLogOperator, IntegerOperator, Literal, Number, Obj, Pow, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::runtime::{Runtime, RuntimeResult};

pub enum ElementaryArithmeticProof {
    ModNegation {
        requirements: Vec<VerifyFactResult>,
    },
    ModNaturalPower {
        requirements: Vec<VerifyFactResult>,
    },
    AbsEvenPower,
    PositivePowerZero {
        premise: Box<EqualFactSearchedProof>,
        requirements: Vec<VerifyFactResult>,
    },
    PositivePowerCancellation {
        premise: Box<EqualFactSearchedProof>,
        requirements: Vec<VerifyFactResult>,
    },
    SqrtKnownSquare {
        premise: Box<EqualFactSearchedProof>,
        requirements: Vec<VerifyFactResult>,
    },
}
impl ElementaryArithmeticProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::ModNegation { .. } => "ModNegation",
            Self::ModNaturalPower { .. } => "ModNaturalPower",
            Self::AbsEvenPower => "AbsEvenPower",
            Self::PositivePowerZero { .. } => "PositivePowerZero",
            Self::PositivePowerCancellation { .. } => "PositivePowerCancellation",
            Self::SqrtKnownSquare { .. } => "SqrtKnownSquare",
        }
    }
}
impl Runtime {
    pub(super) fn search_elementary_arithmetic(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ElementaryArithmeticProof>> {
        use ElementaryArithmeticProof as P;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            // Positive modulus: (-a)%m = (m-a%m)%m.
            if let (Some((dividend, m)), Some((other, modulus))) = (mod_args(left), mod_args(right))
            {
                if same(m, modulus) {
                    if let (Some(a), Obj::ArithmeticOperator(A::Sub(s))) =
                        (neg_arg(dividend), other)
                    {
                        if same(&s.left, m)
                            && mod_args(&s.right).is_some_and(|(x, k)| same(x, a) && same(k, m))
                        {
                            let requirements = self.elementary_members(
                                &[(a, StandardSet::Z), (m, StandardSet::NPos)],
                                state.clone(),
                            )?;
                            if requirements.iter().all(|r| !r.is_failed()) {
                                return Ok(Some(P::ModNegation { requirements }));
                            }
                        }
                    }
                    // Integer powers preserve congruence for natural exponents.
                    if let (Some((a, n)), Some((b, k))) = (pow_args(dividend), pow_args(other)) {
                        if same(n, k) && mod_args(b).is_some_and(|(x, d)| same(x, a) && same(d, m))
                        {
                            let requirements = self.elementary_members(
                                &[
                                    (a, StandardSet::Z),
                                    (m, StandardSet::NPos),
                                    (n, StandardSet::N),
                                ],
                                state.clone(),
                            )?;
                            if requirements.iter().all(|r| !r.is_failed()) {
                                return Ok(Some(P::ModNaturalPower { requirements }));
                            }
                        }
                    }
                }
            }
            // |x|^(2k)=x^(2k); literal positive even exponents only.
            if let (Some((Obj::ArithmeticOperator(A::Abs(a)), n)), Some((x, k))) =
                (pow_args(left), pow_args(right))
            {
                if same(&a.arg, x)
                    && same(n, k)
                    && literal_integer(n).is_some_and(|v| v > 0 && v % 2 == 0)
                {
                    return Ok(Some(P::AbsEvenPower));
                }
            }
            // Consume a stored x^n=0, never synthesize a power-zero premise.
            if is_number(right, "0") {
                let zero = number("0");
                let members = equivalence_class_members_with_paths_in_adjacency(
                    &self.visible_equivalence_class_adjacency(),
                    &zero,
                );
                for (power, _) in members {
                    let Some((base, n)) = pow_args(&power) else {
                        continue;
                    };
                    if !same(base, left) {
                        continue;
                    }
                    let requirements = self.elementary_members(
                        &[(base, StandardSet::C), (n, StandardSet::NPos)],
                        state.clone(),
                    )?;
                    if requirements.iter().any(VerifyFactResult::is_failed) {
                        continue;
                    }
                    if let Some(premise) = self.lookup_known_obj_equality(&power, &zero) {
                        return Ok(Some(P::PositivePowerZero {
                            premise: Box::new(premise),
                            requirements,
                        }));
                    }
                }
            }
            // Principal sqrt consumes x=y^2 only with y>=0.
            if let Obj::ExpLogOperator(ExpLogOperator::Sqrt(s)) = left {
                let squared = Obj::ArithmeticOperator(A::Pow(Pow {
                    base: Box::new(right.clone()),
                    exponent: Box::new(number("2")),
                }));
                if let Some(premise) = self.lookup_known_obj_equality(&s.arg, &squared) {
                    let mut requirements =
                        self.elementary_members(&[(right, StandardSet::R)], state.clone())?;
                    let nonnegative =
                        Fact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact {
                            fact_id: self.global_ids.allocate_fact_id(),
                            left: right.clone(),
                            right: number("0"),
                            line_file: None,
                        }));
                    requirements
                        .push(self.verify_builtin_rule_premise(&nonnegative, state.clone())?);
                    if requirements.iter().all(|r| !r.is_failed()) {
                        return Ok(Some(P::SqrtKnownSquare {
                            premise: Box::new(premise),
                            requirements,
                        }));
                    }
                }
            }
        }
        // A positive base has an injective nonzero integer power. Inspect only
        // already stored equalities; no global rewrite or exponent search.
        let adjacency = self.visible_equivalence_class_adjacency();
        for neighbors in adjacency.values() {
            for (_, known) in neighbors {
                for (a, b) in [(&known.left, &known.right), (&known.right, &known.left)] {
                    let (Some((x, n)), Some((y, k))) = (pow_args(a), pow_args(b)) else {
                        continue;
                    };
                    if !same(x, &fact.left)
                        || !same(y, &fact.right)
                        || !same(n, k)
                    {
                        continue;
                    }
                    let mut requirements = self.elementary_members(
                        &[(x, StandardSet::RPos), (y, StandardSet::RPos), (n, StandardSet::Z)],
                        state,
                    )?;
                    let nonzero: Fact = NotEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: n.clone(), right: number("0"), line_file: None,
                    }.into();
                    requirements.push(self.verify_builtin_rule_premise(&nonzero, state)?);
                    if requirements.iter().any(VerifyFactResult::is_failed) {
                        continue;
                    }
                    if let Some(premise) = self.lookup_known_obj_equality(a, b) {
                        return Ok(Some(P::PositivePowerCancellation {
                            premise: Box::new(premise),
                            requirements,
                        }));
                    }
                }
            }
        }
        Ok(None)
    }
    fn elementary_members(
        &mut self,
        requirements: &[(&Obj, StandardSet)],
        state: VerifyState,
    ) -> RuntimeResult<Vec<VerifyFactResult>> {
        let mut result = Vec::new();
        for (obj, set) in requirements {
            let fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: (*obj).clone(),
                set: Obj::StandardSet(set.clone()),
                line_file: None,
            }));
            result.push(self.verify_builtin_rule_premise(&fact, state.clone())?);
        }
        Ok(result)
    }
}
fn same(a: &Obj, b: &Obj) -> bool {
    a.ir() == b.ir()
}
fn number(n: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.into())))
}
fn is_number(o: &Obj, n: &str) -> bool {
    matches!(o,Obj::Literal(Literal::Number(v)) if v.normalized_value==n)
}
fn literal_integer(o: &Obj) -> Option<i128> {
    if let Obj::Literal(Literal::Number(v)) = o {
        v.normalized_value.parse().ok()
    } else {
        None
    }
}
fn mod_args(o: &Obj) -> Option<(&Obj, &Obj)> {
    if let Obj::IntegerOperator(IntegerOperator::Mod(v)) = o {
        Some((&v.left, &v.right))
    } else {
        None
    }
}
fn pow_args(o: &Obj) -> Option<(&Obj, &Obj)> {
    if let Obj::ArithmeticOperator(A::Pow(v)) = o {
        Some((&v.base, &v.exponent))
    } else {
        None
    }
}
fn neg_arg(o: &Obj) -> Option<&Obj> {
    match o {
        Obj::ArithmeticOperator(A::Neg(v)) => Some(&v.arg),
        Obj::ArithmeticOperator(A::Sub(v)) if is_number(&v.left, "0") => Some(&v.right),
        _ => None,
    }
}
