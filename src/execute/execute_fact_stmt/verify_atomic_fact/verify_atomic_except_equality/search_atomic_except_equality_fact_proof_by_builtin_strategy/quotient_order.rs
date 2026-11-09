use super::helper::{one_obj, zero_obj};
use super::result::*;
use crate::prelude::*;

pub struct QuotientUnitLessProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct QuotientUnitLessEqualProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct QuotientScaleLessProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct QuotientScaleLessEqualProof {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub(super) fn search_quotient_order(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        let (low, high, strict) = match fact {
            AtomicFact::LessFact(f) => (&f.left, &f.right, true),
            AtomicFact::GreaterFact(f) => (&f.right, &f.left, true),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false),
            AtomicFact::GreaterEqualFact(f) => (&f.right, &f.left, false),
            _ => return Ok(None),
        };
        let Some((div, other, quotient_is_low)) = quotient_endpoint(low, high) else {
            return Ok(None);
        };
        if other == one_obj() {
            // b > 0: a/b < 1 iff a < b, with the same weak-order version.
            let (low, high) = if quotient_is_low {
                (*div.left.clone(), *div.right.clone())
            } else {
                (*div.right.clone(), *div.left.clone())
            };
            let requirements = vec![
                self.strategy_less_fact(zero_obj(), *div.right, None),
                self.quotient_order_requirement(low, high, strict),
            ];
            let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, state)?
            else {
                return Ok(None);
            };
            return Ok(Some(if strict {
                QuotientUnitLessProof::new(requirement_facts, proof_of_requirement_facts).into()
            } else {
                QuotientUnitLessEqualProof::new(requirement_facts, proof_of_requirement_facts)
                    .into()
            }));
        }
        if other != *div.left {
            return Ok(None);
        }

        // For b > 0, the signs of a and b-1 determine a/b versus a.
        // Example: a > 0 and b > 1 imply a/b < a; a < 0 reverses it.
        for numerator_positive in [true, false] {
            let (sign_low, sign_high) = if numerator_positive {
                (zero_obj(), *div.left.clone())
            } else {
                (*div.left.clone(), zero_obj())
            };
            let denominator_above_one = quotient_is_low == numerator_positive;
            let (factor_low, factor_high) = if denominator_above_one {
                (one_obj(), *div.right.clone())
            } else {
                (*div.right.clone(), one_obj())
            };
            let requirements = vec![
                self.strategy_less_fact(zero_obj(), *div.right.clone(), None),
                self.quotient_order_requirement(sign_low, sign_high, strict),
                self.quotient_order_requirement(factor_low, factor_high, strict),
            ];
            let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, state)?
            else {
                continue;
            };
            return Ok(Some(if strict {
                QuotientScaleLessProof::new(requirement_facts, proof_of_requirement_facts).into()
            } else {
                QuotientScaleLessEqualProof::new(requirement_facts, proof_of_requirement_facts)
                    .into()
            }));
        }
        Ok(None)
    }

    fn quotient_order_requirement(&mut self, low: Obj, high: Obj, strict: bool) -> Fact {
        if strict {
            self.strategy_less_fact(low, high, None)
        } else {
            self.strategy_less_equal_fact(low, high, None)
        }
    }
}

fn quotient_endpoint(low: &Obj, high: &Obj) -> Option<(Div, Obj, bool)> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = low {
        if *high == one_obj() || *high == *div.left {
            return Some((div.clone(), high.clone(), true));
        }
    }
    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = high {
        if *low == one_obj() || *low == *div.left {
            return Some((div.clone(), low.clone(), false));
        }
    }
    None
}

impl QuotientUnitLessProof {
    pub fn new(
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}
impl From<QuotientUnitLessProof> for AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    fn from(proof: QuotientUnitLessProof) -> Self {
        Self::QuotientUnitLess(proof)
    }
}
impl QuotientUnitLessEqualProof {
    pub fn new(
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}
impl From<QuotientUnitLessEqualProof> for AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    fn from(proof: QuotientUnitLessEqualProof) -> Self {
        Self::QuotientUnitLessEqual(proof)
    }
}
impl QuotientScaleLessProof {
    pub fn new(
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}
impl From<QuotientScaleLessProof> for AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    fn from(proof: QuotientScaleLessProof) -> Self {
        Self::QuotientScaleLess(proof)
    }
}
impl QuotientScaleLessEqualProof {
    pub fn new(
        requirement_facts: Vec<Fact>,
        proof_of_requirement_facts: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            requirement_facts,
            proof_of_requirement_facts,
        }
    }
}
impl From<QuotientScaleLessEqualProof> for AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    fn from(proof: QuotientScaleLessEqualProof) -> Self {
        Self::QuotientScaleLessEqual(proof)
    }
}
