//! The divisibility parts of the gcd/lcm universal properties.
use crate::ast::fact::{EqualFact, Fact, InFact};
use crate::ast::obj::{IntegerOperator, Literal, Mod, Number, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct GcdCommonDivisorProof {
    pub divisor_positive: VerifyFactResult,
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}

pub struct LcmCommonMultipleProof {
    pub first_positive: VerifyFactResult,
    pub second_positive: VerifyFactResult,
    pub first_divisibility: VerifyFactResult,
    pub second_divisibility: VerifyFactResult,
}

impl Runtime {
    // Whole-fact WD supplies integer operands and excludes gcd(0,0).
    // Example: d in N+, a%d=0, b%d=0 => gcd(a,b)%d=0.
    pub(super) fn search_gcd_common_divisor(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<GcdCommonDivisorProof>> {
        for (remainder, zero) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if zero.ir() != zero_obj().ir() {
                continue;
            }
            let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = remainder else {
                continue;
            };
            let Obj::IntegerOperator(IntegerOperator::Gcd(gcd)) = &*rem.left else {
                continue;
            };
            let domain: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: *rem.right.clone(),
                set: Obj::StandardSet(StandardSet::NPos),
                line_file: fact.line_file.clone(),
            }
            .into();
            let divisor_positive = self.verify_builtin_rule_premise(&domain, state)?;
            if divisor_positive.is_failed() {
                continue;
            }
            let first: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: gcd.left.clone(),
                    right: rem.right.clone(),
                })),
                right: zero_obj(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let first_divisibility = self.verify_builtin_rule_premise(&first, state)?;
            if first_divisibility.is_failed() {
                continue;
            }
            let second: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: gcd.right.clone(),
                    right: rem.right.clone(),
                })),
                right: zero_obj(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let second_divisibility = self.verify_builtin_rule_premise(&second, state)?;
            if !second_divisibility.is_failed() {
                return Ok(Some(GcdCommonDivisorProof {
                    divisor_positive,
                    first_divisibility,
                    second_divisibility,
                }));
            }
        }
        Ok(None)
    }

    // Example: a,b in N+, m%a=0, m%b=0 => m%lcm(a,b)=0.
    // The dividend m may be negative or zero; mod WD checks its integer type.
    pub(super) fn search_lcm_common_multiple(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LcmCommonMultipleProof>> {
        for (remainder, zero) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if zero.ir() != zero_obj().ir() {
                continue;
            }
            let Obj::IntegerOperator(IntegerOperator::Mod(rem)) = remainder else {
                continue;
            };
            let Obj::IntegerOperator(IntegerOperator::Lcm(lcm)) = &*rem.right else {
                continue;
            };
            let first_domain: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: *lcm.left.clone(),
                set: Obj::StandardSet(StandardSet::NPos),
                line_file: fact.line_file.clone(),
            }
            .into();
            let first_positive = self.verify_builtin_rule_premise(&first_domain, state)?;
            if first_positive.is_failed() {
                continue;
            }
            let second_domain: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: *lcm.right.clone(),
                set: Obj::StandardSet(StandardSet::NPos),
                line_file: fact.line_file.clone(),
            }
            .into();
            let second_positive = self.verify_builtin_rule_premise(&second_domain, state)?;
            if second_positive.is_failed() {
                continue;
            }
            let first: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: rem.left.clone(),
                    right: lcm.left.clone(),
                })),
                right: zero_obj(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let first_divisibility = self.verify_builtin_rule_premise(&first, state)?;
            if first_divisibility.is_failed() {
                continue;
            }
            let second: Fact = EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: rem.left.clone(),
                    right: lcm.right.clone(),
                })),
                right: zero_obj(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let second_divisibility = self.verify_builtin_rule_premise(&second, state)?;
            if !second_divisibility.is_failed() {
                return Ok(Some(LcmCommonMultipleProof {
                    first_positive,
                    second_positive,
                    first_divisibility,
                    second_divisibility,
                }));
            }
        }
        Ok(None)
    }
}

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number::new("0".into())))
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/common_obj_relations/tests.rs"]
mod common_obj_relations_tests;
