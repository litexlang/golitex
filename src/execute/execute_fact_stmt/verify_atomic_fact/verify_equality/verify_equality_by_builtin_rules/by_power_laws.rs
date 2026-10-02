//! Equality power-law builtins (Stage B wave 1).
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, NotEqualFact};
use crate::ast::obj::{
    Add, ArithmeticOperator, Div, Literal, Mul, Neg, Number, Obj, Pow, StandardSet, Sub,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin PowerProductSameBase: a^m * a^n = a^(m+n).
// Mathematical property: product of powers with a common base adds exponents.
// Example: with a R+, m N, n N: a^m * a^n = a^(m + n).
pub struct PowerProductSameBaseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin PowerOfPower: (a^m)^n = a^(m*n).
// Mathematical property: iterated exponentiation multiplies exponents.
// Example: with a R+, m N, n N: (a^m)^n = a^(m * n).
pub struct PowerOfPowerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin PowerOfProduct: (a*b)^n = a^n * b^n.
// Mathematical property: power distributes over a product.
// Example: with a R+, b R+, n N: (a * b)^n = a^n * b^n.
pub struct PowerOfProductBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ReciprocalAsNegOnePower: 1 / a = a^(-1).
// Mathematical property: reciprocal is the power with exponent -1.
// Example: with a R*: 1 / a = a^(-1).
pub struct ReciprocalAsNegOnePowerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin QuotientAsMulNegOnePower: a / b = a * b^(-1).
// Mathematical property: quotient is multiplication by the reciprocal.
// Example: with a R, b R*: a / b = a * b^(-1).
pub struct QuotientAsMulNegOnePowerBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum PowerLawEqualityBuiltinRuleProof {
    PowerProductSameBase(PowerProductSameBaseBuiltinRuleProof),
    PowerOfPower(PowerOfPowerBuiltinRuleProof),
    PowerOfProduct(PowerOfProductBuiltinRuleProof),
    ReciprocalAsNegOnePower(ReciprocalAsNegOnePowerBuiltinRuleProof),
    QuotientAsMulNegOnePower(QuotientAsMulNegOnePowerBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_power_laws(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowerLawEqualityBuiltinRuleProof>> {
        let child = verify_state.without_well_defined_storage();
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(proof) =
                self.try_power_product_same_base(left, right, child.clone())?
            {
                return Ok(Some(PowerLawEqualityBuiltinRuleProof::PowerProductSameBase(
                    proof,
                )));
            }
            if let Some(proof) = self.try_power_of_power(left, right, child.clone())? {
                return Ok(Some(PowerLawEqualityBuiltinRuleProof::PowerOfPower(proof)));
            }
            if let Some(proof) = self.try_power_of_product(left, right, child.clone())? {
                return Ok(Some(PowerLawEqualityBuiltinRuleProof::PowerOfProduct(proof)));
            }
            if let Some(proof) =
                self.try_reciprocal_as_neg_one_power(left, right, child.clone())?
            {
                return Ok(Some(
                    PowerLawEqualityBuiltinRuleProof::ReciprocalAsNegOnePower(proof),
                ));
            }
            if let Some(proof) =
                self.try_quotient_as_mul_neg_one_power(left, right, child.clone())?
            {
                return Ok(Some(
                    PowerLawEqualityBuiltinRuleProof::QuotientAsMulNegOnePower(proof),
                ));
            }
        }
        Ok(None)
    }

    fn try_power_product_same_base(
        &mut self,
        product_side: &Obj,
        combined_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowerProductSameBaseBuiltinRuleProof>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: left_factor,
            right: right_factor,
        })) = product_side
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: combined_base,
            exponent: combined_exp,
        })) = combined_side
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
            left: exp_left,
            right: exp_right,
        })) = combined_exp.as_ref()
        else {
            return Ok(None);
        };

        let candidates = [
            (left_factor.as_ref(), right_factor.as_ref(), exp_left.as_ref(), exp_right.as_ref()),
            (right_factor.as_ref(), left_factor.as_ref(), exp_left.as_ref(), exp_right.as_ref()),
            (left_factor.as_ref(), right_factor.as_ref(), exp_right.as_ref(), exp_left.as_ref()),
            (right_factor.as_ref(), left_factor.as_ref(), exp_right.as_ref(), exp_left.as_ref()),
        ];
        for (f1, f2, e1, e2) in candidates {
            let Some((b1, exp1)) = match_pow(f1) else {
                continue;
            };
            let Some((b2, exp2)) = match_pow(f2) else {
                continue;
            };
            if b1.ir() != combined_base.as_ref().ir() || b2.ir() != combined_base.as_ref().ir() {
                continue;
            }
            if exp1.ir() != e1.ir() || exp2.ir() != e2.ir() {
                continue;
            }
            let Some(proof_of_requirement_facts) = self.verify_power_law_pos_base_nat_exps(
                combined_base.as_ref(),
                &[e1, e2],
                verify_state.clone(),
            )?
            else {
                continue;
            };
            return Ok(Some(PowerProductSameBaseBuiltinRuleProof {
                proof_of_requirement_facts,
            }));
        }
        Ok(None)
    }

    fn try_power_of_power(
        &mut self,
        nested_side: &Obj,
        combined_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowerOfPowerBuiltinRuleProof>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: outer_base,
            exponent: outer_exp,
        })) = nested_side
        else {
            return Ok(None);
        };
        let Some((inner_base, inner_exp)) = match_pow(outer_base.as_ref()) else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: combined_base,
            exponent: combined_exp,
        })) = combined_side
        else {
            return Ok(None);
        };
        if inner_base.ir() != combined_base.as_ref().ir() {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: mul_left,
            right: mul_right,
        })) = combined_exp.as_ref()
        else {
            return Ok(None);
        };
        let exp_match = (mul_left.as_ref().ir() == inner_exp.ir()
            && mul_right.as_ref().ir() == outer_exp.as_ref().ir())
            || (mul_right.as_ref().ir() == inner_exp.ir()
                && mul_left.as_ref().ir() == outer_exp.as_ref().ir());
        if !exp_match {
            return Ok(None);
        }
        let Some(proof_of_requirement_facts) = self.verify_power_law_pos_base_nat_exps(
            combined_base.as_ref(),
            &[inner_exp, outer_exp.as_ref()],
            verify_state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(PowerOfPowerBuiltinRuleProof {
            proof_of_requirement_facts,
        }))
    }

    fn try_power_of_product(
        &mut self,
        product_power_side: &Obj,
        product_of_powers_side: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowerOfProductBuiltinRuleProof>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: product_base,
            exponent: shared_exp,
        })) = product_power_side
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: factor_a,
            right: factor_b,
        })) = product_base.as_ref()
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: left_pow,
            right: right_pow,
        })) = product_of_powers_side
        else {
            return Ok(None);
        };

        let candidates = [
            (left_pow.as_ref(), right_pow.as_ref(), factor_a.as_ref(), factor_b.as_ref()),
            (right_pow.as_ref(), left_pow.as_ref(), factor_a.as_ref(), factor_b.as_ref()),
            (left_pow.as_ref(), right_pow.as_ref(), factor_b.as_ref(), factor_a.as_ref()),
            (right_pow.as_ref(), left_pow.as_ref(), factor_b.as_ref(), factor_a.as_ref()),
        ];
        for (p1, p2, b1, b2) in candidates {
            let Some((base1, exp1)) = match_pow(p1) else {
                continue;
            };
            let Some((base2, exp2)) = match_pow(p2) else {
                continue;
            };
            if base1.ir() != b1.ir() || base2.ir() != b2.ir() {
                continue;
            }
            if exp1.ir() != shared_exp.as_ref().ir() || exp2.ir() != shared_exp.as_ref().ir() {
                continue;
            }
            let mut proofs = Vec::new();
            for base in [b1, b2] {
                let proof =
                    self.verify_in_standard_set(base, StandardSet::RPos, verify_state.clone())?;
                if proof.is_failed() {
                    proofs.clear();
                    break;
                }
                proofs.push(proof);
            }
            if proofs.len() != 2 {
                continue;
            }
            let exp_proof = self.verify_in_standard_set(
                shared_exp.as_ref(),
                StandardSet::N,
                verify_state.clone(),
            )?;
            if exp_proof.is_failed() {
                continue;
            }
            proofs.push(exp_proof);
            return Ok(Some(PowerOfProductBuiltinRuleProof {
                proof_of_requirement_facts: proofs,
            }));
        }
        Ok(None)
    }

    fn try_reciprocal_as_neg_one_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ReciprocalAsNegOnePowerBuiltinRuleProof>> {
        let (denom, pow_base) = match (left, right) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: num,
                    right: denom,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })),
            ) if is_one_obj(num.as_ref()) && is_neg_one_obj(exponent.as_ref()) => {
                (denom.as_ref(), base.as_ref())
            }
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })),
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: num,
                    right: denom,
                })),
            ) if is_one_obj(num.as_ref()) && is_neg_one_obj(exponent.as_ref()) => {
                (denom.as_ref(), base.as_ref())
            }
            _ => return Ok(None),
        };
        if denom.ir() != pow_base.ir() {
            return Ok(None);
        }
        let nonzero = self.verify_nonzero(denom, verify_state)?;
        if nonzero.is_failed() {
            return Ok(None);
        }
        Ok(Some(ReciprocalAsNegOnePowerBuiltinRuleProof {
            proof_of_requirement_facts: vec![nonzero],
        }))
    }

    fn try_quotient_as_mul_neg_one_power(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<QuotientAsMulNegOnePowerBuiltinRuleProof>> {
        let (numer, denom, mul_left, mul_right) = match (left, right) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: numer,
                    right: denom,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: mul_left,
                    right: mul_right,
                })),
            ) => (numer.as_ref(), denom.as_ref(), mul_left.as_ref(), mul_right.as_ref()),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: mul_left,
                    right: mul_right,
                })),
                Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: numer,
                    right: denom,
                })),
            ) => (numer.as_ref(), denom.as_ref(), mul_left.as_ref(), mul_right.as_ref()),
            _ => return Ok(None),
        };

        let candidates = [(mul_left, mul_right), (mul_right, mul_left)];
        for (factor, inv_candidate) in candidates {
            if factor.ir() != numer.ir() {
                continue;
            }
            let Some((inv_base, inv_exp)) = match_pow(inv_candidate) else {
                continue;
            };
            if inv_base.ir() != denom.ir() || !is_neg_one_obj(inv_exp) {
                continue;
            }
            let nonzero = self.verify_nonzero(denom, verify_state.clone())?;
            if nonzero.is_failed() {
                continue;
            }
            return Ok(Some(QuotientAsMulNegOnePowerBuiltinRuleProof {
                proof_of_requirement_facts: vec![nonzero],
            }));
        }
        Ok(None)
    }

    fn verify_power_law_pos_base_nat_exps(
        &mut self,
        base: &Obj,
        exponents: &[&Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<Vec<VerifyFactResult>>> {
        let mut proofs = Vec::new();
        let base_proof =
            self.verify_in_standard_set(base, StandardSet::RPos, verify_state.clone())?;
        if base_proof.is_failed() {
            return Ok(None);
        }
        proofs.push(base_proof);
        // A positive base also permits exponent zero; induction starts at 0.
        for exp in exponents {
            let exp_proof =
                self.verify_in_standard_set(exp, StandardSet::N, verify_state.clone())?;
            if exp_proof.is_failed() {
                return Ok(None);
            }
            proofs.push(exp_proof);
        }
        Ok(Some(proofs))
    }

    fn verify_in_standard_set(
        &mut self,
        element: &Obj,
        set: StandardSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: Obj::StandardSet(set),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    fn verify_nonzero(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: obj.clone(),
            right: zero_obj(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
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

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn is_neg_one_obj(obj: &Obj) -> bool {
    if matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "-1"
    ) {
        return true;
    }
    // Prefix `-1` parses as Neg(1).
    matches!(
        obj,
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) if is_one_obj(arg.as_ref())
    )
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}
