//! Guarded scalar comparisons and exact quotient membership.
use crate::prelude::*;

pub struct SubtractionOrderPairsProof {
    pub minuend_order: VerifyFactResult,
    pub subtrahend_order: VerifyFactResult,
}
impl SubtractionOrderPairsProof {
    pub fn new(minuend_order: VerifyFactResult, subtrahend_order: VerifyFactResult) -> Self {
        Self {
            minuend_order,
            subtrahend_order,
        }
    }
}

pub struct AbsSquareRadiusProof {
    pub radius_nonnegative: VerifyFactResult,
    pub squared_order: VerifyFactResult,
}
impl AbsSquareRadiusProof {
    pub fn new(radius_nonnegative: VerifyFactResult, squared_order: VerifyFactResult) -> Self {
        Self {
            radius_nonnegative,
            squared_order,
        }
    }
}

pub struct QuotientScalarBoundProof {
    pub denominator_positive: VerifyFactResult,
    pub product_bound: VerifyFactResult,
}
impl QuotientScalarBoundProof {
    pub fn new(denominator_positive: VerifyFactResult, product_bound: VerifyFactResult) -> Self {
        Self {
            denominator_positive,
            product_bound,
        }
    }
}

pub struct ExactIntegerQuotientProof {
    pub numerator_integer: VerifyFactResult,
    pub denominator_integer: VerifyFactResult,
    pub denominator_nonzero: VerifyFactResult,
    pub divisibility: VerifyFactResult,
}
impl ExactIntegerQuotientProof {
    pub fn new(
        numerator_integer: VerifyFactResult,
        denominator_integer: VerifyFactResult,
        denominator_nonzero: VerifyFactResult,
        divisibility: VerifyFactResult,
    ) -> Self {
        Self {
            numerator_integer,
            denominator_integer,
            denominator_nonzero,
            divisibility,
        }
    }
}

impl From<SubtractionOrderPairsProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: SubtractionOrderPairsProof) -> Self {
        Self::SubtractionOrderPairs(proof)
    }
}

impl From<AbsSquareRadiusProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: AbsSquareRadiusProof) -> Self {
        Self::AbsSquareRadius(proof)
    }
}

impl From<QuotientScalarBoundProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: QuotientScalarBoundProof) -> Self {
        Self::QuotientScalarUpperBound(proof)
    }
}

impl From<QuotientScalarBoundProof> for LessFactSearchProofByBuiltinRule {
    fn from(proof: QuotientScalarBoundProof) -> Self {
        Self::QuotientScalarStrictUpperBound(proof)
    }
}

impl From<ExactIntegerQuotientProof> for super::in_fact::InFactSearchProofByBuiltinRule {
    fn from(proof: ExactIntegerQuotientProof) -> Self {
        Self::ExactIntegerQuotient(proof)
    }
}

impl Runtime {
    pub(super) fn search_subtraction_order_pairs(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        // a<=b, c<=d => a-d<=b-c; enclosing comparison WD owns real domains.
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(right)),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        let Some(minuend) = self.weak_or_strict_order_premise(
            &left.left,
            &right.left,
            fact.line_file.clone(),
            state,
        )?
        else {
            return Ok(None);
        };
        let Some(subtrahend) = self.weak_or_strict_order_premise(
            &right.right,
            &left.right,
            fact.line_file.clone(),
            state,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(
            SubtractionOrderPairsProof::new(minuend, subtrahend).into(),
        ))
    }

    pub(super) fn search_abs_square_radius(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        // r>=0, x^2<=r^2 => abs(x)<=r, with no sign restriction on x.
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(value)) = &fact.left else {
            return Ok(None);
        };
        let left_square = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: value.arg.clone(),
            exponent: Box::new(Obj::Literal(Literal::Number(Number::new("2".into())))),
        }));
        let right_square = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(fact.right.clone()),
            exponent: Box::new(Obj::Literal(Literal::Number(Number::new("2".into())))),
        }));
        let Some(squared_order) = self.weak_or_strict_order_premise(
            &left_square,
            &right_square,
            fact.line_file.clone(),
            state,
        )?
        else {
            return Ok(None);
        };
        let radius_nonnegative = self.verify_order_nonnegative(&fact.right, state)?;
        if radius_nonnegative.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            AbsSquareRadiusProof::new(radius_nonnegative, squared_order).into(),
        ))
    }

    pub(super) fn search_quotient_scalar_bound(
        &mut self,
        left: &Obj,
        right: &Obj,
        strict: bool,
        state: VerifyState,
    ) -> RuntimeResult<Option<QuotientScalarBoundProof>> {
        // b>0, a<=M*b => a/b<=M (and the strict counterpart).
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = left else {
            return Ok(None);
        };
        let denominator_positive = self.verify_order_positive(&div.right, state)?;
        if denominator_positive.is_failed() {
            return Ok(None);
        }
        // Both placements denote the same product, but retain actual premise evidence.
        for (first, second) in [(right, div.right.as_ref()), (div.right.as_ref(), right)] {
            let product = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: Box::new(first.clone()),
                right: Box::new(second.clone()),
            }));
            let bound = if strict {
                self.strict_order_premise(&div.left, &product, None, state)?
            } else {
                self.weak_or_strict_order_premise(&div.left, &product, None, state)?
            };
            if let Some(product_bound) = bound {
                return Ok(Some(QuotientScalarBoundProof::new(
                    denominator_positive,
                    product_bound,
                )));
            }
        }
        Ok(None)
    }

    pub(super) fn search_exact_integer_quotient(
        &mut self,
        fact: &InFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<super::in_fact::InFactSearchProofByBuiltinRule>> {
        // a,b in Z, b!=0, $dvd(a,b) => a/b in Z, for either divisor sign.
        if !matches!(&fact.set, Obj::StandardSet(StandardSet::Z)) {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = &fact.element else {
            return Ok(None);
        };
        let numerator: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: *div.left.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: fact.line_file.clone(),
        }
        .into();
        let numerator_integer = self.verify_builtin_rule_premise(&numerator, state)?;
        if numerator_integer.is_failed() {
            return Ok(None);
        }
        let denominator: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: *div.right.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: fact.line_file.clone(),
        }
        .into();
        let denominator_integer = self.verify_builtin_rule_premise(&denominator, state)?;
        if denominator_integer.is_failed() {
            return Ok(None);
        }
        let denominator_nonzero = self.verify_order_nonzero(&div.right, state)?;
        if denominator_nonzero.is_failed() {
            return Ok(None);
        }
        let premise: Fact = DvdFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *div.left.clone(),
            right: *div.right.clone(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let divisibility = self.verify_builtin_rule_premise(&premise, state)?;
        if divisibility.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ExactIntegerQuotientProof::new(
                numerator_integer,
                denominator_integer,
                denominator_nonzero,
                divisibility,
            )
            .into(),
        ))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/selected_scalar_bt_rules/tests.rs"]
mod selected_scalar_bt_rules_tests;
