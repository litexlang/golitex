//! Fixed real sign BT schemas composed by strict expression descent.
use crate::prelude::*;

#[cfg(test)]
#[path = "../../../../tests/unit/execute/positive_sign_composition.rs"]
mod tests;

impl Runtime {
    // Truth only after enclosing object WD. No verify_fact/rule dispatcher,
    // definition search, state reset, or publication occurs in this traversal.
    pub(in crate::execute) fn search_structural_real_sign(
        &mut self,
        element: &Obj,
        state: VerifyState,
    ) -> Option<StructuralRealSignProof> {
        use RealSign as S;
        let leaf = self.search_real_sign_leaf(element, state);
        if leaf
            .as_ref()
            .is_some_and(|p| matches!(p.sign, S::Positive | S::Negative | S::Zero))
        {
            return leaf;
        }
        let derived = self.search_real_sign_expression(element, state);
        match (leaf, derived) {
            (Some(a), Some(b)) => {
                if a.sign.implies(b.sign) {
                    return Some(a);
                }
                if b.sign.implies(a.sign) {
                    return Some(b);
                }
                let (weak, nonzero) = if a.sign == S::Nonzero { (b, a) } else { (a, b) };
                if nonzero.sign.implies(S::Nonzero)
                    && matches!(weak.sign, S::Nonnegative | S::Nonpositive)
                {
                    Some(StructuralRealSignProof::new(
                        element.clone(),
                        if weak.sign == S::Nonnegative {
                            S::Positive
                        } else {
                            S::Negative
                        },
                        StructuralRealSignReason::WeakSignAndNonzero {
                            weak: Box::new(weak),
                            nonzero: Box::new(nonzero),
                        },
                    ))
                } else {
                    Some(weak)
                }
            }
            (Some(p), None) | (None, Some(p)) => Some(p),
            (None, None) => None,
        }
    }

    fn search_real_sign_expression(
        &mut self,
        element: &Obj,
        state: VerifyState,
    ) -> Option<StructuralRealSignProof> {
        use RealSign as S;
        use StructuralRealSignReason as P;
        let (sign, reason) = match element {
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(v)) => {
                let argument = self.search_structural_real_sign(&v.arg, state)?;
                (
                    argument.sign.negated(),
                    P::Neg {
                        argument: Box::new(argument),
                    },
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Add(v)) => {
                let left = self.search_structural_real_sign(&v.left, state)?;
                let right = self.search_structural_real_sign(&v.right, state)?;
                (
                    sign_of_sum(left.sign, right.sign)?,
                    P::Add {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(v)) => {
                let left = self.search_structural_real_sign(&v.left, state)?;
                let right = self.search_structural_real_sign(&v.right, state)?;
                (
                    sign_of_sum(left.sign, right.sign.negated())?,
                    P::Sub {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)) => {
                let left = self.search_structural_real_sign(&v.left, state)?;
                let right = self.search_structural_real_sign(&v.right, state)?;
                (
                    sign_of_product(left.sign, right.sign)?,
                    P::Mul {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) => {
                let left = self.search_structural_real_sign(&v.left, state)?;
                let right = self.search_structural_real_sign(&v.right, state)?;
                // A denominator sign must itself certify nonzero, independently
                // of the enclosing Div WD; no nonnegative-to-positive guess.
                if !right.sign.implies(S::Nonzero) {
                    return None;
                }
                (
                    sign_of_product(left.sign, right.sign)?,
                    P::Div {
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                )
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Min(v)) => {
                return self.search_real_extremum_sign(element, &v.left, &v.right, true, state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Max(v)) => {
                return self.search_real_extremum_sign(element, &v.left, &v.right, false, state)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(v)) => {
                let base = self.search_structural_real_sign(&v.base, state);
                if base
                    .as_ref()
                    .map(|p| p.sign == S::Positive)
                    .unwrap_or(false)
                {
                    let exponent_real = self.search_membership_of_checked_object(
                        &v.exponent,
                        &StandardSet::R,
                        state,
                    )?;
                    (
                        S::Positive,
                        P::PositivePower {
                            base: Box::new(base?),
                            exponent_real: Box::new(exponent_real),
                        },
                    )
                } else {
                    // Any positive even literal power of a real is nonnegative;
                    // a certified nonzero base makes it strictly positive.
                    let Obj::Literal(Literal::Number(n)) = &*v.exponent else {
                        return None;
                    };
                    let n = n.normalized_value.parse::<i64>().ok()?;
                    if n <= 0 || n % 2 != 0 {
                        return None;
                    }
                    if let Some(base) = base.filter(|p| p.sign.implies(S::Nonzero)) {
                        (
                            S::Positive,
                            P::PositiveEvenPower {
                                base: Box::new(base),
                                exponent: v.exponent.as_ref().clone(),
                            },
                        )
                    } else {
                        let base_real = self.search_membership_of_checked_object(
                            &v.base,
                            &StandardSet::R,
                            state,
                        )?;
                        (
                            S::Nonnegative,
                            P::NonnegativeEvenPower {
                                base_real: Box::new(base_real),
                                exponent: v.exponent.as_ref().clone(),
                            },
                        )
                    }
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(v)) => {
                if let Some(argument) = self
                    .search_structural_real_sign(&v.arg, state)
                    .filter(|p| p.sign.implies(S::Nonzero))
                {
                    (
                        S::Positive,
                        P::PositiveAbs {
                            argument: Box::new(argument),
                        },
                    )
                } else {
                    let real =
                        self.search_membership_of_checked_object(&v.arg, &StandardSet::R, state)?;
                    (
                        S::Nonnegative,
                        P::NonnegativeAbs {
                            argument_real: Box::new(real),
                        },
                    )
                }
            }
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(v)) => {
                if let Some(argument) = self
                    .search_structural_real_sign(&v.arg, state)
                    .filter(|p| p.sign == S::Positive)
                {
                    (
                        S::Positive,
                        P::PositiveSqrt {
                            argument: Box::new(argument),
                        },
                    )
                } else {
                    // Defined principal sqrt is nonnegative. Its input-domain
                    // certificate remains in the enclosing object's WD.
                    let real =
                        self.search_membership_of_checked_object(&v.arg, &StandardSet::R, state)?;
                    (
                        S::Nonnegative,
                        P::NonnegativeSqrt {
                            argument_real: Box::new(real),
                        },
                    )
                }
            }
            _ => return None,
        };
        Some(StructuralRealSignProof::new(element.clone(), sign, reason))
    }

    fn search_real_sign_leaf(
        &mut self,
        element: &Obj,
        state: VerifyState,
    ) -> Option<StructuralRealSignProof> {
        use RealSign as S;
        use StructuralRealSignReason as P;
        let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
        if element.ir() == zero.ir() {
            return Some(StructuralRealSignProof::new(
                element.clone(),
                S::Zero,
                P::ZeroLiteral,
            ));
        }
        // Read both orientations directly, keeping the actual scoped citation.
        // Example: x>0 and 0<x supply the same positive leaf at any depth.
        let positive = self
            .known_less_proof(&zero, element)
            .or_else(|| self.known_greater_proof(element, &zero));
        let negative = if positive.is_none() {
            self.known_less_proof(element, &zero)
                .or_else(|| self.known_greater_proof(&zero, element))
        } else {
            None
        };
        if let Some((sign, source)) = positive
            .map(|p| (S::Positive, p))
            .or_else(|| negative.map(|p| (S::Negative, p)))
        {
            let real = self.search_membership_of_checked_object(element, &StandardSet::R, state)?;
            return Some(StructuralRealSignProof::new(
                element.clone(),
                sign,
                P::Known {
                    real: Box::new(real),
                    source: Box::new(source),
                },
            ));
        }
        for (sign, fact) in [
            (
                S::Positive,
                AtomicFact::LessFact(LessFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: zero.clone(),
                    right: element.clone(),
                    line_file: None,
                }),
            ),
            (
                S::Negative,
                AtomicFact::LessFact(LessFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: element.clone(),
                    right: zero.clone(),
                    line_file: None,
                }),
            ),
        ] {
            if let Some(closed) = calculate_closed_atomic_except_equality_fact(&fact) {
                return Some(StructuralRealSignProof::new(
                    element.clone(),
                    sign,
                    P::Closed(Box::new(closed)),
                ));
            }
        }
        // Structural membership is the existing non-searching carrier mechanism;
        // it does not call this sign traversal or another builtin dispatcher.
        for (set, sign) in [
            (StandardSet::RPos, S::Positive),
            (StandardSet::RNeg, S::Negative),
        ] {
            if let Some(member) = self.search_membership_of_checked_object(element, &set, state) {
                return Some(StructuralRealSignProof::new(
                    element.clone(),
                    sign,
                    P::Membership(Box::new(member)),
                ));
            }
        }
        let nonzero = self
            .known_not_equal_proof(element, &zero)
            .or_else(|| self.known_not_equal_proof(&zero, element));
        let weak = self
            .known_less_equal_proof(&zero, element)
            .or_else(|| self.known_greater_equal_proof(element, &zero));
        let (weak, sign) = if let Some(p) = weak {
            (Some(p), S::Nonnegative)
        } else {
            (
                self.known_less_equal_proof(element, &zero)
                    .or_else(|| self.known_greater_equal_proof(&zero, element)),
                S::Nonpositive,
            )
        };
        if let Some(weak) = weak {
            let real = self.search_membership_of_checked_object(element, &StandardSet::R, state)?;
            return Some(if let Some(nonzero) = nonzero {
                StructuralRealSignProof::new(
                    element.clone(),
                    if sign == S::Nonnegative {
                        S::Positive
                    } else {
                        S::Negative
                    },
                    P::WeakAndNonzero {
                        real: Box::new(real),
                        weak: Box::new(weak),
                        nonzero: Box::new(nonzero),
                    },
                )
            } else {
                StructuralRealSignProof::new(
                    element.clone(),
                    sign,
                    P::Known {
                        real: Box::new(real),
                        source: Box::new(weak),
                    },
                )
            });
        }
        if let Some(source) = nonzero {
            let real = self.search_membership_of_checked_object(element, &StandardSet::R, state)?;
            return Some(StructuralRealSignProof::new(
                element.clone(),
                S::Nonzero,
                P::Known {
                    real: Box::new(real),
                    source: Box::new(source),
                },
            ));
        }
        None
    }

    fn search_real_extremum_sign(
        &mut self,
        element: &Obj,
        a: &Obj,
        b: &Obj,
        minimum: bool,
        state: VerifyState,
    ) -> Option<StructuralRealSignProof> {
        use RealSign as S;
        use StructuralRealSignReason as P;
        let left = self.search_structural_real_sign(a, state);
        let right = self.search_structural_real_sign(b, state);
        // max needs one positive (or nonnegative) operand; min needs one
        // negative (or nonpositive) operand. The other must still be real.
        // Prefer a strict witness on either side over a weak witness on the
        // first side: max(nonnegative, positive) is strictly positive.
        for (index, required) in [
            (0, if minimum { S::Negative } else { S::Positive }),
            (1, if minimum { S::Negative } else { S::Positive }),
            (
                0,
                if minimum {
                    S::Nonpositive
                } else {
                    S::Nonnegative
                },
            ),
            (
                1,
                if minimum {
                    S::Nonpositive
                } else {
                    S::Nonnegative
                },
            ),
        ] {
            let selected = if index == 0 {
                left.as_ref()
            } else {
                right.as_ref()
            };
            if let Some(selected) = selected {
                let usable = selected.sign.implies(required);
                if usable {
                    let other = self.search_membership_of_checked_object(
                        if index == 0 { b } else { a },
                        &StandardSet::R,
                        state,
                    )?;
                    let sign = if minimum {
                        if selected.sign == S::Negative {
                            S::Negative
                        } else {
                            S::Nonpositive
                        }
                    } else {
                        if selected.sign == S::Positive {
                            S::Positive
                        } else {
                            S::Nonnegative
                        }
                    };
                    // Move only after all borrowed branch decisions are complete.
                    let selected = Box::new(if index == 0 { left? } else { right? });
                    let reason = match (minimum, index) {
                        (true, 0) => P::MinLeft {
                            selected,
                            other_real: Box::new(other),
                        },
                        (true, _) => P::MinRight {
                            selected,
                            other_real: Box::new(other),
                        },
                        (false, 0) => P::MaxLeft {
                            selected,
                            other_real: Box::new(other),
                        },
                        (false, _) => P::MaxRight {
                            selected,
                            other_real: Box::new(other),
                        },
                    };
                    return Some(StructuralRealSignProof::new(element.clone(), sign, reason));
                }
            }
        }
        let (left, right) = (left?, right?);
        let desired = if minimum {
            S::Nonnegative
        } else {
            S::Nonpositive
        };
        if !left.sign.implies(desired) || !right.sign.implies(desired) {
            return None;
        }
        let strict = if minimum { S::Positive } else { S::Negative };
        let sign = if left.sign == strict && right.sign == strict {
            strict
        } else {
            desired
        };
        let reason = if minimum {
            P::MinBoth {
                left: Box::new(left),
                right: Box::new(right),
            }
        } else {
            P::MaxBoth {
                left: Box::new(left),
                right: Box::new(right),
            }
        };
        Some(StructuralRealSignProof::new(element.clone(), sign, reason))
    }
}

fn sign_of_sum(a: RealSign, b: RealSign) -> Option<RealSign> {
    use RealSign as S;
    if a == S::Zero {
        return Some(b);
    }
    if b == S::Zero {
        return Some(a);
    }
    if a.implies(S::Nonnegative) && b.implies(S::Nonnegative) {
        return Some(if a == S::Positive || b == S::Positive {
            S::Positive
        } else {
            S::Nonnegative
        });
    }
    if a.implies(S::Nonpositive) && b.implies(S::Nonpositive) {
        return Some(if a == S::Negative || b == S::Negative {
            S::Negative
        } else {
            S::Nonpositive
        });
    }
    None
}
fn sign_of_product(a: RealSign, b: RealSign) -> Option<RealSign> {
    use RealSign as S;
    if a == S::Zero || b == S::Zero {
        return Some(S::Zero);
    }
    if (a == S::Positive && b == S::Positive) || (a == S::Negative && b == S::Negative) {
        return Some(S::Positive);
    }
    if (a == S::Positive && b == S::Negative) || (a == S::Negative && b == S::Positive) {
        return Some(S::Negative);
    }
    if (a.implies(S::Nonnegative) && b.implies(S::Nonnegative))
        || (a.implies(S::Nonpositive) && b.implies(S::Nonpositive))
    {
        return Some(S::Nonnegative);
    }
    if (a.implies(S::Nonnegative) && b.implies(S::Nonpositive))
        || (a.implies(S::Nonpositive) && b.implies(S::Nonnegative))
    {
        return Some(S::Nonpositive);
    }
    if a.implies(S::Nonzero) && b.implies(S::Nonzero) {
        return Some(S::Nonzero);
    }
    None
}
