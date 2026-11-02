use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sqrt_quotient_square(
        &self,
        fact: &EqualFact,
        equation: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::EqualFact(source)) = source_subject(equation)? else {
            return Err(invalid("QuotientSquareEquationFamily"));
        };
        let (
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(ratio)),
        ) = (&source.left, &source.right)
        else {
            return Err(invalid("QuotientSquareEquationShape"));
        };
        for (square, product, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(numerator)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
            ) = (square, product)
            else {
                continue;
            };
            if numerator.base.ir() != ratio.left.ir() {
                continue;
            }
            for (radicand, denominator, reverse_product) in [
                (&product.left, &product.right, false),
                (&product.right, &product.left, true),
            ] {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(denominator)) =
                    denominator.as_ref()
                else {
                    continue;
                };
                if radicand.ir() != root.arg.ir() || denominator.base.ir() != ratio.right.ir()
                    || ![&numerator.exponent, &denominator.exponent].iter().all(|n| matches!(n.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value=="2")) { continue; }
                let requirements = std::slice::from_ref(equation);
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    0,
                );
                let equality = self.compile_verify(equation, &prior)?.1;
                let complete = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    1,
                );
                let root = self.compile_object_reference(&source.left, &complete)?;
                let ratio = self.compile_object_reference(&source.right, &complete)?;
                let lhs_exp =
                    self.compile_literal_natural_identity(&numerator.exponent, 2, position)?;
                let rhs_exp =
                    self.compile_literal_natural_identity(&denominator.exponent, 2, position)?;
                let numerator = self.compile_object_reference(square, position)?;
                let denominator = self.compile_object_reference(
                    if reverse_product {
                        &product.left
                    } else {
                        &product.right
                    },
                    position,
                )?;
                let denominator_value = "(M.powValue (Litex.denote _denominator.val.base) (Litex.denote _denominator.val.exponent))";
                let product = if reverse_product {
                    format!("M.mulValue {denominator_value} (Litex.denote _root.val.arg)")
                } else {
                    format!("M.mulValue (Litex.denote _root.val.arg) {denominator_value}")
                };
                return Ok(format!(
                    "(by\n  let _root := {}\n  let _ratio := {}\n  let _numerator := {}\n  let _denominator := {}\n  have _lhs_exp : Litex.denote _numerator.val.exponent = M.number ((2 : ℕ) : ℂ) := {}\n  have _rhs_exp : Litex.denote _denominator.val.exponent = M.number ((2 : ℕ) : ℂ) := {}\n  have _identity : M.powValue (Litex.denote _numerator.val.base) (Litex.denote _numerator.val.exponent) = {product} := by\n    rw [_lhs_exp, _rhs_exp]\n    exact Litex.sqrtQuotientSquareValue _root _ratio {} {reverse_product}\n  exact _identity{}\n)",
                    root.replace('\n', "\n  "), ratio.replace('\n', "\n  "),
                    numerator.replace('\n', "\n  "), denominator.replace('\n', "\n  "),
                    lhs_exp.replace('\n', "\n  "), rhs_exp.replace('\n', "\n  "),
                    equality.replace('\n', "\n    "), if reverse { ".symm" } else { "" }
                ));
            }
        }
        Err(invalid("QuotientSquareEndpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_sqrt_nonpositive_square(
        &self,
        fact: &EqualFact,
        nonpositive: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (root, negative, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root_arg)) = root else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(square)) = root_arg.arg.as_ref()
            else {
                continue;
            };
            let Some(argument) = negative_arg(negative) else {
                continue;
            };
            if argument.ir() != square.base.ir()
                || !matches!(square.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value=="2")
            {
                continue;
            }
            let Fact::AtomicFact(bound) = source_subject(nonpositive)? else {
                return Err(invalid("NonpositiveFamily"));
            };
            let (left, right, strict) = source_order_oriented(&bound)?;
            if left.ir() != argument.ir() || !is_exact_zero(right) {
                return Err(invalid("NonpositiveSubject"));
            }
            let requirements = std::slice::from_ref(nonpositive);
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(nonpositive, &prior)?.1;
            let proof = if strict {
                format!("(Litex.ltToLe _root.val.arg.val.base (Litex.number (M := M) 0) {proof})")
            } else {
                proof
            };
            let complete = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                1,
            );
            let real = self.compile_real_membership_certificate(argument, &complete)?;
            let normalized = self.compile_negated_value(
                negative,
                "_root.val.arg.val.base",
                &format!("(Litex.realToComplex _root.val.arg.val.base {real})"),
                &complete,
            )?;
            let exponent = self.compile_literal_natural_identity(&square.exponent, 2, position)?;
            let root = self.compile_object_reference(root, position)?;
            return Ok(format!("(by\n  let _root := {root}\n  have _bound : Litex.Le _root.val.arg.val.base (Litex.number (M := M) 0) := {proof}\n  have _exp : Litex.denote _root.val.arg.val.exponent = M.number ((2 : ℕ) : ℂ) := {exponent}\n  have _id : Litex.denote _root = M.negValue (Litex.denote _root.val.arg.val.base) := by\n    change Litex.sqrtValue (M.powValue (Litex.denote _root.val.arg.val.base) (Litex.denote _root.val.arg.val.exponent)) = _\n    rw [_exp]\n    exact Litex.sqrtOfNonpositiveSquareValue _root.val.arg.val.base _bound\n  exact (_id.trans ({normalized}).symm){}\n)", if reverse { ".symm" } else { "" }));
        }
        Err(invalid("NonpositiveSquareEndpoints"))
    }

    pub(in crate::compile_to_lean) fn compile_remainder_elementary(
        &self,
        fact: &EqualFact,
        power: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != if power { 3 } else { 2 } {
            return Err(invalid("RemainderRequirements"));
        }
        for (left, right, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::IntegerOperator(IntegerOperator::Mod(left)),
                Obj::IntegerOperator(IntegerOperator::Mod(right)),
            ) = (left, right)
            else {
                continue;
            };
            if left.right.ir() != right.right.ir() {
                continue;
            }
            let (a, n) = if power {
                let (
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
                ) = (left.left.as_ref(), right.left.as_ref())
                else {
                    continue;
                };
                let Obj::IntegerOperator(IntegerOperator::Mod(inner)) = b.base.as_ref() else {
                    continue;
                };
                if a.base.ir() != inner.left.ir()
                    || a.exponent.ir() != b.exponent.ir()
                    || inner.right.ir() != left.right.ir()
                {
                    continue;
                }
                (a.base.as_ref(), Some(a.exponent.as_ref()))
            } else {
                let Some(a) = negative_arg(&left.left) else {
                    continue;
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = right.left.as_ref()
                else {
                    continue;
                };
                let Obj::IntegerOperator(IntegerOperator::Mod(inner)) = sub.right.as_ref() else {
                    continue;
                };
                if sub.left.ir() != left.right.ir()
                    || inner.left.ir() != a.ir()
                    || inner.right.ir() != left.right.ir()
                {
                    continue;
                }
                (a, None)
            };
            let m = left.right.as_ref();
            let mut subjects = vec![(a, StandardSet::Z), (m, StandardSet::NPos)];
            if let Some(n) = n {
                subjects.push((n, StandardSet::N));
            }
            let mut proofs = Vec::new();
            for (index, (child, (subject, carrier))) in
                requirements.iter().zip(subjects).enumerate()
            {
                let scope = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    index,
                );
                proofs.push(self.compile_power_member(child, subject, carrier, &scope)?);
            }
            let complete = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                requirements.len(),
            );
            let a_term = self.compile_object_reference(a, &complete)?;
            let m_term = self.compile_object_reference(m, &complete)?;
            let proof = if let Some(n) = n {
                format!(
                    "(Litex.remainderNaturalPowerValue {a_term} {m_term} {} {} {} {})",
                    self.compile_object_reference(n, &complete)?,
                    proofs[0],
                    proofs[1],
                    proofs[2]
                )
            } else {
                let normalized = self.compile_negated_value(
                    &left.left,
                    &a_term,
                    &format!("(Litex.integerToComplex {a_term} {})", proofs[0]),
                    &complete,
                )?;
                format!("((congrArg (fun _a => Litex.integerDivisionValue (M := M) false _a (Litex.denote {m_term})) {normalized}).trans (Litex.remainderNegationValue {a_term} {m_term} {} {}))", proofs[0], proofs[1])
            };
            return Ok(if reverse {
                format!("({proof}).symm")
            } else {
                proof
            });
        }
        Err(invalid("RemainderEndpoints"))
    }
}
fn negative_arg(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => Some(&p.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if is_exact_zero(&p.left) => {
            Some(&p.right)
        }
        _ => None,
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ElementaryArithmetic/{part}"))
}
