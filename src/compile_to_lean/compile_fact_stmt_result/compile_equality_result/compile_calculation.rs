use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_builtin_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &EqualitySearchProofByCalculation,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let values = match proof {
            EqualitySearchProofByCalculation::ClosedDecimal {
                left_normal,
                right_normal,
            } => ClosedValuePair::Decimal {
                left: left_normal.clone(),
                right: right_normal.clone(),
            },
            EqualitySearchProofByCalculation::ClosedRational {
                left_normal,
                right_normal,
            } => {
                let left = self
                    .compile_numeric_observation(&fact.left, position)?
                    .3
                    .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
                let right = self
                    .compile_numeric_observation(&fact.right, position)?
                    .3
                    .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
                if left.to_obj().readable_string() != *left_normal
                    || right.to_obj().readable_string() != *right_normal
                {
                    return Err(LeanCompileError::unsupported("ClosedEquality/NormalForms"));
                }
                ClosedValuePair::Rational { left, right }
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "ClosedEquality/BuiltinFamily",
                ))
            }
        };
        self.compile_closed_equality(fact, &ClosedEqualityCalculationProof { values }, position)
    }

    pub(in crate::compile_to_lean) fn compile_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &ClosedEqualityCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if matches!(proof.values, ClosedValuePair::Complex { .. }) {
            return self.compile_closed_complex_relation(
                &fact.left,
                &fact.right,
                &proof.values,
                true,
                position,
            );
        }
        let left = self
            .compile_numeric_observation(&fact.left, position)?
            .3
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let right = self
            .compile_numeric_observation(&fact.right, position)?
            .3
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let matching = match &proof.values {
            ClosedValuePair::Decimal { left: a, right: b } => {
                scalar_decimal(a)? == left && scalar_decimal(b)? == right
            }
            ClosedValuePair::Rational { left: a, right: b } => a == &left && b == &right,
            ClosedValuePair::Complex {
                left_real: a,
                left_imaginary: ai,
                right_real: b,
                right_imaginary: bi,
            } => a == &left && b == &right && ai.is_zero() && bi.is_zero(),
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("ClosedEquality/Radical"))
            }
        };
        if !matching || left != right {
            return Err(LeanCompileError::new("ClosedEquality/Values", "Closed equality values differ from their exact source endpoints or from each other."));
        }
        let x = self.compile_numeric_observation(&fact.left, position)?;
        let y = self.compile_numeric_observation(&fact.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }

    pub(in crate::compile_to_lean) fn compile_scalar_division_relation(
        &self,
        fact: &EqualFact,
        proof: &ScalarDivisionRelationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (child, product_from_division) = match proof {
            ScalarDivisionRelationProof::ProductFromDivision(p) => (&p.division_equation, true),
            ScalarDivisionRelationProof::DivisionFromProduct(p) => (&p.product_equation, false),
        };
        let compiled = self.compile_verify(child, position)?;
        let source_equation = source_subject(child)?;
        let equation = match &source_equation {
            Fact::AtomicFact(AtomicFact::EqualFact(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ScalarDivisionRelation/Child",
                    "The source equation is not an equality.",
                ))
            }
        };
        let (_numerator, _denominator, _factor, quotient, reversed, commuted) =
            if product_from_division {
                let quotient = match &equation.left {
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "ScalarDivisionRelation/DivisionSubject",
                            "ProductFromDivision must cite a quotient equation.",
                        ))
                    }
                };
                let mut matched = None;
                for (other, product, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = product {
                        if other.ir() != quotient.left.ir() {
                            continue;
                        }
                        if p.left.ir() == equation.right.ir() && p.right.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, false));
                            break;
                        }
                        if p.right.ir() == equation.right.ir() && p.left.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, true));
                            break;
                        }
                    }
                }
                let (reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source quotient equation does not describe the parent product endpoints."))?;
                (
                    quotient.left.as_ref(),
                    quotient.right.as_ref(),
                    &equation.right,
                    &equation.left,
                    reversed,
                    commuted,
                )
            } else {
                let mut matched = None;
                for (quotient_obj, factor, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(q)) = quotient_obj {
                        if equation.left.ir() != q.left.ir() {
                            continue;
                        }
                        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = &equation.right
                        {
                            if p.left.ir() == factor.ir() && p.right.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, false));
                                break;
                            }
                            if p.right.ir() == factor.ir() && p.left.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, true));
                                break;
                            }
                        }
                    }
                }
                let (q, factor, quotient_obj, reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source product equation does not describe the parent quotient endpoints."))?;
                (
                    q.left.as_ref(),
                    q.right.as_ref(),
                    factor,
                    quotient_obj,
                    reversed,
                    commuted,
                )
            };
        // The checked child has now formed its exact endpoints. Its WD is
        // available to the conversion, without publishing its equality truth.
        let checked_child =
            SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let position = &checked_child;
        let product = if product_from_division {
            if reversed {
                &fact.left
            } else {
                &fact.right
            }
        } else {
            &equation.right
        };
        let quotient = self.compile_object_reference(quotient, position)?;
        let product = self.compile_object_reference(product, position)?;
        let factor_field = if commuted { "right" } else { "left" };
        let member_field = if commuted { "2" } else { "1" };
        let commute = if commuted {
            "(Litex.sameMulComm _product.val.left _product.val.right _product.wd.1 _product.wd.2)"
        } else {
            ""
        };
        let converted = if product_from_division {
            if commuted {
                format!("((_conversion.mp _child).trans {commute}.symm)")
            } else {
                "(_conversion.mp _child)".to_string()
            }
        } else if commuted {
            format!("(_conversion.mpr (_child.trans {commute}))")
        } else {
            "(_conversion.mpr _child)".to_string()
        };
        let converted = if reversed {
            format!("({converted}.symm)")
        } else {
            converted
        };
        Ok(format!("(by\n  let _quotient := {}\n  let _product := {}\n  have _child : {} := {}\n  have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.{factor_field} _quotient.wd.1 _quotient.wd.2.1 _product.wd.{member_field} _quotient.wd.2.2\n  exact {converted})",
            quotient.replace('\n', "\n  "), product.replace('\n', "\n  "), compiled.0.replace('\n', "\n  "), compiled.1.replace('\n', "\n  ")))
    }

    pub(in crate::compile_to_lean) fn compile_rational(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        guarded: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_arithmetic_expression(&fact.left)?;
        validate_arithmetic_expression(&fact.right)?;
        let expected = normalization_nonzero_subjects(&fact.left, &fact.right)?;
        if requirements.len() != expected.len()
            || proofs.len() != expected.len()
            || guarded != !expected.is_empty()
        {
            return Err(LeanCompileError::new("Rational/Requirements", "The selected normalization family or ordered guard arity differs from the source expression."));
        }
        let mut native_guards = Vec::new();
        for (index, ((requirement, proof), object)) in
            requirements.iter().zip(proofs).zip(expected).enumerate()
        {
            ensure_nonzero_subject(requirement, &object)?;
            let proved = self.compile_verify(proof, position)?;
            if &source_subject(proof)? != requirement {
                return Err(LeanCompileError::new(
                    "Rational/RequirementSubject",
                    "A guard's verify result differs from its exact ordered requirement.",
                ));
            }
            let term = self.compile_object_reference(&object, position)?;
            let native = self.compile_numeric_observation(&object, position)?;
            // A tactic-valued observation needs its expected scalar type before
            // elaborating the zero in this standalone nonzero proposition.
            native_guards.push(format!("have _litex_nz_{index} : ({} : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote {term} {} {} {}", native.0, native.0, native.1, proved.1));
        }
        let x = self.compile_numeric_observation(&fact.left, position)?;
        let y = self.compile_numeric_observation(&fact.right, position)?;
        // The empty Rational tag contains no monomial trace. The Lean kernel
        // checks the fixed normalization proof, including forged false tags.
        let normalization = if guarded {
            let guard_names = (0..native_guards.len())
                .map(|i| format!("_litex_nz_{i}"))
                .collect::<Vec<_>>();
            let exact_guards = guard_names
                .iter()
                .map(|n| format!("exact {n}"))
                .collect::<Vec<_>>()
                .join(" | ");
            format!("(by\n  {}\n  litex_normalize_rational (disch := repeat' first | {exact_guards} | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)\n)", native_guards.join("\n  "))
        } else {
            // The same source atom can occur through different projections of
            // certified objects. Compare those definitions at default transparency.
            "(by ring!)".to_string()
        };
        Ok(format!(
            // Endpoint WD was checked by the equality dispatcher. The exact
            // denotation certificates determine these same two objects.
            "(Litex.NativeBridge.sameOfDenoteNumber _ _ {} {} {} {} {normalization})",
            x.0, y.0, x.1, y.1
        ))
    }
}
