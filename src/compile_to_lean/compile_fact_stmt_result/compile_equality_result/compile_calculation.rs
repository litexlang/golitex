use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &ClosedEqualityCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
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
        let (_numerator, denominator, factor, quotient, reversed, commuted) =
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
        let b = self.compile_numeric_observation(denominator, position)?;
        let c = self.compile_numeric_observation(factor, position)?;
        let x = self.compile_numeric_observation(&equation.left, position)?;
        let y = self.compile_numeric_observation(&equation.right, position)?;
        let source_eq = format!(
            "(Litex.NativeBridge.nativeEqOfDenoteNumber {} {} {} {} {} {} {})",
            self.compile_object_reference(&equation.left, position)?,
            self.compile_object_reference(&equation.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1,
            compiled.1
        );
        let guard = format!(
            "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} ({}).wd.2.2)",
            self.compile_object_reference(denominator, position)?,
            b.0,
            b.1,
            self.compile_object_reference(quotient, position)?
        );
        let native_proof = if product_from_division {
            let product = format!("((div_eq_iff {guard}).mp {source_eq})");
            let oriented = if commuted {
                format!("({product}.trans (mul_comm {} {}))", c.0, b.0)
            } else {
                product
            };
            if reversed {
                format!("({oriented}.symm)")
            } else {
                oriented
            }
        } else {
            let product = if commuted {
                format!("({source_eq}.trans (mul_comm {} {}))", b.0, c.0)
            } else {
                source_eq
            };
            let quotient = format!("((div_eq_iff {guard}).mpr {product})");
            if reversed {
                format!("({quotient}.symm)")
            } else {
                quotient
            }
        };
        let left = self.compile_numeric_observation(&fact.left, position)?;
        let right = self.compile_numeric_observation(&fact.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} {native_proof})",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            left.0,
            right.0,
            left.1,
            right.1
        ))
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
            native_guards.push(format!("have _litex_nz_{index} : {} ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote {term} {} {} {}", native.0, native.0, native.1, proved.1));
        }
        let left = self.compile_object_reference(&fact.left, position)?;
        let right = self.compile_object_reference(&fact.right, position)?;
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
            "(by ring)".to_string()
        };
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {left} {right} {} {} {} {} {normalization})",
            x.0, y.0, x.1, y.1
        ))
    }
}
