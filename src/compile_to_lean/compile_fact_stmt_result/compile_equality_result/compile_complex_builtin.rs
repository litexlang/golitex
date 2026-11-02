use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_complex::complex_argument;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_projection(
        &self,
        fact: &EqualFact,
        imaginary: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "Complex/RealProjectionRequirements",
            ));
        }
        for (projection, target, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((kind, _, arg)) = complex_argument(projection) else {
                continue;
            };
            if kind
                != if imaginary {
                    "ImaginaryPart"
                } else {
                    "RealPart"
                }
                || if imaginary {
                    !is_exact_zero(target)
                } else {
                    arg.ir() != target.ir()
                }
            {
                continue;
            }
            if !matches!(source_subject(&requirements[0])?, Fact::AtomicFact(AtomicFact::InFact(ref f))
                if f.element.ir() == arg.ir() && f.set == Obj::StandardSet(StandardSet::R))
            {
                return Err(LeanCompileError::unsupported(
                    "Complex/RealProjectionSubject",
                ));
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &child)?.1;
            let arg = self.compile_object_reference(arg, position)?;
            let law = if imaginary {
                "imaginaryPartOfRealValue"
            } else {
                "realPartOfRealValue"
            };
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(Litex.{law} (Litex.denote {arg}) {proof}){symmetric}"
            ));
        }
        Err(LeanCompileError::unsupported(
            "Complex/RealProjectionEndpoints",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_rectangular_projection(
        &self,
        fact: &EqualFact,
        imaginary: bool,
        real_proof: &VerifyFactResult,
        imaginary_proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (projection, target, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((kind, _, Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)))) =
                complex_argument(projection)
            else {
                continue;
            };
            if kind
                != if imaginary {
                    "ImaginaryPart"
                } else {
                    "RealPart"
                }
            {
                continue;
            }
            for (real, scaled, real_first) in [
                (&sum.left, &sum.right, true),
                (&sum.right, &sum.left, false),
            ] {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = scaled.as_ref()
                else {
                    continue;
                };
                let (coefficient, unit_first) = if matches!(
                    product.left.as_ref(),
                    Obj::Literal(Literal::ImaginaryUnit(_))
                ) {
                    (&product.right, true)
                } else if matches!(
                    product.right.as_ref(),
                    Obj::Literal(Literal::ImaginaryUnit(_))
                ) {
                    (&product.left, false)
                } else {
                    continue;
                };
                if target.ir()
                    != if imaginary {
                        coefficient.ir()
                    } else {
                        real.ir()
                    }
                {
                    continue;
                }
                for (result, subject) in [(real_proof, real), (imaginary_proof, coefficient)] {
                    if !matches!(source_subject(result)?, Fact::AtomicFact(AtomicFact::InFact(ref f))
                        if f.element.ir() == subject.ir() && f.set == Obj::StandardSet(StandardSet::R))
                    {
                        return Err(LeanCompileError::unsupported(
                            "Complex/RectangularRequirementSubject",
                        ));
                    }
                }
                let first = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(std::slice::from_ref(real_proof)),
                    0,
                );
                let first_compiled = self.compile_verify(real_proof, &first)?;
                let first_fact = source_subject(real_proof)?;
                let first_definition =
                    self.emit_internal_fact(&first_fact, &first_compiled, &first)?;
                let completed = SourcePosition { before: 1, ..first };
                let second = SourcePosition::new(
                    Some(&completed),
                    SourceOwner::EqualityRequirements(std::slice::from_ref(imaginary_proof)),
                    0,
                );
                let second_compiled = self.compile_verify(imaginary_proof, &second)?;
                let second_fact = source_subject(imaginary_proof)?;
                let second_definition =
                    self.emit_internal_fact(&second_fact, &second_compiled, &second)?;
                let a = self.compile_object_reference(real, position)?;
                let b = self.compile_object_reference(coefficient, position)?;
                let law = if imaginary {
                    "imaginaryPartRectangularValue"
                } else {
                    "realPartRectangularValue"
                };
                let symmetric = if reversed { ".symm" } else { "" };
                return Ok(format!("(by\n  {}\n  {}\n  exact (Litex.{law} (Litex.denote {a}) (Litex.denote {b}) h_{} h_{} {real_first} {unit_first}){symmetric}\n)", first_definition.replace('\n', "\n  "), second_definition.replace('\n', "\n  "), first_fact.fact_id().value(), second_fact.fact_id().value()));
            }
        }
        Err(LeanCompileError::unsupported(
            "Complex/RectangularEndpoints",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_complex_product_projection(
        &self,
        fact: &EqualFact,
        imaginary: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (projection, target) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some((kind, _, Obj::ArithmeticOperator(ArithmeticOperator::Mul(input)))) =
                complex_argument(projection)
            else {
                continue;
            };
            if kind
                != if imaginary {
                    "ImaginaryPart"
                } else {
                    "RealPart"
                }
            {
                continue;
            }
            let (first, second) = match (target, imaginary) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), true) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)), false) => (&p.left, &p.right),
                _ => continue,
            };
            let pair_matches = |term: &Obj, left_kind: &str, right_kind: &str| {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = term else {
                    return false;
                };
                matches!(complex_argument(&p.left), Some((kind, _, arg)) if kind == left_kind && arg.ir() == input.left.ir())
                    && matches!(complex_argument(&p.right), Some((kind, _, arg)) if kind == right_kind && arg.ir() == input.right.ir())
            };
            let valid = if imaginary {
                (pair_matches(first, "RealPart", "ImaginaryPart")
                    && pair_matches(second, "ImaginaryPart", "RealPart"))
                    || (pair_matches(second, "RealPart", "ImaginaryPart")
                        && pair_matches(first, "ImaginaryPart", "RealPart"))
            } else {
                pair_matches(first, "RealPart", "RealPart")
                    && pair_matches(second, "ImaginaryPart", "ImaginaryPart")
            };
            if !valid {
                continue;
            }
            let a = self.compile_numeric_observation(&input.left, position)?.0;
            let b = self.compile_numeric_observation(&input.right, position)?.0;
            let law = if imaginary {
                "complexImaginaryProduct"
            } else {
                "complexRealProduct"
            };
            let symmetric = if projection.ir() == fact.right.ir() {
                "symm; "
            } else {
                ""
            };
            let tactic = if imaginary {
                format!("{symmetric}simpa only [add_comm] using (Litex.{law} {a} {b})")
            } else {
                format!("{symmetric}exact (Litex.{law} {a} {b})")
            };
            return self.compile_complex_native_identity(fact, &tactic, position);
        }
        Err(LeanCompileError::unsupported(
            "Complex/ProductProjectionSubject",
        ))
    }
}
