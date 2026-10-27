use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_complex::complex_argument;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError,LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_conjugation::ConjugationEqualityProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_complex_reconstruction(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (z, expanded, reversed) in [
            (&fact.right, &fact.left, false),
            (&fact.left, &fact.right, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = expanded else {
                continue;
            };
            for (real, imag) in [(&sum.left, &sum.right), (&sum.right, &sum.left)] {
                if !matches!(complex_argument(real),Some(("RealPart",_,a)) if a.ir()==z.ir()) {
                    continue;
                }
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = imag.as_ref()
                else {
                    continue;
                };
                let valid=[(&product.left,&product.right),(&product.right,&product.left)].iter().any(|(part,unit)|matches!(unit.as_ref(),Obj::Literal(Literal::ImaginaryUnit(_))) && matches!(complex_argument(part),Some(("ImaginaryPart",_,a)) if a.ir()==z.ir()));
                if !valid {
                    continue;
                }
                let value = self.compile_numeric_observation(z, position)?.0;
                return self.compile_complex_native_identity(fact,&format!("{}simpa only [add_comm, mul_comm] using (Litex.complexReconstruction {value})",if reversed{"symm; "}else{""}),position);
            }
        }
        Err(LeanCompileError::unsupported(
            "Complex/ReconstructionSubject",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_conjugate_identity(
        &self,
        fact: &EqualFact,
        proof: &ConjugationEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use ConjugationEqualityProof as P;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Some(("Conjugate", _, inner)) = complex_argument(left) {
                let pair = match (proof, inner, right) {
                    (
                        P::ConjugateAdd(_),
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(a)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(b)),
                    ) => Some((&a.left, &a.right, &b.left, &b.right, "star_add")),
                    (
                        P::ConjugateSub(_),
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Sub(b)),
                    ) => Some((&a.left, &a.right, &b.left, &b.right, "star_sub")),
                    (
                        P::ConjugateMul(_),
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
                    ) => Some((&a.left, &a.right, &b.left, &b.right, "star_mul, mul_comm")),
                    (
                        P::ConjugateDiv(_),
                        Obj::ArithmeticOperator(ArithmeticOperator::Div(a)),
                        Obj::ArithmeticOperator(ArithmeticOperator::Div(b)),
                    ) => Some((&a.left, &a.right, &b.left, &b.right, "star_div₀")),
                    _ => None,
                };
                if let Some((x, y, cx, cy, law)) = pair {
                    if matches!(complex_argument(cx),Some(("Conjugate",_,a)) if a.ir()==x.ir())
                        && matches!(complex_argument(cy),Some(("Conjugate",_,a)) if a.ir()==y.ir())
                    {
                        return self.compile_complex_native_identity(
                            fact,
                            &format!("simp only [{law}]"),
                            position,
                        );
                    }
                }
            }
            let Some((outer, _, nested)) = complex_argument(left) else {
                continue;
            };
            let Some(("Conjugate", _, arg)) = complex_argument(nested) else {
                continue;
            };
            let valid = match proof {
                P::ConjugateInvolution(_) => outer == "Conjugate" && arg.ir() == right.ir(),
                P::ConjugateRealPart(_) => {
                    outer == "RealPart"
                        && matches!(complex_argument(right),Some(("RealPart",_,a)) if a.ir()==arg.ir())
                }
                P::ConjugateImaginaryPart(_) => {
                    outer == "ImaginaryPart"
                        && matches!(right,Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) if matches!(complex_argument(&n.arg),Some(("ImaginaryPart",_,a)) if a.ir()==arg.ir()))
                }
                P::ConjugateModulus(_) => {
                    outer == "ComplexAbs"
                        && matches!(complex_argument(right),Some(("ComplexAbs",_,a)) if a.ir()==arg.ir())
                }
                _ => false,
            };
            if valid {
                if matches!(proof, P::ConjugateInvolution(_)) {
                    let term = if left.ir() == fact.left.ir() {
                        "exact star_star _"
                    } else {
                        "exact (star_star _).symm"
                    };
                    return self.compile_complex_native_identity(fact, term, position);
                }
                let law = match proof {
                    P::ConjugateInvolution(_) => "star_star",
                    P::ConjugateRealPart(_) => "Complex.star_def, Complex.conj_re",
                    P::ConjugateImaginaryPart(_) => {
                        "Complex.star_def, Complex.conj_im, Complex.ofReal_neg"
                    }
                    P::ConjugateModulus(_) => "norm_star",
                    _ => unreachable!(),
                };
                return self.compile_complex_native_identity(
                    fact,
                    &format!("simp only [{law}]"),
                    position,
                );
            }
        }
        Err(LeanCompileError::unsupported(
            "Complex/ConjugationRuleOrSubject",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_complex_modulus_product(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some(("ComplexAbs", _, arg)) = complex_argument(left) else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
            ) = (arg, right)
            else {
                continue;
            };
            if matches!(complex_argument(&b.left),Some(("ComplexAbs",_,x)) if x.ir()==a.left.ir())
                && matches!(complex_argument(&b.right),Some(("ComplexAbs",_,x)) if x.ir()==a.right.ir())
            {
                return self.compile_complex_native_identity(
                    fact,
                    "simp only [norm_mul, Complex.ofReal_mul]",
                    position,
                );
            }
        }
        Err(LeanCompileError::unsupported(
            "Complex/ModulusProductSubject",
        ))
    }

    fn compile_complex_native_identity(
        &self,
        fact: &EqualFact,
        tactic: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let x = self.compile_numeric_observation(&fact.left, position)?;
        let y = self.compile_numeric_observation(&fact.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by {tactic}))",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }
}
