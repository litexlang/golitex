use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_positive_integer_power_cancellation(
        &self,
        goal: &EqualFact,
        premise: &EqualFactSearchedProof,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 4 {
            return Err(invalid("CancellationRequirements"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(exponent)) = source_subject(&requirements[2])?
        else {
            return Err(invalid("CancellationExponent"));
        };
        if exponent.set != Obj::StandardSet(StandardSet::Z) {
            return Err(invalid("CancellationExponent"));
        }
        let mut children = Vec::new();
        for (index, (child, (object, carrier))) in requirements[..3]
            .iter()
            .zip([
                (&goal.left, StandardSet::RPos),
                (&goal.right, StandardSet::RPos),
                (&exponent.element, StandardSet::Z),
            ])
            .enumerate()
        {
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                index,
            );
            children.push(self.compile_power_member(child, object, carrier, &prior)?);
        }
        let prior = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            3,
        );
        children.push(self.compile_power_nonzero_child(
            &requirements[3],
            &exponent.element,
            &prior,
        )?);
        let complete = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            requirements.len(),
        );
        // The original third requirement fixes the exponent of both searched
        // powers. This view creates no new source fact or formation evidence.
        let power = |base: &Obj| {
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                base: Box::new(base.clone()),
                exponent: Box::new(exponent.element.clone()),
            }))
        };
        let view = EqualFact {
            fact_id: goal.fact_id,
            left: power(&goal.left),
            right: power(&goal.right),
            line_file: goal.line_file.clone(),
        };
        let equality = self.compile_equality_search(&view, premise, &complete)?;
        Ok(format!(
            "(Litex.positiveIntegerPowerCancellationValue {} {} {} {} {} {} {} {equality})",
            self.compile_object_reference(&goal.left, &complete)?,
            self.compile_object_reference(&goal.right, &complete)?,
            self.compile_object_reference(&exponent.element, &complete)?,
            children[0],
            children[1],
            children[2],
            children[3]
        ))
    }

    fn compile_power_scalar_constant(
        &self,
        object: &Obj,
        value: i128,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if EvalRational::from_obj(object) != EvalRational::new(value, 1) {
            return Err(invalid("ScalarConstant"));
        }
        let term = self.compile_object_reference(object, position)?;
        let observed = self.compile_numeric_observation(object, position)?;
        Ok(format!("(show Litex.denote {term} = M.number ({value} : ℂ) from (({}).trans (congrArg M.number (by norm_num))))",observed.1))
    }
    pub(super) fn compile_power_member(
        &self,
        proof: &VerifyFactResult,
        object: &Obj,
        target: StandardSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let carrier = membership_subject(&source_subject(proof)?, object)?;
        let term = self.compile_object_reference(object, position)?;
        let member = self.compile_verify(proof, position)?.1;
        standard_inclusion_term(&carrier, &target, &term, &member)
    }
    pub(super) fn compile_power_nonzero_child(
        &self,
        proof: &VerifyFactResult,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_nonzero_subject(&source_subject(proof)?, object)?;
        Ok(self.compile_verify(proof, position)?.1)
    }
    pub(super) fn compile_power_native_endpoints(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &str,
        reversed: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let result = format!(
            "(show Litex.Same {} {} from {proof})",
            self.compile_object_reference(left, position)?,
            self.compile_object_reference(right, position)?
        );
        Ok(if reversed {
            format!("{result}.symm")
        } else {
            result
        })
    }
    pub(in crate::compile_to_lean) fn compile_constant_base_power(
        &self,
        fact: &EqualFact,
        domain: Option<StandardSet>,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let zero = domain.is_some();
        let zero_law = match domain {
            None => "",
            Some(StandardSet::NPos) => "zeroPositiveNaturalPowerValue",
            Some(StandardSet::RPos) => "zeroPositiveExponentPowerValue",
            _ => return Err(invalid("ConstantDomain")),
        };
        if requirements.len() != usize::from(zero) {
            return Err(invalid("ConstantRequirements"));
        }
        let value = if zero { 0 } else { 1 };
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) = left else {
                continue;
            };
            if EvalRational::from_obj(&p.base) != EvalRational::new(value, 1)
                || EvalRational::from_obj(right) != EvalRational::new(value, 1)
            {
                continue;
            }
            let base = self.compile_power_scalar_constant(&p.base, value, position)?;
            let result = self.compile_power_scalar_constant(right, value, position)?;
            let term = self.compile_object_reference(left, position)?;
            let proof = if zero {
                let he = self.compile_power_member(
                    &requirements[0],
                    &p.exponent,
                    domain.clone().unwrap(),
                    position,
                )?;
                format!("(Litex.{zero_law} {term} {base} {he})")
            } else {
                format!("(Litex.onePowerValue {term} {base})")
            };
            let proof = format!("({proof}.trans {result}.symm)");
            return Ok(if reversed {
                format!("{proof}.symm")
            } else {
                proof
            });
        }
        Err(invalid("ConstantEndpoints"))
    }
    pub(in crate::compile_to_lean) fn compile_negative_integer_reciprocal(
        &self,
        fact: &EqualFact,
        children: [&VerifyFactResult; 3],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)),
                Obj::ArithmeticOperator(ArithmeticOperator::Div(q)),
            ) = (left, right)
            else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(negative)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(other)),
            ) = (p.exponent.as_ref(), q.right.as_ref())
            else {
                continue;
            };
            if !literal_one(&q.left)
                || p.base.ir() != other.base.ir()
                || negative.arg.ir() != other.exponent.ir()
            {
                continue;
            }
            let a = self.compile_object_reference(&p.base, position)?;
            let e = self.compile_object_reference(&other.exponent, position)?;
            let ha = self.compile_power_member(children[0], &p.base, StandardSet::C, position)?;
            let he =
                self.compile_power_member(children[1], &other.exponent, StandardSet::Z, position)?;
            let h0 = self.compile_power_nonzero_child(children[2], &p.base, position)?;
            return self.compile_power_native_endpoints(
                left,
                right,
                &format!("(Litex.negativeIntegerPowerReciprocalValue {a} {e} {ha} {he} {h0})"),
                reversed,
                position,
            );
        }
        Err(invalid("NegativeReciprocalEndpoints"))
    }
    pub(in crate::compile_to_lean) fn compile_reciprocal_negative_one(
        &self,
        fact: &EqualFact,
        quotient: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(invalid("ReciprocalRequirements"));
        }
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = left else {
                continue;
            };
            let power = if quotient {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = right else {
                    continue;
                };
                if product.left.ir() != div.left.ir() {
                    continue;
                }
                product.right.as_ref()
            } else {
                if !literal_one(&div.left) {
                    continue;
                }
                right
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) = power else {
                continue;
            };
            if p.base.ir() != div.right.ir()
                || EvalRational::from_obj(&p.exponent) != EvalRational::new(-1, 1)
            {
                continue;
            }
            let h0 = self.compile_power_nonzero_child(&requirements[0], &div.right, position)?;
            let exponent = self.compile_object_reference(&p.exponent, position)?;
            let he = self.compile_power_scalar_constant(&p.exponent, -1, position)?;
            // These are the exact source division's WD carriers. No fresh
            // membership or nonzero verification is requested here.
            let term = self.compile_object_reference(left, position)?;
            let law = if quotient {
                "quotientNegativeOnePowerValue"
            } else {
                "reciprocalNegativeOnePowerValue"
            };
            let proof = if quotient {
                format!("(let _power_div := {term}; Litex.{law} _power_div.val.left _power_div.val.right {exponent} _power_div.wd.1 _power_div.wd.2.1 {h0} {he})")
            } else {
                format!("(let _power_div := {term}; Litex.{law} _power_div.val.right {exponent} _power_div.wd.2.1 {h0} {he})")
            };
            return self.compile_power_native_endpoints(left, right, &proof, reversed, position);
        }
        Err(invalid("ReciprocalEndpoints"))
    }
    pub(in crate::compile_to_lean) fn compile_natural_product_power(
        &self,
        fact: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() == 5 {
            return self.compile_integer_product_distribution(fact, requirements, position);
        }
        if requirements.len() != 3 {
            return Err(invalid("ProductPowerNaturalRequirements"));
        }
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(q)),
            ) = (left, right)
            else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(base)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
            ) = (p.base.as_ref(), q.left.as_ref(), q.right.as_ref())
            else {
                continue;
            };
            if base.left.ir() != a.base.ir()
                || base.right.ir() != b.base.ir()
                || p.exponent.ir() != a.exponent.ir()
                || p.exponent.ir() != b.exponent.ir()
            {
                continue;
            }
            let ha =
                self.compile_power_member(&requirements[0], &base.left, StandardSet::C, position)?;
            let hb =
                self.compile_power_member(&requirements[1], &base.right, StandardSet::C, position)?;
            let he =
                self.compile_power_member(&requirements[2], &p.exponent, StandardSet::N, position)?;
            let proof = format!(
                "(Litex.naturalPowerProductValue {} {} {} {ha} {hb} {he})",
                self.compile_object_reference(&base.left, position)?,
                self.compile_object_reference(&base.right, position)?,
                self.compile_object_reference(&p.exponent, position)?
            );
            return self.compile_power_native_endpoints(left, right, &proof, reversed, position);
        }
        Err(invalid("ProductPowerEndpoints"))
    }
}
fn literal_one(obj: &Obj) -> bool {
    matches!(obj,Obj::Literal(Literal::Number(n))if n.normalized_value=="1")
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("PowerBuiltin/{part}"))
}
