use crate::compile_to_lean::compile_real_set_bounds::contains_parameter;
use crate::compile_to_lean::helper::{is_exact_zero, source_subject};
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_rational_ratio_witness(
        &self,
        fact: &PlainExistFact,
        child: &VerifyFactResult,
        positive: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let bindings = bindings(fact)?;
        let [(a, a_set), (b, b_set)] = bindings.as_slice() else {
            return Err(invalid("RatioBinders"));
        };
        if a.id == b.id
            || **a_set != Obj::StandardSet(StandardSet::Z)
            || **b_set
                != Obj::StandardSet(if positive {
                    StandardSet::Z
                } else {
                    StandardSet::ZStar
                })
            || fact.facts.len() != if positive { 2 } else { 1 }
        {
            return Err(invalid("RatioCarriers"));
        }
        let a_obj = Obj::Identifier(IdentifierObj::from_bound_name(a));
        let b_obj = Obj::Identifier(IdentifierObj::from_bound_name(b));
        if positive {
            let valid = match &fact.facts[0] {
                QuantifierFreeFact::AtomicFact(AtomicFact::GreaterFact(p)) => {
                    p.left.ir() == b_obj.ir() && is_exact_zero(&p.right)
                }
                QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(p)) => {
                    is_exact_zero(&p.left) && p.right.ir() == b_obj.ir()
                }
                _ => false,
            };
            if !valid {
                return Err(invalid("PositiveDenominatorFirst"));
            }
        }
        let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal)) =
            &fact.facts[usize::from(positive)]
        else {
            return Err(invalid("RatioEquality"));
        };
        let ratio = |object: &Obj| {
            matches!(object,Obj::ArithmeticOperator(ArithmeticOperator::Div(p))
            if p.left.ir()==a_obj.ir() && p.right.ir()==b_obj.ir())
        };
        let (q, reverse) = if ratio(&equal.right) {
            (&equal.left, false)
        } else if ratio(&equal.left) {
            (&equal.right, true)
        } else {
            return Err(invalid("RatioOperands"));
        };
        if contains_parameter(q, a.id)
            || contains_parameter(q, b.id)
            || !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::InFact(p))
                if p.element.ir()==q.ir() && p.set==Obj::StandardSet(StandardSet::Q))
        {
            return Err(invalid("RationalMember"));
        }
        let proof = self.compile_verify(child, position)?.1;
        let q = self.compile_object_reference(
            q,
            &SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX),
        )?;
        let law = if positive {
            "rationalPositiveRatioWitness"
        } else {
            "rationalIntegerRatioWitness"
        };
        let application = format!("Litex.{law} {q} {proof}");
        if !reverse {
            return Ok(format!("({application})"));
        }
        Ok(if positive {
            format!("(by obtain ⟨a,ha,b,hb,hpos,heq⟩ := {application}; exact ⟨a,ha,b,hb,hpos,heq.symm⟩)")
        } else {
            format!("(by obtain ⟨a,ha,b,hb,heq⟩ := {application}; exact ⟨a,ha,b,hb,heq.symm⟩)")
        })
    }

    pub(super) fn compile_integer_multiple_witness(
        &self,
        fact: &PlainExistFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let bindings = bindings(fact)?;
        let [(parameter, carrier)] = bindings.as_slice() else {
            return Err(invalid("MultipleBinder"));
        };
        if **carrier != Obj::StandardSet(StandardSet::Z)
            || requirements.len() != 4
            || children.len() != 4
        {
            return Err(invalid("MultipleStages"));
        }
        let [QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal))] = fact.facts.as_slice()
        else {
            return Err(invalid("MultipleEquality"));
        };
        let bound = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        for (product, dividend, reverse_equality) in [
            (&equal.right, &equal.left, false),
            (&equal.left, &equal.right, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = product else {
                continue;
            };
            let (divisor, reverse_product) = if product.right.ir() == bound.ir() {
                (&product.left, false)
            } else if product.left.ir() == bound.ir() {
                (&product.right, true)
            } else {
                continue;
            };
            if contains_parameter(dividend, parameter.id)
                || contains_parameter(divisor, parameter.id)
            {
                continue;
            }
            for (requirement, object) in requirements[..2].iter().zip([dividend, divisor.as_ref()])
            {
                if !matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(p))
                    if p.element.ir()==object.ir() && p.set==Obj::StandardSet(StandardSet::Z))
                {
                    return Err(invalid("MultipleIntegerSubjects"));
                }
            }
            if !matches!(&requirements[2],Fact::AtomicFact(AtomicFact::NotEqualFact(p))
                if p.left.ir()==divisor.ir() && is_exact_zero(&p.right))
            {
                return Err(invalid("MultipleNonzeroSubject"));
            }
            let Fact::AtomicFact(AtomicFact::EqualFact(remainder)) = &requirements[3] else {
                return Err(invalid("MultipleRemainderEquality"));
            };
            if !is_exact_zero(&remainder.right)
                || !matches!(&remainder.left,Obj::IntegerOperator(IntegerOperator::Mod(p))
                    if p.left.ir()==dividend.ir() && p.right.ir()==divisor.ir())
            {
                return Err(invalid("MultipleRemainderSubject"));
            }
            let mut proofs = Vec::new();
            for (requirement, child) in requirements.iter().zip(children) {
                if source_subject(child)? != *requirement {
                    return Err(invalid("MultipleOriginalChild"));
                }
                proofs.push(self.compile_verify(child, position)?.1);
            }
            let a = self.compile_object_reference(
                dividend,
                &SourcePosition::new(
                    Some(position),
                    SourceOwner::Verify(&children[0]),
                    usize::MAX,
                ),
            )?;
            let b = self.compile_object_reference(
                divisor,
                &SourcePosition::new(
                    Some(position),
                    SourceOwner::Verify(&children[1]),
                    usize::MAX,
                ),
            )?;
            let application = format!(
                "Litex.integerMultipleFromZeroRemainder {a} {b} {} {} {} {} {reverse_product}",
                proofs[0], proofs[1], proofs[2], proofs[3]
            );
            return Ok(if reverse_equality {
                format!("(by obtain ⟨k,hk,heq⟩ := {application}; exact ⟨k,hk,heq.symm⟩)")
            } else {
                format!("({application})")
            });
        }
        Err(invalid("MultipleOperands"))
    }
}

fn bindings(fact: &PlainExistFact) -> Result<Vec<(&BoundName, &Obj)>, LeanCompileError> {
    let mut values = Vec::new();
    for group in &fact.typed_parameters.groups {
        let ParamType::Obj(carrier) = &group.param_type else {
            return Err(invalid("BinderKind"));
        };
        for parameter in &group.params {
            values.push((parameter, carrier));
        }
    }
    Ok(values)
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Exist/RationalInteger/{stage}"))
}
