use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
impl LitexToLeanCompiler {
    pub(super) fn integer_power_pair_profile(requirements: &[VerifyFactResult]) -> bool {
        requirements.len()==4&&matches!(source_subject(&requirements[1]),Ok(Fact::AtomicFact(AtomicFact::NotEqualFact(_))))&&requirements[2..].iter().all(|p|matches!(source_subject(p),Ok(Fact::AtomicFact(AtomicFact::InFact(f)))if f.set==Obj::StandardSet(StandardSet::Z)))
    }
    pub(super) fn compile_integer_binary_power_law(
        &self,
        goal: &EqualFact,
        product: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !Self::integer_power_pair_profile(requirements) {
            return Err(invalid("PairProfile"));
        }
        let (
            Fact::AtomicFact(AtomicFact::InFact(base)),
            Fact::AtomicFact(AtomicFact::InFact(first)),
            Fact::AtomicFact(AtomicFact::InFact(second)),
        ) = (
            source_subject(&requirements[0])?,
            source_subject(&requirements[2])?,
            source_subject(&requirements[3])?,
        )
        else {
            return Err(invalid("PairMemberships"));
        };
        let (a, m, n) = (&base.element, &first.element, &second.element);
        for (left, right, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Pow(combined)) = right else {
                continue;
            };
            if combined.base.ir() != a.ir() {
                continue;
            }
            let valid = if product {
                let (
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(factors)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),
                ) = (left, combined.exponent.as_ref())
                else {
                    continue;
                };
                let (
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(q)),
                ) = (factors.left.as_ref(), factors.right.as_ref())
                else {
                    continue;
                };
                p.base.ir() == a.ir()
                    && q.base.ir() == a.ir()
                    && p.exponent.ir() == m.ir()
                    && q.exponent.ir() == n.ir()
                    && sum.left.ir() == m.ir()
                    && sum.right.ir() == n.ir()
            } else {
                let (
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(outer)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(exponents)),
                ) = (left, combined.exponent.as_ref())
                else {
                    continue;
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(inner)) = outer.base.as_ref()
                else {
                    continue;
                };
                inner.base.ir() == a.ir()
                    && inner.exponent.ir() == m.ir()
                    && outer.exponent.ir() == n.ir()
                    && exponents.left.ir() == m.ir()
                    && exponents.right.ir() == n.ir()
            };
            if !valid {
                continue;
            }
            let mut proofs = Vec::new();
            for i in 0..4 {
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    i,
                );
                proofs.push(match i {
                    0 => self.compile_power_member(&requirements[i], a, StandardSet::C, &prior)?,
                    1 => self.compile_power_nonzero_child(&requirements[i], a, &prior)?,
                    2 => self.compile_power_member(&requirements[i], m, StandardSet::Z, &prior)?,
                    _ => self.compile_power_member(&requirements[i], n, StandardSet::Z, &prior)?,
                });
            }
            let complete = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                4,
            );
            let law = if product {
                "integerPowerProductValue"
            } else {
                "integerPowerOfPowerValue"
            };
            let proof = format!(
                "(Litex.{law} {} {} {} {})",
                self.compile_object_reference(a, &complete)?,
                self.compile_object_reference(m, &complete)?,
                self.compile_object_reference(n, &complete)?,
                proofs.join(" ")
            );
            return self.compile_power_native_endpoints(left, right, &proof, reversed, &complete);
        }
        Err(invalid("PairEndpoints"))
    }
    pub(super) fn compile_integer_product_distribution(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 5 {
            return Err(invalid("DistributionRequirements"));
        }
        for (left, right, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
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
            let mut proofs = Vec::new();
            for i in 0..5 {
                let prior = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(requirements),
                    i,
                );
                proofs.push(match i {
                    0 => self.compile_power_member(
                        &requirements[i],
                        &base.left,
                        StandardSet::C,
                        &prior,
                    )?,
                    1 => self.compile_power_member(
                        &requirements[i],
                        &base.right,
                        StandardSet::C,
                        &prior,
                    )?,
                    2 => self.compile_power_member(
                        &requirements[i],
                        &p.exponent,
                        StandardSet::Z,
                        &prior,
                    )?,
                    3 => self.compile_power_nonzero_child(&requirements[i], &base.left, &prior)?,
                    _ => self.compile_power_nonzero_child(&requirements[i], &base.right, &prior)?,
                });
            }
            let complete = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                5,
            );
            let proof = format!(
                "(Litex.integerPowerProductDistributionValue {} {} {} {})",
                self.compile_object_reference(&base.left, &complete)?,
                self.compile_object_reference(&base.right, &complete)?,
                self.compile_object_reference(&p.exponent, &complete)?,
                proofs.join(" ")
            );
            return self.compile_power_native_endpoints(left, right, &proof, reversed, &complete);
        }
        Err(invalid("DistributionEndpoints"))
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("IntegerPowerLaw/{part}"))
}
