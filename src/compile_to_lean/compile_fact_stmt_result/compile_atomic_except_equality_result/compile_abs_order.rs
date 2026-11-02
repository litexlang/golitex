use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

fn abs_argument(object: &Obj) -> Option<&Obj> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) = object {
        Some(&p.arg)
    } else {
        None
    }
}
impl LitexToLeanCompiler {
    fn compile_abs_order_zero(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !is_exact_zero(object) {
            return Err(invalid("ZeroEndpoint"));
        }
        let term = self.compile_object_reference(object, position)?;
        let numeric = self.compile_numeric_observation(object, position)?;
        Ok(format!("(show Litex.denote {term} = M.number (0 : ℂ) from (({}).trans (congrArg M.number (by norm_num))))",numeric.1))
    }
    pub(super) fn compile_abs_self_order(
        &self,
        goal: &AtomicFact,
        lower: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(invalid("SelfStrictness"));
        }
        if lower {
            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) = low else {
                return Err(invalid("SelfLowerSubject"));
            };
            if !matches!(abs_argument(&p.right),Some(arg)if arg.ir()==high.ir()) {
                return Err(invalid("SelfLowerArgument"));
            }
            let zero = self.compile_abs_order_zero(&p.left, position)?;
            Ok(format!(
                "(Litex.absSelfLowerValue {} {zero})",
                self.compile_object_reference(low, position)?
            ))
        } else {
            if !matches!(abs_argument(high),Some(arg)if arg.ir()==low.ir()) {
                return Err(invalid("SelfUpperArgument"));
            }
            Ok(format!(
                "(Litex.absSelfUpperValue {})",
                self.compile_object_reference(high, position)?
            ))
        }
    }
    pub(super) fn compile_abs_triangle_order(
        &self,
        goal: &AtomicFact,
        kind: u8,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(invalid("TriangleStrictness"));
        }
        let valid = if kind == 0 {
            let (
                Some(Obj::ArithmeticOperator(ArithmeticOperator::Add(sum))),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(bound)),
            ) = (abs_argument(low), high)
            else {
                return Err(invalid("TriangleSubjects"));
            };
            matches!((abs_argument(&bound.left),abs_argument(&bound.right)),(Some(a),Some(b))if sum.left.ir()==a.ir()&&sum.right.ir()==b.ir())
        } else {
            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(difference)) = low else {
                return Err(invalid("ReverseTriangleDifference"));
            };
            let (Some(a), Some(b)) = (
                abs_argument(&difference.left),
                abs_argument(&difference.right),
            ) else {
                return Err(invalid("ReverseTriangleAbsoluteValues"));
            };
            let (s, t) = match (abs_argument(high), kind) {
                (Some(Obj::ArithmeticOperator(ArithmeticOperator::Add(sum))), 1) => {
                    (&sum.left, &sum.right)
                }
                (Some(Obj::ArithmeticOperator(ArithmeticOperator::Sub(sum))), 2) => {
                    (&sum.left, &sum.right)
                }
                _ => return Err(invalid("ReverseTriangleSubject")),
            };
            s.ir() == a.ir() && t.ir() == b.ir()
        };
        if !valid {
            return Err(invalid("TriangleArguments"));
        }
        let law = match kind {
            0 => "absTriangleValue",
            1 => "absReverseTriangleAddValue",
            2 => "absReverseTriangleSubValue",
            _ => return Err(invalid("TriangleKind")),
        };
        Ok(format!(
            "(Litex.{law} {} {} rfl rfl)",
            self.compile_object_reference(low, position)?,
            self.compile_object_reference(high, position)?
        ))
    }
    pub(super) fn compile_abs_bound_projection(
        &self,
        goal: &AtomicFact,
        negative: bool,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let AtomicFact::LessEqualFact(known) = &premise.fact else {
            return Err(invalid("ProjectionPremise"));
        };
        let Some(argument) = abs_argument(&known.left) else {
            return Err(invalid("ProjectionRoot"));
        };
        if strict || known.right.ir() != high.ir() {
            return Err(invalid("ProjectionBound"));
        }
        let zero = if negative {
            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(q)) = low else {
                return Err(invalid("NegativeProjectionSubject"));
            };
            if q.right.ir() != argument.ir() {
                return Err(invalid("NegativeProjectionArgument"));
            }
            Some(self.compile_abs_order_zero(&q.left, position)?)
        } else {
            if low.ir() != argument.ir() {
                return Err(invalid("ProjectionArgument"));
            }
            None
        };
        let proof = self.compile_order_known_premise(premise, position)?.1;
        let root = self.compile_object_reference(&known.left, position)?;
        let bound = self.compile_object_reference(high, position)?;
        Ok(if let Some(zero) = zero {
            format!(
                "(Litex.absBoundNegativeProjectionValue {root} {} {bound} {zero} rfl {proof})",
                self.compile_object_reference(low, position)?
            )
        } else {
            format!("(Litex.absBoundUpperProjectionValue {root} {bound} {proof})")
        })
    }
    pub(super) fn compile_abs_symmetric_bound(
        &self,
        goal: &AtomicFact,
        upper: &VerifyFactResult,
        negative: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let Some(argument) = abs_argument(low) else {
            return Err(invalid("SymmetricRoot"));
        };
        let (
            Fact::AtomicFact(AtomicFact::LessEqualFact(upper_fact)),
            Fact::AtomicFact(AtomicFact::LessEqualFact(negative_fact)),
        ) = (source_subject(upper)?, source_subject(negative)?)
        else {
            return Err(invalid("SymmetricChildren"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(q)) = &negative_fact.left else {
            return Err(invalid("SymmetricNegativeProfile"));
        };
        if strict
            || upper_fact.left.ir() != argument.ir()
            || upper_fact.right.ir() != high.ir()
            || q.right.ir() != argument.ir()
            || negative_fact.right.ir() != high.ir()
        {
            return Err(invalid("SymmetricSubjects"));
        }
        let upper = self
            .compile_verify(upper, &position.atomic_search_prior(0)?)?
            .1;
        let negative = self
            .compile_verify(negative, &position.atomic_search_prior(1)?)?
            .1;
        let complete = position.atomic_search_prior(2)?;
        let zero = self.compile_abs_order_zero(&q.left, &complete)?;
        Ok(format!(
            "(Litex.absFromSymmetricBoundsValue {} {} {} {zero} rfl {upper} {negative})",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(&negative_fact.left, &complete)?,
            self.compile_object_reference(high, &complete)?
        ))
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("AbsOrder/{part}"))
}
