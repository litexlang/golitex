use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_rounding_bounds(
        &self,
        fact: &EqualFact,
        ceiling: bool,
        integer: &VerifyFactResult,
        weak: &VerifyFactResult,
        strict: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (rounded, candidate, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let argument = match rounded {
                Obj::ArithmeticOperator(ArithmeticOperator::Floor(p)) if !ceiling => &p.arg,
                Obj::ArithmeticOperator(ArithmeticOperator::Ceil(p)) if ceiling => &p.arg,
                _ => continue,
            };
            let member = source_subject(integer)?;
            let weak_fact = source_subject(weak)?;
            let strict_fact = source_subject(strict)?;
            if !matches!(member,Fact::AtomicFact(AtomicFact::InFact(ref p))
                if p.element.ir()==candidate.ir() && p.set==Obj::StandardSet(StandardSet::Z))
            {
                continue;
            }
            let Fact::AtomicFact(AtomicFact::LessEqualFact(weak_fact)) = weak_fact else {
                continue;
            };
            let Fact::AtomicFact(AtomicFact::LessFact(strict_fact)) = strict_fact else {
                continue;
            };
            let (lo, hi) = if ceiling {
                (argument.as_ref(), candidate)
            } else {
                (candidate, argument.as_ref())
            };
            if weak_fact.left.ir() != lo.ir() || weak_fact.right.ir() != hi.ir() {
                continue;
            }
            let shifted = if ceiling {
                if strict_fact.right.ir() != argument.ir() {
                    continue;
                }
                match &strict_fact.left {
                    Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => (&p.left, &p.right),
                    _ => continue,
                }
            } else {
                if strict_fact.left.ir() != argument.ir() {
                    continue;
                }
                match &strict_fact.right {
                    Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => (&p.left, &p.right),
                    _ => continue,
                }
            };
            if shifted.0.ir() != candidate.ir()
                || !matches!(shifted.1.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
            {
                continue;
            }
            // Native matching verified these three premises independently; no
            // new proof or inference is published between their verifications.
            let proofs = [integer, weak, strict]
                .into_iter()
                .map(|child| self.compile_verify(child, position).map(|p| p.1))
                .collect::<Result<Vec<_>, _>>()?;
            let rounded = self.compile_object_reference(rounded, position)?;
            let candidate = self.compile_object_reference(candidate, position)?;
            let law = if ceiling {
                "ceilFromIntegerBounds"
            } else {
                "floorFromIntegerBounds"
            };
            return Ok(format!(
                "(Litex.{law} {rounded} {candidate} {} {} {}){}",
                proofs[0],
                proofs[1],
                proofs[2],
                if reverse { ".symm" } else { "" }
            ));
        }
        Err(LeanCompileError::unsupported(
            "Rounding/OriginalIntegerBounds",
        ))
    }
}
