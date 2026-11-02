//! Consume the carrier coverage recorded by append_iteration_coverage_requirements.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(super) fn validate_range_input(
    input: &Obj,
    start: &Obj,
    end: &Obj,
    requirements: &[VerifyFactResult],
) -> Result<usize, LeanCompileError> {
    let expected = match input {
        Obj::StandardSet(StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C) => {
            return Ok(0);
        }
        Obj::StandardSet(StandardSet::N) => Some(StandardSet::N),
        Obj::StandardSet(StandardSet::NPos | StandardSet::QPos | StandardSet::RPos) => {
            Some(StandardSet::NPos)
        }
        _ => None,
    };
    let source = requirements
        .first()
        .ok_or_else(|| LeanCompileError::unsupported("RangeInput/MissingCoverage"))?;
    let fact = source_subject(source)?;
    let valid = match (expected, fact) {
        (Some(set), Fact::AtomicFact(AtomicFact::InFact(f))) => {
            f.element.ir() == start.ir() && f.set == Obj::StandardSet(set)
        }
        (None, Fact::AtomicFact(AtomicFact::SubsetFact(f))) => {
            matches!(&f.left, Obj::SetFormer(SetFormer::ClosedRange(range))
                if range.start.ir() == start.ir() && range.end.ir() == end.ir())
                && f.right.ir() == input.ir()
        }
        _ => false,
    };
    if !valid {
        return Err(LeanCompileError::unsupported("RangeInput/CoverageSubject"));
    }
    Ok(1)
}

impl LitexToLeanCompiler {
    pub(super) fn compile_range_input_member(
        &self,
        input: &Obj,
        endpoints: [&str; 2],
        integer_proofs: [&str; 2],
        coverage: Option<&String>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [first, last] = endpoints;
        if let Obj::StandardSet(
            set @ (StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C),
        ) = input
        {
            return Ok(format!(
                "(Litex.integerInUnboundedCarrier .{} (by decide) k)",
                standard_value_constructor(set)?
            ));
        }
        let coverage =
            coverage.ok_or_else(|| LeanCompileError::unsupported("RangeInput/MissingCoverage"))?;
        Ok(match input {
            Obj::StandardSet(StandardSet::N) => {
                format!("(Litex.integerInNaturalAbove {first} {coverage} k hlow)")
            }
            Obj::StandardSet(StandardSet::NPos | StandardSet::QPos | StandardSet::RPos) => {
                let positive = format!("(Litex.integerInPositiveAbove {first} {coverage} k hlow)");
                let number = "(Litex.number (M := M) (k : ℂ))";
                match input {
                    Obj::StandardSet(StandardSet::NPos) => positive,
                    Obj::StandardSet(StandardSet::QPos) => format!(
                        "(Litex.inQPos_intro {number} (Litex.integerToRational {number} (Litex.NativeBridge.numberInZ k)) (Litex.inNPos_positive {number} {positive}))"
                    ),
                    _ => format!(
                        "(Litex.inRPos_intro {number} (Litex.integerToReal {number} (Litex.NativeBridge.numberInZ k)) (Litex.inNPos_positive {number} {positive}))"
                    ),
                }
            }
            _ => {
                let carrier = self.compile_object_reference(input, position)?;
                format!(
                    "(Litex.integerInCoveredRange {first} {last} {carrier} {} {} {coverage} k hlow hhigh)",
                    integer_proofs[0], integer_proofs[1]
                )
            }
        })
    }
}
