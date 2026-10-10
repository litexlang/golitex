use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_arithmetic_congruence_strategy(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (_, pairs) = arithmetic_constructor_pairs(&fact.left, &fact.right)
            .ok_or_else(|| LeanCompileError::unsupported("ArithmeticCongruence/Constructor"))?;
        if requirements.len() != pairs.len() || children.len() != requirements.len() {
            return Err(LeanCompileError::new(
                "ArithmeticCongruence/Requirements",
                "The selected strategy has the wrong ordered requirement arity.",
            ));
        }
        for ((requirement, child), (left, right)) in requirements.iter().zip(children).zip(pairs) {
            let subject = source_subject(child)?;
            if subject.fact_id() != requirement.fact_id() || subject.ir() != requirement.ir() {
                return Err(LeanCompileError::new(
                    "ArithmeticCongruence/RequirementSubject",
                    "The child does not verify the exact recorded requirement and ID.",
                ));
            }
            match requirement {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ArithmeticCongruence/RequirementSubject",
                        "The requirement is not this exact ordered operand equality.",
                    ))
                }
            }
        }
        self.compile_arithmetic_congruence(fact, children, position)
    }

    pub(in crate::compile_to_lean) fn compile_arithmetic_congruence(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (operation, pairs) =
            arithmetic_constructor_pairs(&fact.left, &fact.right).ok_or_else(|| {
                LeanCompileError::unsupported("Equality/MatchingOneArgByOne/Constructor")
            })?;
        if children.len() != pairs.len() {
            return Err(LeanCompileError::new(
                "ArithmeticCongruence/Children",
                "Constructor congruence has the wrong ordered child arity.",
            ));
        }
        let mut compiled = Vec::new();
        for (index, (result, (left, right))) in children.iter().zip(pairs).enumerate() {
            let child_position = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let child = self.compile_verify(result, &child_position)?;
            match &source_subject(result)? {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ArithmeticCongruence/ChildSubject",
                        "Congruence child does not prove this exact ordered operand pair.",
                    ))
                }
            }
            compiled.push(child.1);
        }
        if compiled.len() == 1 {
            Ok(format!("(congrArg M.{operation} {})", compiled[0]))
        } else {
            Ok(format!(
                "(congrArg₂ M.{operation} {} {})",
                compiled[0], compiled[1]
            ))
        }
    }

    pub(in crate::compile_to_lean) fn compile_identity(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &TheyAreTheSameProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            TheyAreTheSameProof::SameIr(_) if left.ir() == right.ir() => Ok(format!(
                "(Litex.sameRefl {})",
                self.compile_object_reference(left, position)?
            )),
            TheyAreTheSameProof::SameIr(_) => Err(LeanCompileError::new(
                "Equality/IdentitySubject",
                "Exact identity evidence has different source endpoints.",
            )),
            TheyAreTheSameProof::SameFreeParamShape(_) => {
                Err(LeanCompileError::unsupported("Equality/SameFreeParamShape"))
            }
        }
    }
}
