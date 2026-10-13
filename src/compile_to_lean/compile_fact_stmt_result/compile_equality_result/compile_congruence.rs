use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matching_one_arg_by_one(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (Obj::FnObj(left), Obj::FnObj(right)) = (&fact.left, &fact.right) else {
            return self.compile_arithmetic_congruence(fact, children, position);
        };
        // The verifier peels outer argument groups first and then the remaining
        // function prefix. The current call constructor owns one group only.
        if left.body.len() != 1
            || right.body.len() != 1
            || left.body[0].len() != right.body[0].len()
            || !matches!(left.body[0].len(), 1 | 2)
        {
            return Err(LeanCompileError::unsupported(
                "Equality/MatchingOneArgByOne/FunctionArity",
            ));
        }
        let pairs = crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(
            &fact.left,
            &fact.right,
        )
        .ok_or_else(|| {
            LeanCompileError::new(
                "FunctionCongruence/Constructor",
                "The selected certificate does not peel these original function calls.",
            )
        })?;
        if children.len() != pairs.len() {
            return Err(LeanCompileError::new(
                "FunctionCongruence/Children",
                "Function congruence has the wrong ordered argument and head arity.",
            ));
        }
        let mut compiled = Vec::with_capacity(children.len());
        for (index, (result, (a, b))) in children.iter().zip(pairs).enumerate() {
            match source_subject(result)? {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == a.ir() && eq.right.ir() == b.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "FunctionCongruence/ChildSubject",
                        "The child is not this exact ordered argument or function-head equality.",
                    ))
                }
            }
            let child_position = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            compiled.push(self.compile_verify(result, &child_position)?.1);
        }
        let left = self.compile_object_reference(&fact.left, position)?;
        let right = self.compile_object_reference(&fact.right, position)?;
        if compiled.len() == 2 {
            Ok(format!(
                "(Litex.callCongr {left} {right} {} {})",
                compiled[1], compiled[0]
            ))
        } else {
            Ok(format!(
                "(Litex.call2Congr {left} {right} {} {} {})",
                compiled[2], compiled[0], compiled[1]
            ))
        }
    }

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
        let operation_term = arithmetic_operation_term(operation);
        if compiled.len() == 1 {
            Ok(format!("(congrArg {operation_term} {})", compiled[0]))
        } else {
            Ok(format!(
                "(congrArg₂ {operation_term} {} {})",
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
