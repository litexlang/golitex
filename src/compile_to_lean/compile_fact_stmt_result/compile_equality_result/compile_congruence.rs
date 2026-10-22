use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::{
    helper::set_builders_alpha_equal, SameFreeParamShapeProof,
};

impl LitexToLeanCompiler {
    pub(super) fn compile_tuple_component_strategy(
        &self,
        fact: &EqualFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(
            (&fact.left, &fact.right),
            (
                Obj::ProductShape(ProductShape::Tuple(_)),
                Obj::ProductShape(ProductShape::Tuple(_))
            )
        ) || requirements.len() != children.len()
        {
            return Err(LeanCompileError::unsupported("TupleStrategy/Requirements"));
        }
        for (requirement, child) in requirements.iter().zip(children) {
            if source_subject(child)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "TupleStrategy/RequirementSubject",
                ));
            }
        }
        self.compile_matching_one_arg_by_one(fact, children, position)
    }

    pub(in crate::compile_to_lean) fn compile_matching_one_arg_by_one(
        &self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let (
            Obj::ProductShape(ProductShape::Tuple(left)),
            Obj::ProductShape(ProductShape::Tuple(right)),
        ) = (&fact.left, &fact.right)
        {
            if left.args.is_empty()
                || left.args.len() != right.args.len()
                || children.len() != left.args.len()
            {
                return Err(LeanCompileError::new(
                    "TupleCongruence/Children",
                    "Tuple congruence needs one original equality per ordered component.",
                ));
            }
            let mut components = Vec::with_capacity(children.len());
            for (index, ((left, right), child)) in
                left.args.iter().zip(&right.args).zip(children).enumerate()
            {
                match source_subject(child)? {
                    Fact::AtomicFact(AtomicFact::EqualFact(eq))
                        if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "TupleCongruence/ChildSubject",
                            "The child is not this exact ordered component equality.",
                        ))
                    }
                }
                let child_position = SourcePosition::new(
                    Some(position),
                    SourceOwner::EqualityRequirements(children),
                    index,
                );
                components.push(self.compile_verify(child, &child_position)?.1);
            }
            return Ok(format!(
                "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext {}))",
                finite_vector_proof(&components),
            ));
        }
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
        self.compile_object_reference(&fact.left, position)?;
        self.compile_object_reference(&fact.right, position)?;
        if compiled.len() == 2 {
            Ok(format!(
                "(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {} {})",
                compiled[1], compiled[0]
            ))
        } else {
            Ok(format!(
                "(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {} (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) {} {}))",
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
            // The child's closed WD lets cannot determine metavariables from
            // outside their scope. Give congrArg the exact semantic endpoints,
            // using only this child's two already checked formation stages.
            let formed = SourcePosition::new(Some(&child_position), SourceOwner::Verify(result), 2);
            compiled.push(format!(
                "(show {} = {} from {})",
                self.compile_normalization_value(left, &formed)?,
                self.compile_normalization_value(right, &formed)?,
                child.1,
            ));
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
            TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::SetBuilder(_)) => {
                let (
                    Obj::SetFormer(SetFormer::SetBuilder(left_set)),
                    Obj::SetFormer(SetFormer::SetBuilder(right_set)),
                ) = (left, right)
                else {
                    return Err(LeanCompileError::new(
                        "Equality/SetBuilderAlphaSubject",
                        "Set-builder alpha evidence requires two set builders.",
                    ));
                };
                if !set_builders_alpha_equal(left_set, right_set) {
                    return Err(LeanCompileError::new(
                        "Equality/SetBuilderAlphaSubject",
                        "The recorded endpoints differ beyond renaming bound parameters.",
                    ));
                }
                let left = self.compile_object_reference(left, position)?;
                let right = self.compile_object_reference(right, position)?;
                Ok(format!("(show Litex.Same {left} {right} from rfl)"))
            }
            TheyAreTheSameProof::SameFreeParamShape(_) => {
                Err(LeanCompileError::unsupported("Equality/SameFreeParamShape"))
            }
        }
    }
}
