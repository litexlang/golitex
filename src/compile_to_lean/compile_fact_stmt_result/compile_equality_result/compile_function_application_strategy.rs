use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::fn_obj_prefix_obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_composed_structure::FunctionApplicationCongruenceProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    /// Replay the callable-prefix equality before the last group's arguments.
    /// This route does not require equality of the prefix's original inputs.
    pub(super) fn compile_function_application_strategy(
        &self,
        goal: &EqualFact,
        proof: &FunctionApplicationCongruenceProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (Obj::FnObj(left), Obj::FnObj(right)) = (&goal.left, &goal.right) else {
            return Err(LeanCompileError::unsupported(
                "FunctionApplicationStrategy/Constructor",
            ));
        };
        let (Some(a), Some(b)) = (left.body.last(), right.body.last()) else {
            return Err(LeanCompileError::unsupported(
                "FunctionApplicationStrategy/EmptyCall",
            ));
        };
        if a.is_empty() || a.len() != b.len() {
            return Err(LeanCompileError::unsupported(
                "FunctionApplicationStrategy/Arity",
            ));
        }
        let mut pairs = vec![(
            fn_obj_prefix_obj(left, left.body.len() - 1),
            fn_obj_prefix_obj(right, right.body.len() - 1),
        )];
        pairs.extend(
            a.iter()
                .zip(b)
                .map(|(a, b)| (a.as_ref().clone(), b.as_ref().clone())),
        );
        let children = &proof.proof_of_requirement_facts;
        if proof.requirement_facts.len() != pairs.len() || children.len() != pairs.len() {
            return Err(LeanCompileError::unsupported(
                "FunctionApplicationStrategy/Requirements",
            ));
        }
        let mut equalities = Vec::with_capacity(pairs.len());
        for (index, ((requirement, child), (a, b))) in proof
            .requirement_facts
            .iter()
            .zip(children)
            .zip(pairs)
            .enumerate()
        {
            if source_subject(child)? != *requirement
                || !matches!(requirement,
                Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==a.ir() && eq.right.ir()==b.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "FunctionApplicationStrategy/RequirementSubject",
                ));
            }
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            let compiled = self.compile_verify(child, &prior)?;
            let checked = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 2);
            equalities.push(format!(
                "(show {} = {} from {})",
                self.compile_normalization_value(&a, &checked)?,
                self.compile_normalization_value(&b, &checked)?,
                compiled.1
            ));
        }
        // Both complete original formations remain mandatory. The expression
        // below only composes the already checked semantic equality children.
        self.compile_object_reference(&goal.left, position)?;
        self.compile_object_reference(&goal.right, position)?;
        let proof = Self::function_call_congruence(&equalities[0], &equalities[1..])?;
        Ok(format!(
            "(show {} = {} from {proof})",
            self.compile_normalization_value(&goal.left, position)?,
            self.compile_normalization_value(&goal.right, position)?
        ))
    }

    /// Semantic packing shared by distinct original proof routes. Their callers
    /// own subject validation, original child order, WD and citation scopes.
    pub(super) fn function_call_congruence(
        function: &str,
        arguments: &[String],
    ) -> Result<String, LeanCompileError> {
        let argument = match arguments.len() {
            0 => {
                return Err(LeanCompileError::unsupported(
                    "FunctionCongruence/EmptyArguments",
                ))
            }
            1 => arguments[0].clone(),
            2 => format!(
                "(congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) {} {})",
                arguments[0], arguments[1]
            ),
            _ => format!(
                "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext {}))",
                finite_vector_proof(arguments)
            ),
        };
        Ok(format!(
            "(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {function} {argument})"
        ))
    }
}
