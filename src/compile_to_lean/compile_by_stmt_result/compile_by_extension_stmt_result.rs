use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecByExtensionStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_extension_result(
        &self,
        result: &ExecByExtensionStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecByExtensionStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Extension/Failed"));
        };
        let VerifyFactWellDefinedResult::Success(wd) = &proof.goal_wd else {
            return Err(LeanCompileError::unsupported("Extension/GoalWD"));
        };
        let goal = self.resolve_fact(
            proof.stored.primary_fact_id(),
            &SourcePosition {
                before: 3,
                ..*position
            },
        )?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &goal else {
            return Err(LeanCompileError::unsupported("Extension/Goal"));
        };
        self.compile_fact_wd(wd, &goal, position)?;
        for (result, left, right) in [
            (&proof.left_to_right, &equal.left, &equal.right),
            (&proof.right_to_left, &equal.right, &equal.left),
        ] {
            if !matches!(source_subject(result)?, Fact::AtomicFact(AtomicFact::SubsetFact(f))
                if f.left.ir() == left.ir() && f.right.ir() == right.ir())
            {
                return Err(LeanCompileError::new(
                    "Extension/Direction",
                    "A retained subset direction differs from the original equality endpoints.",
                ));
            }
        }
        let caller = SourcePosition {
            before: 1,
            ..*position
        };
        let scope = SourcePosition::new(Some(&caller), SourceOwner::Extension(proof), 0);
        let mut steps = Vec::new();
        for (step_index, step) in proof.proof_steps.iter().enumerate() {
            steps.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: step_index,
                    ..scope
                },
                step_index + 1,
                true,
            )?);
        }
        let forward = self.compile_verify(
            &proof.left_to_right,
            &SourcePosition {
                before: proof.proof_steps.len(),
                ..scope
            },
        )?;
        let reverse = self.compile_verify(
            &proof.right_to_left,
            &SourcePosition {
                before: proof.proof_steps.len() + 1,
                ..scope
            },
        )?;
        let formed = SourcePosition::new(Some(position), SourceOwner::FactWD(wd), usize::MAX);
        let left = self.compile_object_reference(&equal.left, &formed)?;
        let right = self.compile_object_reference(&equal.right, &formed)?;
        steps.push(format!(
            "have _extension_forward : {} := {}",
            forward.0, forward.1
        ));
        steps.push(format!(
            "have _extension_reverse : {} := {}",
            reverse.0, reverse.1
        ));
        steps.push(format!("exact Litex.SetSemantics.ext _ _ (Litex.isSet {left}) (Litex.isSet {right}) (fun x => ⟨_extension_forward x, _extension_reverse x⟩)"));
        let term = format!("(by\n  {}\n)", steps.join("\n").replace('\n', "\n  "));
        self.emit_by_completed_fact(
            &goal,
            (self.fact_proposition(&goal, &formed)?, term),
            &proof.stored,
            position,
            3,
            index,
            local,
        )
    }
}
