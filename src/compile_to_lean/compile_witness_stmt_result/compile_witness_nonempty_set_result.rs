use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtSuccessResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_witness_nonempty_statement(
        &self,
        proof: &ExecWitnessNonemptySetStmtSuccessResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if proof.proof_steps.len() != proof.statement.proof.len() {
            return Err(LeanCompileError::unsupported("WitnessNonempty/ProofSteps"));
        }
        let object = self.compile_wd(
            success_object_wd(&proof.obj_well_defined, &proof.statement.obj)?,
            position,
        )?;
        let set_prior = SourcePosition {
            before: 1,
            ..*position
        };
        let set = self.compile_wd(
            success_object_wd(&proof.set_well_defined, &proof.statement.set)?,
            &set_prior,
        )?;
        let formed = SourcePosition {
            before: 2,
            ..*position
        };
        let scope = SourcePosition::new(Some(&formed), SourceOwner::WitnessNonempty(proof), 0);
        let mut lines = Vec::new();
        for (index, (source, step)) in proof
            .statement
            .proof
            .iter()
            .zip(&proof.proof_steps)
            .enumerate()
        {
            validate_statement_capture(source, step)?;
            let prior = SourcePosition {
                before: index,
                ..scope
            };
            lines.push(self.compile_statement_in_scope(step, &prior, index + 1, true)?);
        }
        let complete = SourcePosition {
            before: proof.proof_steps.len(),
            ..scope
        };
        if !matches!(source_subject(&proof.membership_check)?, Fact::AtomicFact(AtomicFact::InFact(ref member))
            if member.element.ir() == proof.statement.obj.ir() && member.set.ir() == proof.statement.set.ir())
        {
            return Err(LeanCompileError::unsupported(
                "WitnessNonempty/MembershipSubject",
            ));
        }
        let (_, membership) = self.compile_verify(&proof.membership_check, &complete)?;
        lines.push(format!("exact ⟨Litex.denote {object}, {membership}⟩"));
        let published = SourcePosition {
            before: 3,
            ..*position
        };
        let fact = self.resolve_fact(proof.store_and_infer_result.primary_fact_id(), &published)?;
        if !matches!(&fact, Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir() == proof.statement.set.ir())
        {
            return Err(LeanCompileError::unsupported(
                "WitnessNonempty/StoredSubject",
            ));
        }
        self.compile_completed_fact_statement(
            &fact,
            (
                format!("Litex.IsNonempty {set}"),
                format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
            ),
            &proof.store_and_infer_result,
            &published,
            index,
            local,
        )
    }
}
