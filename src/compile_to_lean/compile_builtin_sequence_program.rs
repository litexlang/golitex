//! Replay the exact checked sequence program under a borrowed lexical owner.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, ExecReleaseThmStmtResult,
    TheoremDerivationProof,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

pub(super) fn program_parts(
    proof: &TheoremDerivationProof,
) -> Option<(
    BuiltinTheoremId,
    &[ExecStmtResult],
    &ExecStmtResult,
    &VerifyFactResult,
)> {
    use BuiltinTheoremId as I;
    use TheoremDerivationProof as D;
    let (id, real, extrema) = match proof {
        D::SequenceMonotoneBoundedAbove(p) => {
            (I::SequenceMonotoneBoundedAbove, Some(&p.completeness), None)
        }
        D::SequenceMonotoneBoundedBelow(p) => {
            (I::SequenceMonotoneBoundedBelow, Some(&p.completeness), None)
        }
        D::SequenceCauchyBounded(p) => (I::SequenceCauchyBounded, Some(&p.completeness), None),
        D::SequenceCauchyConvergent(p) => {
            (I::SequenceCauchyConvergent, Some(&p.completeness), None)
        }
        D::SequenceConvergentBounded(p) => {
            (I::SequenceConvergentBounded, Some(&p.completeness), None)
        }
        D::SequenceLimsupBounded(p) => {
            (I::SequenceLimsupBoundedExists, None, Some(&p.completeness))
        }
        D::SequenceLiminfBounded(p) => {
            (I::SequenceLiminfBoundedExists, None, Some(&p.completeness))
        }
        _ => return None,
    };
    if let Some(p) = real {
        Some((id, &p.derivation_steps, &p.application, &p.conclusion))
    } else {
        let p = extrema?;
        Some((id, &p.derivation_steps, &p.application, &p.conclusion))
    }
}
pub(super) fn program_identity(id: BuiltinTheoremId) -> bool {
    use BuiltinTheoremId::*;
    matches!(
        id,
        SequenceMonotoneBoundedAbove
            | SequenceMonotoneBoundedBelow
            | SequenceCauchyBounded
            | SequenceCauchyConvergent
            | SequenceConvergentBounded
            | SequenceLimsupBoundedExists
            | SequenceLiminfBoundedExists
    )
}
fn invalid(s: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceProgram/{s}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_sequence_program(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        let (id, steps, application, conclusion) =
            program_parts(derivation).ok_or_else(|| invalid("SelectedDerivation"))?;
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        use BuiltinTheoremId::*;
        let count = if matches!(
            id,
            SequenceMonotoneBoundedAbove
                | SequenceMonotoneBoundedBelow
                | SequenceLimsupBoundedExists
                | SequenceLiminfBoundedExists
        ) {
            3
        } else {
            2
        };
        if id != builtin.theorem
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || args != &builtin.arguments
            || args.len() != id.arity()
            || !matches!(&call.name, AtomicName::Plain{name} if name==id.as_str())
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
            || steps.is_empty()
            || source_subject(conclusion)? != builtin.conclusions[0]
        {
            return Err(invalid("OriginalStages"));
        }
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(applied),
        )) = application
        else {
            return Err(invalid("OriginalApplication"));
        };
        if applied.call.arguments != call.arguments
            || !matches!(
                applied.theorem_derivation,
                TheoremDerivationProof::UserTheorem
            )
            || !matches!(applied.callee, ResolvedTheoremCallee::UserTheorem(_))
        {
            return Err(invalid("ApplicationIdentity"));
        }
        let (definitions, _) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let completed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &completed)?;
        let scope = SourcePosition::new(Some(&completed), SourceOwner::Derivation(derivation), 0);
        let mut body = Vec::new();
        for (index, step) in steps.iter().enumerate() {
            body.push(self.compile_statement_in_scope(
                step,
                &SourcePosition {
                    before: index,
                    ..scope
                },
                index + 1,
                true,
            )?);
        }
        let end = SourcePosition {
            before: steps.len(),
            ..scope
        };
        body.push(self.compile_statement_in_scope(application, &end, steps.len() + 1, true)?);
        let applied_scope =
            SourcePosition::new(Some(&end), SourceOwner::Statement(application), usize::MAX);
        body.push(format!(
            "exact {}",
            self.compile_verify(conclusion, &applied_scope)?.1
        ));
        Ok((
            definitions,
            format!("(by\n  {}\n)", body.join("\n").replace('\n', "\n  ")),
            builtin.conclusions.clone(),
        ))
    }
}
