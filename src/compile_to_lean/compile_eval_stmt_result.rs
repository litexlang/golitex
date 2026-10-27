use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_command_statement(
        &self,
        result: &ExecCommandStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p)) => {
                self.compile_eval_statement(p, position, index, local)
            }
            ExecCommandStmtResult::Eval(ExecEvalStmtResult::Failed(_)) => {
                Err(LeanCompileError::unsupported("Eval/Failed"))
            }
        }
    }

    fn compile_eval_statement(
        &self,
        p: &ExecEvalStmtSuccess,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if p.statement.obj_to_eval.ir() != p.source_object.ir()
            || p.evaluated_equal_fact.left.ir() != p.source_object.ir()
            || p.evaluated_equal_fact.right.ir() != p.evaluated_object.ir()
        {
            return Err(LeanCompileError::unsupported("Eval/Endpoints"));
        }
        if !p.matrix_scalar_evaluations.is_empty()
            || !p.aggregate_evaluations.is_empty()
            || !p.function_evaluations.is_empty()
            || !p.algo_evaluations.is_empty()
        {
            return Err(LeanCompileError::unsupported("Eval/EvaluationFamily"));
        }
        ensure_object(&p.source_object, &p.source_well_defined)?;
        self.compile_wd(&p.source_well_defined, position)?;
        let source_complete = SourcePosition {
            before: 1,
            ..*position
        };
        let mut equalities = Vec::new();
        for (index, id) in p.cited_equal_fact_ids.iter().enumerate() {
            if p.cited_equal_fact_ids[..index].contains(id) {
                return Err(LeanCompileError::unsupported("Eval/CitationOrder"));
            }
            let resolved = self.resolve_fact(*id, position)?;
            let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &resolved else {
                return Err(LeanCompileError::unsupported("Eval/CitationFamily"));
            };
            if eq.fact_id != *id || *self.cited_fact_reference(*id, position)?.0 != resolved {
                return Err(LeanCompileError::unsupported("Eval/CitationSubject"));
            }
            equalities.push((*id, eq.clone()));
        }
        let mut used = Vec::new();
        let rewritten = self.compile_eval_rewrite(
            &p.source_object,
            &p.rewritten_object,
            &equalities,
            &mut used,
            &source_complete,
        )?;
        if used != p.cited_equal_fact_ids {
            return Err(LeanCompileError::unsupported("Eval/CitationOrder"));
        }
        let (value, calculation) =
            self.compile_eval_closed_value(&p.rewritten_object, &source_complete)?;
        let (output, output_value) =
            self.compile_eval_closed_value(&p.evaluated_object, &source_complete)?;
        if value != output {
            return Err(LeanCompileError::unsupported("Eval/Value"));
        }
        let wd = &p.evaluated_equal_well_defined;
        let bindings =
            self.compile_equal_wd_locals(&p.evaluated_equal_fact, wd, &source_complete)?;
        let formed =
            SourcePosition::new(Some(&source_complete), SourceOwner::EqualWDLocals(wd, 2), 2);
        let left = self.compile_object_reference(&p.source_object, &formed)?;
        let right = self.compile_object_reference(&p.evaluated_object, &formed)?;
        let ty = format!("Litex.Same {left} {right}");
        let proof = format!(
            "(show {ty} from ({rewritten}).trans (({calculation}).trans ({output_value}).symm))"
        );
        let compiled = (
            Self::scope_equal_wd(ty.clone(), &bindings),
            Self::scope_equal_wd_proof(ty, proof, &bindings),
        );
        let completed = SourcePosition {
            before: 3,
            ..*position
        };
        self.compile_completed_fact_statement(
            &p.evaluated_equal_fact.clone().into(),
            compiled,
            &p.store_and_infer_result,
            &completed,
            index,
            local,
        )
    }

    /// The rewrite endpoint is a semantic value, not a new WD object. Only
    /// exact original citation endpoints or owned arithmetic congruence apply.
    fn compile_eval_rewrite(
        &self,
        source: &Obj,
        target: &Obj,
        equalities: &[(FactId, EqualFact)],
        used: &mut Vec<FactId>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let raw = self.compile_normalization_value(source, position)?;
        if source.ir() == target.ir() {
            return Ok(format!("(Eq.refl {raw})"));
        }
        let hits: Vec<_> = equalities
            .iter()
            .filter(|(_, f)| {
                (f.left.ir() == source.ir() && f.right.ir() == target.ir())
                    || (f.right.ir() == source.ir() && f.left.ir() == target.ir())
            })
            .collect();
        if hits.len() > 1 {
            return Err(LeanCompileError::unsupported("Eval/AmbiguousRewrite"));
        }
        if let Some((id, _)) = hits.first() {
            if crate::rational_expression::ClosedNumericExpr::try_from_obj(target).is_none() {
                return Err(LeanCompileError::unsupported("Eval/NonNumericReplacement"));
            }
            if !used.contains(id) {
                used.push(*id);
            }
            return self.compile_registered_equality(*id, source, target, position);
        }
        let (op, children) = arithmetic_constructor_pairs(source, target)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/RewriteSubject"))?;
        let proofs = children
            .into_iter()
            .map(|(a, b)| self.compile_eval_rewrite(a, b, equalities, used, position))
            .collect::<Result<Vec<_>, _>>()?;
        let op = arithmetic_operation_term(op);
        match proofs.as_slice() {
            [p] => Ok(format!("(congrArg {op} {p})")),
            [p, q] => Ok(format!("(congrArg₂ {op} {p} {q})")),
            _ => Err(LeanCompileError::unsupported("Eval/RewriteArity")),
        }
    }
}

pub(super) fn eval_statement(statement: &ExecStmtResult) -> Option<&ExecEvalStmtSuccess> {
    match statement {
        ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) => {
            Some(p)
        }
        _ => None,
    }
}

pub(super) fn in_closed_eval(position: &SourcePosition<'_>) -> bool {
    let mut cursor = Some(position);
    while let Some(p) = cursor {
        if let SourceOwner::Statement(s) = p.owner {
            if let Some(e) = eval_statement(s) {
                return crate::rational_expression::ClosedNumericExpr::try_from_obj(
                    &e.source_object,
                )
                .is_some();
            }
        }
        cursor = p.parent;
    }
    false
}
