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
        if !p.matrix_scalar_evaluations.is_empty() || !p.algo_evaluations.is_empty() {
            return Err(LeanCompileError::unsupported("Eval/EvaluationFamily"));
        }
        ensure_object(&p.source_object, &p.source_well_defined)?;
        self.compile_wd(&p.source_well_defined, position)?;
        let source_complete = SourcePosition {
            before: 1,
            ..*position
        };
        let body_citation_count = p
            .function_evaluations
            .iter()
            .map(|f| f.cited_equal_fact_ids.len())
            .sum::<usize>();
        let initial_count = p
            .cited_equal_fact_ids
            .len()
            .checked_sub(body_citation_count)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/CitationCount"))?;
        let source_ids = &p.cited_equal_fact_ids[..initial_count];
        let equalities = self.compile_eval_citations(source_ids, position)?;
        let mut used = Vec::new();
        let rewritten = self.compile_eval_rewrite(
            &p.source_object,
            &p.rewritten_object,
            &equalities,
            &mut used,
            &source_complete,
        )?;
        if used != source_ids {
            return Err(LeanCompileError::unsupported("Eval/CitationOrder"));
        }
        let mut remaining = p.function_evaluations.len();
        let mut remaining_aggregates = p.aggregate_evaluations.len();
        let (value, calculation, body_cites) = self.compile_eval_value(
            &p.rewritten_object,
            &p.function_evaluations,
            &mut remaining,
            &p.aggregate_evaluations,
            &mut remaining_aggregates,
            &source_complete,
        )?;
        used.extend(body_cites);
        if remaining != 0 || remaining_aggregates != 0 || used != p.cited_equal_fact_ids {
            return Err(LeanCompileError::unsupported("Eval/EvaluationOrder"));
        }
        let (output, output_value) =
            self.compile_eval_closed_value(&p.evaluated_object, &source_complete)?;
        if value != output {
            return Err(LeanCompileError::unsupported("Eval/Value"));
        }
        let evaluated = SourcePosition {
            before: 2,
            ..*position
        };
        let wd = &p.evaluated_equal_well_defined;
        let bindings = self.compile_equal_wd_locals(&p.evaluated_equal_fact, wd, &evaluated)?;
        let formed = SourcePosition::new(Some(&evaluated), SourceOwner::EqualWDLocals(wd, 2), 2);
        let left = self.compile_object_reference(&p.source_object, &formed)?;
        let right = self.compile_object_reference(&p.evaluated_object, &formed)?;
        let ty = format!("Litex.Same {left} {right}");
        let input_value = self.compile_calculation_endpoint(
            &p.source_object,
            &value,
            format!("({rewritten}).trans {calculation}"),
            &formed,
        )?;
        let output_value =
            self.compile_calculation_endpoint(&p.evaluated_object, &output, output_value, &formed)?;
        let proof = format!("(show {ty} from ({input_value}).trans ({output_value}).symm)");
        let compiled = (
            Self::scope_equal_wd(ty.clone(), &bindings),
            Self::scope_equal_wd_proof(ty, proof, &bindings),
        );
        let completed = SourcePosition {
            before: 4,
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

    pub(super) fn compile_eval_citations(
        &self,
        ids: &[FactId],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<(FactId, EqualFact)>, LeanCompileError> {
        let mut equalities = Vec::new();
        for (index, id) in ids.iter().enumerate() {
            if ids[..index].contains(id) {
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
        Ok(equalities)
    }

    /// The rewrite endpoint is a semantic value, not a new WD object. Only
    /// exact original citation endpoints or owned arithmetic congruence apply.
    pub(super) fn compile_eval_rewrite(
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
        if let Some((id, equality)) = hits.first() {
            if crate::rational_expression::ClosedNumericExpr::try_from_obj(target).is_none() {
                return Err(LeanCompileError::unsupported("Eval/NonNumericReplacement"));
            }
            if !used.contains(id) {
                used.push(*id);
            }
            let (original_source, original_target) = if equality.left.ir() == source.ir() {
                (&equality.left, &equality.right)
            } else {
                (&equality.right, &equality.left)
            };
            let cited =
                self.compile_registered_equality(*id, original_source, original_target, position)?;
            if original_target == target {
                return Ok(cited);
            }
            // Numeric rewriting may canonicalize unary negatives into signed
            // numeral leaves. Cite the exact stored endpoint, then justify the
            // changed representation with its original numeric observation.
            let original = self.compile_numeric_observation(original_target, position)?;
            let (value, target_value) = self.compile_eval_closed_value(target, position)?;
            if original.3.as_ref() != Some(&value) {
                return Err(LeanCompileError::unsupported("Eval/ReplacementValue"));
            }
            let literal = exact_rational_literal(&value, "ℂ")?;
            return Ok(format!("(Eq.trans {cited} (Eq.trans (({}).trans (congrArg M.number (by norm_num : {} = {literal}))) (Eq.symm {target_value})))", original.1, original.0));
        }
        if let (Obj::FnObj(a), Obj::FnObj(b)) = (source, target) {
            if a.head != b.head
                || a.body.len() != 1
                || b.body.len() != 1
                || a.body[0].len() != b.body[0].len()
                || !(1..=2).contains(&a.body[0].len())
            {
                return Err(LeanCompileError::unsupported("Eval/RewriteCall"));
            }
            let head = match a.head.as_ref() {
                FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
                FnObjHead::AnonymousFnLiteral(f) => {
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
                }
                _ => return Err(LeanCompileError::unsupported("Eval/RewriteCallHead")),
            };
            let function = self.compile_normalization_value(&head, position)?;
            let proofs = a.body[0]
                .iter()
                .zip(&b.body[0])
                .map(|(x, y)| self.compile_eval_rewrite(x, y, equalities, used, position))
                .collect::<Result<Vec<_>, _>>()?;
            let argument = match proofs.as_slice() {
                [p] => p.clone(),
                [p,q] => format!("(congrArg₂ (fun x y => Litex.FiniteFunction.tupleValue (M := M) ![x,y]) {p} {q})"),
                _ => unreachable!(),
            };
            return Ok(format!(
                "(congrArg (Litex.FunctionSemantics.callValue (M := M) {function}) {argument})"
            ));
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
