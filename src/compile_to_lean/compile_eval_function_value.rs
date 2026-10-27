use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    FunctionApplicationEvaluationResult, FunctionApplicationExpansionProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_eval_function_value(
        &self,
        application: &Obj,
        evaluations: &[FunctionApplicationEvaluationResult],
        remaining: &mut usize,
        aggregates: &[crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult],
        remaining_aggregates: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        let index = remaining
            .checked_sub(1)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/FunctionMissing"))?;
        let p = &evaluations[index];
        if !matches!(application, Obj::FnObj(call) if call.body.len() == 1 && (1..=2).contains(&call.body[0].len()))
        {
            return Err(LeanCompileError::unsupported("Eval/FunctionArity"));
        }
        if application.ir() != p.application.ir()
            || p.nested_function_evidence.end != index
            || p.nested_function_evidence.start > index
        {
            return Err(LeanCompileError::unsupported("Eval/FunctionOrder"));
        }
        *remaining = index;
        let prior = SourcePosition::new(
            Some(position),
            SourceOwner::EvalFunctions(evaluations),
            p.nested_function_evidence.start,
        );
        ensure_object(application, &p.application_well_defined)?;
        self.compile_wd(&p.application_well_defined, &prior)?;
        let formed = SourcePosition::new(
            Some(&prior),
            SourceOwner::WD(&p.application_well_defined),
            usize::MAX,
        );
        let beta = match &p.application_well_defined {
            ObjWellDefinedProof::ByDef { .. } => {
                self.compile_eval_function_beta(p, &p.application_well_defined, &formed)?
            }
            ObjWellDefinedProof::ByKnown { .. } => formed
                .with_visible_wd(application, &mut |wd, _| {
                    self.compile_eval_function_beta(p, wd, &formed)
                })?
                .ok_or_else(|| LeanCompileError::unsupported("Eval/FunctionProducer"))?,
        };
        let equalities = self.compile_eval_citations(&p.cited_equal_fact_ids, &formed)?;
        let mut cites = Vec::new();
        let rewrite = self.compile_eval_rewrite(
            p.expansion.expanded_body(),
            &p.rewritten_body,
            &equalities,
            &mut cites,
            &formed,
        )?;
        if cites != p.cited_equal_fact_ids {
            return Err(LeanCompileError::unsupported("Eval/FunctionCitations"));
        }
        // Child evaluation advances its own completion prefix. The outer call's
        // already checked WD stays available without freezing that child prefix.
        let body_position = SourcePosition::new(
            Some(position),
            SourceOwner::WD(&p.application_well_defined),
            usize::MAX,
        );
        let (value, evaluated, child_cites) = self.compile_eval_value(
            &p.rewritten_body,
            evaluations,
            remaining,
            aggregates,
            remaining_aggregates,
            &body_position,
        )?;
        if *remaining != p.nested_function_evidence.start
            || EvalRational::from_obj(&p.value).as_ref() != Some(&value)
        {
            return Err(LeanCompileError::unsupported("Eval/FunctionValue"));
        }
        cites.extend(child_cites);
        Ok((
            value,
            format!("(({beta}).trans (({rewrite}).trans {evaluated}))"),
            cites,
        ))
    }

    fn compile_eval_function_beta(
        &self,
        p: &FunctionApplicationEvaluationResult,
        constructor: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match &p.expansion {
            FunctionApplicationExpansionProof::Anonymous(expansion) => {
                let Obj::FnObj(call) = &p.application else {
                    return Err(LeanCompileError::unsupported("Eval/FunctionApplication"));
                };
                let head = match call.head.as_ref() {
                    FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
                    FnObjHead::AnonymousFnLiteral(f) => {
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
                    }
                    _ => return Err(LeanCompileError::unsupported("Eval/FunctionHead")),
                };
                let literal = expansion
                    .function_equal
                    .path
                    .last()
                    .map(|(_, to, _)| to)
                    .unwrap_or(&head);
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = literal else {
                    return Err(LeanCompileError::unsupported("Eval/FunctionBody"));
                };
                self.compile_checked_function_beta(
                    &p.application,
                    constructor,
                    function,
                    Some(&expansion.function_equal),
                    &expansion.expanded_body,
                    position,
                )
            }
            FunctionApplicationExpansionProof::CheckedBeta(pf) => self
                .compile_parent_checked_function_body(
                    &p.application,
                    constructor,
                    &pf.function_body,
                    &pf.expanded_body,
                    position,
                ),
        }
    }
}
