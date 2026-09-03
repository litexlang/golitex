//! Fact well-definedness context collection and citations.

use super::super::*;

pub(in super::super) fn validate_success_obj_well_defined_result(
    result: &SuccessVerifyObjWellDefinedResult,
    expected_object: &Obj,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    if let SuccessVerifyObjWellDefinedResult::Reuse(reuse) = result {
        if obj_equality_key(&reuse.object) != obj_equality_key(expected_object) {
            return Err("reused object WD result changed its checked object".into());
        }
    }
    let direct = direct_object_well_definedness_result(result)?;
    let result_address = direct as *const SuccessVerifyDirectObjWellDefinedResult as usize;
    if !visited.insert(result_address) {
        return Ok(());
    }
    if obj_equality_key(&direct.object) != obj_equality_key(expected_object) {
        return Err("object WD result changed its checked object".into());
    }
    if let Some(binder) = &direct.steps.binder {
        validate_success_obj_binder_well_defined_result(binder, expected_object, visited)?;
    }
    for child in &direct.steps.children {
        validate_success_obj_well_defined_result(
            child.result.as_ref(),
            &child.source_object,
            visited,
        )?;
    }
    for check in &direct.steps.fact_checks {
        if check.expected_proposition.to_string() != check.verification.fact().to_string() {
            return Err("object WD fact check changed its verified proposition".into());
        }
    }
    for requirement in &direct.steps.target_requirements {
        if requirement.expected_proposition.to_string()
            != requirement.verification.fact().to_string()
        {
            return Err("object WD target requirement changed its proposition".into());
        }
    }
    Ok(())
}

pub(in super::super) fn collect_well_definedness_to_lean_context_from_fact_result(
    result: &SuccessVerifyFactWellDefinedProofResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    match result {
        SuccessVerifyFactWellDefinedProofResult::AtomicFact(result) => {
            for argument in &result.arguments {
                let mut visited = HashSet::new();
                collect_well_definedness_to_lean_context_from_object_result(
                    &argument.source_object,
                    &argument.result,
                    context,
                    &mut visited,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::AndFact(result) => {
            for child in &result.conjuncts {
                collect_well_definedness_to_lean_context_from_fact_result(child, context)?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ChainFact(result) => {
            for child in &result.comparisons {
                collect_well_definedness_to_lean_context_from_fact_result(child, context)?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::OrFact(result) => {
            for child in &result.branches {
                collect_well_definedness_to_lean_context_from_fact_result(child, context)?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ExistFact(result) => {
            collect_well_definedness_to_lean_context_from_fact_binder(&result.binder, context)?;
            for child in &result.body {
                collect_well_definedness_to_lean_context_from_fact_result(
                    &child.well_definedness,
                    context,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ForallFact(result) => {
            collect_well_definedness_to_lean_context_from_fact_binder(&result.binder, context)?;
            for child in result.premises.iter().chain(result.conclusions.iter()) {
                collect_well_definedness_to_lean_context_from_fact_result(
                    &child.well_definedness,
                    context,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(result) => {
            collect_well_definedness_to_lean_context_from_fact_result(&result.forward, context)?;
            collect_well_definedness_to_lean_context_from_fact_result(&result.reverse, context)?;
        }
        SuccessVerifyFactWellDefinedProofResult::NotForallFact(result) => {
            collect_well_definedness_to_lean_context_from_fact_result(&result.inner, context)?;
        }
    }
    Ok(())
}

pub(in super::super) fn success_verify_fact_result_is_deferred_plain_citation(
    verification: &SuccessFactProofNode,
) -> bool {
    match verification.proof() {
        SuccessFactProofResult::StoredFactCitation(_) => true,
        SuccessFactProofResult::Reuse(reuse) => {
            success_verify_fact_result_is_deferred_plain_citation(reuse.source.as_ref())
        }
        _ => false,
    }
}

pub(in super::super) fn render_deferred_plain_fact_result_citation(
    verification: &SuccessFactProofNode,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match verification.proof() {
        SuccessFactProofResult::StoredFactCitation(citation)
            if success_verify_fact_result_is_deferred_plain_citation(verification) =>
        {
            let source = citation.source_fact.clone();
            if source.to_string() != verification.fact().to_string() {
                return Err("deferred WD citation changed its target proposition".into());
            }
            resolve_fact_citation(&citation.source_fact_id, &source, context)
        }
        SuccessFactProofResult::Reuse(reuse) => {
            render_deferred_plain_fact_result_citation(reuse.source.as_ref(), context)
        }
        _ => Err("WD requirement is not a deferred plain FactId citation".into()),
    }
}

pub(in super::super) fn render_function_application_requirement_proof(
    requirement: &StmtResultFunctionApplicationRequirementToLeanCompilationContext,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match &requirement.proof_expression {
        Some(proof_expression) => Ok(proof_expression.clone()),
        None => match render_deferred_plain_fact_result_citation(
            requirement.verification.as_ref(),
            context,
        ) {
            Ok(proof_expression) => Ok(proof_expression),
            Err(_) => {
                // This is a lexical recursive read of the canonical Result,
                // not a second lowering IR. No top-level declarations may be
                // created while constructing a local requirement proof.
                let mut nested_compiler = StmtResultToLeanCompiler::new("nested WD Result");
                nested_compiler.environment_stack = context.clone();
                let proof_expression = nested_compiler
                    .construct_lean_proof_from_shared_verify_fact_result(
                        requirement.verification.as_ref(),
                    )?
                    .ok_or_else(|| {
                        "nested WD requirement Result has no direct Lean proof constructor"
                            .to_string()
                    })?;
                if !nested_compiler.declarations.is_empty() {
                    return Err(
                        "nested WD requirement attempted to emit a top-level Lean declaration"
                            .into(),
                    );
                }
                Ok(proof_expression)
            }
        },
    }
}

pub(in super::super) fn collect_well_definedness_to_lean_context_from_fact_binder(
    binder: &SuccessVerifyFactBinderResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    for group in &binder.parameter_groups {
        if let Some(carrier) = &group.carrier {
            let mut visited = HashSet::new();
            collect_well_definedness_to_lean_context_from_object_result(
                &carrier.source_object,
                &carrier.result,
                context,
                &mut visited,
            )?;
        }
        for premise in &group.parameters {
            collect_well_definedness_parameter_fact_alias(premise, context)?;
            collect_well_definedness_to_lean_context_from_fact_result(
                premise.well_definedness.proof.as_ref(),
                context,
            )?;
        }
    }
    Ok(())
}

pub(in super::super) fn collect_well_definedness_parameter_fact_alias(
    premise: &SuccessVerifyBinderPremiseResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Some(symbol_id) = premise.symbol_id else {
        return Ok(());
    };
    let fact_id = fact_id_for_well_definedness_binder_premise(premise)?;
    if !context.parameter_fact_aliases.iter().any(|alias| {
        alias.symbol_id == symbol_id
            && alias.fact_id == fact_id
            && alias.proposition.to_string() == premise.proposition.to_string()
    }) {
        context
            .parameter_fact_aliases
            .push(StmtResultWellDefinednessParameterFactAlias {
                symbol_id,
                fact_id,
                proposition: premise.proposition.clone(),
            });
    }
    Ok(())
}

pub(in super::super) fn fact_id_for_well_definedness_binder_premise(
    premise: &SuccessVerifyBinderPremiseResult,
) -> Result<FactId, String> {
    premise
        .infers
        .store_fact_outputs
        .iter()
        .find(|output| {
            output.itself_and_why_itself_is_stored.0.to_string() == premise.proposition.to_string()
        })
        .and_then(|output| output.fact_id)
        .ok_or_else(|| {
            format!(
                "binder premise `{}` has no frozen ordinary FactId",
                premise.proposition
            )
        })
}
