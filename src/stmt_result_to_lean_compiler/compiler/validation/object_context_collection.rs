//! Object, binder, iteration, and function-application well-definedness contexts.

use super::super::*;

pub(in super::super) fn direct_object_well_definedness_result(
    result: &SuccessVerifyObjWellDefinedResult,
) -> Result<&SuccessVerifyDirectObjWellDefinedResult, String> {
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(result) => Ok(result),
        SuccessVerifyObjWellDefinedResult::Reuse(result) => Ok(result.source.as_ref()),
    }
}

pub(in super::super) fn collect_well_definedness_to_lean_context_from_object_result(
    source_object: &Obj,
    result: &Rc<SuccessVerifyObjWellDefinedResult>,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let result_address = Rc::as_ptr(result) as usize;
    if !visited.insert(result_address) {
        if matches!(source_object, Obj::FnObj(_)) {
            collect_function_application_well_definedness_to_lean_context(
                source_object,
                direct_object_well_definedness_result(result.as_ref())?,
                context,
            )?;
        }
        return Ok(());
    }
    let direct = direct_object_well_definedness_result(result.as_ref())?;
    if obj_equality_key(source_object) != obj_equality_key(&direct.object) {
        return Err(format!(
            "object WD Result changed `{source_object}` to `{}`",
            direct.object
        ));
    }
    if matches!(source_object, Obj::FnObj(_)) {
        collect_function_application_well_definedness_to_lean_context(
            source_object,
            direct,
            context,
        )?;
    }
    for child in &direct.steps.children {
        collect_well_definedness_to_lean_context_from_object_result(
            &child.source_object,
            &child.result,
            context,
            visited,
        )?;
    }
    if let Some(binder) = &direct.steps.binder {
        collect_well_definedness_to_lean_context_from_object_binder(
            source_object,
            direct,
            binder,
            context,
            visited,
        )?;
    }
    Ok(())
}

pub(in super::super) fn collect_well_definedness_to_lean_context_from_object_child(
    child: &SuccessVerifyChildObjWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    collect_well_definedness_to_lean_context_from_object_result(
        &child.source_object,
        &child.result,
        context,
        visited,
    )
}

pub(in super::super) fn collect_well_definedness_to_lean_context_from_object_binder(
    owner_object: &Obj,
    owner_result: &SuccessVerifyDirectObjWellDefinedResult,
    binder: &SuccessVerifyBinderObjectWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    match binder {
        SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => {
            collect_well_definedness_to_lean_context_from_object_child(
                &result.parameter_carrier,
                context,
                visited,
            )?;
            collect_well_definedness_to_lean_context_from_binder_premises(
                std::slice::from_ref(&result.parameter),
                context,
            )?;
            for condition in &result.conditions {
                collect_well_definedness_to_lean_context_from_fact_result(
                    condition.well_definedness.proof.as_ref(),
                    context,
                )?;
            }
        }
        SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => {
            for child in &result.parameter_carriers {
                collect_well_definedness_to_lean_context_from_object_child(
                    child, context, visited,
                )?;
            }
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.parameters,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.domains,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_object_child(
                &result.return_carrier,
                context,
                visited,
            )?;
        }
        SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => {
            for child in &result.parameter_carriers {
                collect_well_definedness_to_lean_context_from_object_child(
                    child, context, visited,
                )?;
            }
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.parameters,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.domains,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_object_child(
                &result.return_carrier,
                context,
                visited,
            )?;
            collect_well_definedness_to_lean_context_from_object_child(
                &result.body,
                context,
                visited,
            )?;
            collect_anonymous_function_well_definedness_to_lean_context(
                owner_object,
                result,
                context,
            )?;
        }
        SuccessVerifyBinderObjectWellDefinedResult::Iteration(result) => {
            collect_iteration_well_definedness_to_lean_context(
                owner_object,
                owner_result,
                result,
                context,
            )?;
        }
        // These constructor-specific binders already publish every object
        // dependency through `steps.children`; they do not introduce
        // parameter aliases consumed by the current Lean surface.
        SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(_)
        | SuccessVerifyBinderObjectWellDefinedResult::Reduce(_)
        | SuccessVerifyBinderObjectWellDefinedResult::Structure(_) => {}
    }
    Ok(())
}

pub(in super::super) fn collect_iteration_well_definedness_to_lean_context(
    owner_object: &Obj,
    owner_result: &SuccessVerifyDirectObjWellDefinedResult,
    result: &SuccessVerifyIterationWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Obj::Sum(sum) = owner_object else {
        return Ok(());
    };
    let occurrence_id = sum
        .source_occurrence_id
        .ok_or_else(|| "sum WD Result has no parser-owned source occurrence id".to_string())?;
    if !matches!(&owner_result.object, Obj::Sum(_)) {
        return Err("sum Iteration WD Result changed its owner object".into());
    }
    if obj_equality_key(owner_object) != obj_equality_key(&owner_result.object) {
        return Err("sum Iteration WD Result changed its owner semantic key".into());
    }
    let interval = result.interval.as_ref();
    let return_carrier = interval.return_carrier.source_object.clone();
    let retained = StmtResultIterationWellDefinednessToLeanCompilationContext {
        source_aggregate: owner_object.clone(),
        operation: result.operation.clone(),
        parameter_set: interval.parameter_set.clone(),
        return_carrier,
        parameter_count: interval.parameters.len(),
        domain_count: interval.domains.len(),
        has_body: interval.body.is_some(),
        has_body_membership: interval.body_membership.is_some(),
        has_exact_integer_coverage: matches!(
            interval.coverage,
            SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(_)
                | SuccessVerifyIterationCoverageResult::Enumerated(_)
        ),
    };
    if let Some(previous) = context.iterations.insert(occurrence_id, retained) {
        if obj_equality_key(&previous.source_aggregate) != obj_equality_key(owner_object) {
            return Err(format!(
                "sum occurrence {} selected two different Iteration WD Results",
                occurrence_id.value()
            ));
        }
    }
    Ok(())
}

pub(in super::super) fn iteration_has_reviewed_integer_callable_contract(
    iteration: &StmtResultIterationWellDefinednessToLeanCompilationContext,
) -> bool {
    let Obj::Sum(sum) = &iteration.source_aggregate else {
        return false;
    };
    match sum.func.as_ref() {
        Obj::AnonymousFn(_) => iteration.has_body && iteration.has_body_membership,
        // A named callable has no interval-local body in the verifier Result.
        // Its exact unary Z-to-Z contract is instead selected by the stored
        // function-membership FactId when the target renderer lowers it.
        Obj::Atom(atom) if atom.symbol_ref().is_some() => {
            !iteration.has_body && !iteration.has_body_membership
        }
        _ => false,
    }
}

pub(in super::super) fn collect_well_definedness_to_lean_context_from_binder_premises(
    premises: &[SuccessVerifyBinderPremiseResult],
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    for premise in premises {
        collect_well_definedness_parameter_fact_alias(premise, context)?;
        collect_well_definedness_to_lean_context_from_fact_result(
            premise.well_definedness.proof.as_ref(),
            context,
        )?;
    }
    Ok(())
}

pub(in super::super) fn well_definedness_binder_premise_to_lean_compilation_context(
    premise: &SuccessVerifyBinderPremiseResult,
) -> Result<StmtResultWellDefinednessBinderPremiseToLeanCompilationContext, String> {
    Ok(
        StmtResultWellDefinednessBinderPremiseToLeanCompilationContext {
            role: premise.role,
            symbol_id: premise.symbol_id,
            fact_id: fact_id_for_well_definedness_binder_premise(premise)?,
            proposition: premise.proposition.clone(),
        },
    )
}

pub(in super::super) fn collect_anonymous_function_well_definedness_to_lean_context(
    owner_object: &Obj,
    result: &SuccessVerifyAnonymousFunctionWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Obj::AnonymousFn(source_function) = owner_object else {
        return Err("anonymous-function WD binder changed its owner object".into());
    };
    let occurrence_id = source_function.source_occurrence_id.ok_or_else(|| {
        "anonymous function WD Result has no parser-owned occurrence id".to_string()
    })?;
    let parameters = result
        .parameters
        .iter()
        .map(well_definedness_binder_premise_to_lean_compilation_context)
        .collect::<Result<Vec<_>, _>>()?;
    let domains = result
        .domains
        .iter()
        .map(well_definedness_binder_premise_to_lean_compilation_context)
        .collect::<Result<Vec<_>, _>>()?;
    let mut assumption_infers = SuccessInferResult::new();
    for premise in result.parameters.iter().chain(result.domains.iter()) {
        assumption_infers.new_infer_result_inside(premise.infers.clone());
    }
    context.anonymous_functions.insert(
        occurrence_id,
        StmtResultAnonymousFunctionWellDefinednessToLeanCompilationContext {
            source_function: owner_object.clone(),
            body_source_object: result.body.source_object.clone(),
            body_well_definedness: result.body.result.clone(),
            parameters,
            domains,
            assumption_infers,
            compiled_inference_fact_proof_steps: Vec::new(),
            closure: StmtResultAnonymousFunctionClosureToLeanCompilationContext {
                role: result.body_membership.role,
                expected_proposition: result.body_membership.expected_proposition.clone(),
                verification: result.body_membership.verification.clone(),
                proof_expression: None,
            },
        },
    );
    Ok(())
}

pub(in super::super) fn collect_function_application_well_definedness_to_lean_context(
    source_object: &Obj,
    root: &SuccessVerifyDirectObjWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Obj::FnObj(source_application) = source_object else {
        return Ok(());
    };
    let Some(occurrence_id) = source_application.source_occurrence_id else {
        // Multi-layer WD Results contain synthetic prefix nodes such as
        // `g(a)` underneath the one parser-owned `g(a)(b)` occurrence. The
        // outer Result collects every layer from its FunctionPrefix edges;
        // the synthetic child therefore has no independent context key.
        return Ok(());
    };
    let layer_count = source_application.body.len();
    if layer_count == 0 {
        return Err("function application retained no argument layers".into());
    }
    let mut layer_results = vec![None; layer_count];
    let mut current = root;
    for layer_index in (0..layer_count).rev() {
        let source_prefix: Obj = source_application.prefix_obj(layer_index + 1);
        if obj_equality_key(&current.object) != obj_equality_key(&source_prefix) {
            return Err(format!(
                "function application layer {layer_index} changed its Result-owned source prefix"
            ));
        }
        layer_results[layer_index] = Some(current);
        if layer_index == 0 {
            continue;
        }
        let prefix_children = current
            .steps
            .children
            .iter()
            .filter(|child| {
                child.role
                    == (WellDefinedObjChildRole::FunctionPrefix {
                        through_layer_index: layer_index - 1,
                    })
            })
            .collect::<Vec<_>>();
        let [prefix_child] = prefix_children.as_slice() else {
            return Err(format!(
                "function application layer {layer_index} requires one exact FunctionPrefix child Result"
            ));
        };
        current = direct_object_well_definedness_result(prefix_child.result.as_ref())?;
    }
    let first_layer = layer_results[0].expect("every application layer was retained");
    let anonymous_function_head = first_layer
        .steps
        .children
        .iter()
        .find(|child| child.role == WellDefinedObjChildRole::FunctionHead)
        .map(|child| child.source_object.clone());
    let layers = layer_results
        .into_iter()
        .map(|layer| {
            let layer = layer.expect("every application layer was retained");
            StmtResultFunctionApplicationLayerWellDefinednessToLeanCompilationContext {
                source_prefix: layer.object.clone(),
                function_contracts: layer.function_contracts.clone(),
                intrinsic_result_set: layer.intrinsic_result_set.clone(),
                requirements: layer
                    .steps
                    .target_requirements
                    .iter()
                    .map(|requirement| {
                        StmtResultFunctionApplicationRequirementToLeanCompilationContext {
                            role: requirement.role,
                            expected_proposition: requirement.expected_proposition.clone(),
                            verification: requirement.verification.clone(),
                            proof_expression: None,
                        }
                    })
                    .collect(),
            }
        })
        .collect();
    let application_context =
        StmtResultFunctionApplicationWellDefinednessToLeanCompilationContext {
            source_application: source_object.clone(),
            function_contracts: root.function_contracts.clone(),
            anonymous_function_head,
            layers,
        };
    if let Some(previous) = context
        .function_applications
        .insert(occurrence_id, application_context)
    {
        if obj_equality_key(&previous.source_application) != obj_equality_key(source_object) {
            return Err(format!(
                "function application occurrence {} was reused for another source object",
                occurrence_id.value()
            ));
        }
    }
    Ok(())
}
