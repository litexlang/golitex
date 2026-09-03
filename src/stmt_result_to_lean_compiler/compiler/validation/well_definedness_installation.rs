//! Installation and intrinsic-store inspection for well-definedness results.

use super::super::*;

/// Consume the intrinsic stores inside one recursive fact-WD child while the
/// compiler already has the complete parent-owned WD tree active. This keeps
/// nested binder context available without manufacturing a duplicate child
/// statement certificate.
pub(in super::super) fn install_fact_well_definedness_proof_store_results_in_active_environment(
    result: &SuccessVerifyFactWellDefinedProofResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    match result {
        SuccessVerifyFactWellDefinedProofResult::AtomicFact(atomic) => {
            let mut visited = HashSet::new();
            for argument in &atomic.arguments {
                install_object_well_definedness_store_results_for_source(
                    &argument.source_object,
                    argument.result.as_ref(),
                    environment_stack,
                    &mut visited,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::AndFact(and) => {
            for conjunct in &and.conjuncts {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    conjunct,
                    environment_stack,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ChainFact(chain) => {
            for comparison in &chain.comparisons {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    comparison,
                    environment_stack,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::OrFact(or) => {
            for branch in &or.branches {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    branch,
                    environment_stack,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::NotForallFact(not_forall) => {
            install_fact_well_definedness_proof_store_results_in_active_environment(
                &not_forall.inner,
                environment_stack,
            )?;
        }
        // Binder bodies own a different lexical environment. Their stores are
        // installed only after the corresponding parameter aliases have been
        // introduced by the forall/existential compiler.
        SuccessVerifyFactWellDefinedProofResult::ExistFact(_)
        | SuccessVerifyFactWellDefinedProofResult::ForallFact(_)
        | SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(_) => {}
    }
    Ok(())
}

pub(in super::super) fn install_object_well_definedness_store_results(
    result: &SuccessVerifyObjWellDefinedResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let source_object = match result {
        SuccessVerifyObjWellDefinedResult::Direct(direct) => direct.object.clone(),
        SuccessVerifyObjWellDefinedResult::Reuse(reuse) => reuse.object.clone(),
    };
    install_object_well_definedness_store_results_for_source(
        &source_object,
        result,
        environment_stack,
        visited,
    )
}

pub(in super::super) fn install_object_well_definedness_store_results_for_source(
    source_object: &Obj,
    result: &SuccessVerifyObjWellDefinedResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let direct = direct_object_well_definedness_result(result)?;
    let result_address = direct as *const SuccessVerifyDirectObjWellDefinedResult as usize;
    if !visited.insert(result_address) {
        return Ok(());
    }
    if obj_equality_key(source_object) != obj_equality_key(&direct.object) {
        return Err(format!(
            "object WD store source changed `{source_object}` to `{}`",
            direct.object
        ));
    }
    for child in &direct.steps.children {
        install_object_well_definedness_store_results_for_source(
            &child.source_object,
            child.result.as_ref(),
            environment_stack,
            visited,
        )?;
    }
    if let Some(binder) = direct.steps.binder.as_deref() {
        install_object_binder_well_definedness_store_results(binder, environment_stack, visited)?;
    }
    for store in &direct.steps.stores {
        let result_set = direct.intrinsic_result_set.as_ref().ok_or_else(|| {
            format!(
                "object WD stored `{}` without an intrinsic result set",
                store.fact
            )
        })?;
        let expected: Fact = InFact::new(
            direct.object.clone(),
            result_set.clone(),
            store.fact.line_file(),
        )
        .into();
        if store.fact.to_string() != expected.to_string() {
            return Err(format!(
                "object WD store changed intrinsic membership `{expected}` to `{}`",
                store.fact
            ));
        }
        let fact_id = store.fact_id.ok_or_else(|| {
            format!("object WD intrinsic-result store `{expected}` has no FactId")
        })?;
        let matching_source_outputs = store
            .infers
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.fact_id == Some(fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string() == expected.to_string()
            })
            .count();
        if matching_source_outputs != 1 {
            return Err(format!(
                "object WD intrinsic-result store `{expected}` lost its exact source store output"
            ));
        }
        let rendered_object = render_obj(source_object, environment_stack)?;
        let rendered_set = render_obj(result_set, environment_stack)?;
        let proof = format!("Litex.In.own {rendered_set} {rendered_object}");
        if let Some(existing) = environment_stack.fact_propositions.get(&fact_id) {
            if existing.to_string() != expected.to_string()
                && !membership_facts_are_equal_up_to_nested_binder_alpha(existing, &expected)
            {
                return Err(format!(
                    "object WD FactId `{fact_id}` changed from `{existing}` to `{expected}`"
                ));
            }
        }
        environment_stack.fact_names.insert(fact_id, proof);
        environment_stack
            .fact_propositions
            .insert(fact_id, expected);
    }
    if let Some(instantiation) = direct.steps.template_instantiation.as_deref() {
        install_template_instantiation_result(&direct.object, instantiation, environment_stack)?;
    }
    Ok(())
}

pub(in super::super) fn install_binder_premise_well_definedness_store_results(
    premise: &SuccessVerifyBinderPremiseResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    install_fact_well_definedness_proof_store_results_in_active_environment(
        premise.well_definedness.proof.as_ref(),
        environment_stack,
    )?;
    Ok(())
}

pub(in super::super) fn install_child_object_well_definedness_store_results(
    child: &SuccessVerifyChildObjWellDefinedResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    install_object_well_definedness_store_results_for_source(
        &child.source_object,
        child.result.as_ref(),
        environment_stack,
        visited,
    )
}

pub(in super::super) fn install_iteration_scalar_return_well_definedness_store_results(
    result: &SuccessVerifyIterationScalarReturnResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    for child in &result.parameter_carriers {
        install_child_object_well_definedness_store_results(child, environment_stack, visited)?;
    }
    for premise in result.parameters.iter().chain(result.domains.iter()) {
        install_binder_premise_well_definedness_store_results(premise, environment_stack)?;
    }
    install_child_object_well_definedness_store_results(
        &result.return_carrier,
        environment_stack,
        visited,
    )
}

pub(in super::super) fn install_iteration_interval_well_definedness_store_results(
    result: &SuccessVerifyIterationIntervalResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    for child in &result.parameter_carriers {
        install_child_object_well_definedness_store_results(child, environment_stack, visited)?;
    }
    for premise in &result.parameters {
        install_binder_premise_well_definedness_store_results(premise, environment_stack)?;
    }
    install_child_object_well_definedness_store_results(
        &result.return_carrier,
        environment_stack,
        visited,
    )?;
    // An interval body is checked under the iteration parameter. Its
    // intrinsic stores are binder-local (and, for the current exact Sum
    // lowering, are replayed through the retained anonymous-function WD
    // context). Installing them in the surrounding scope would either render
    // an unbound symbol or publish a FactId outside its lexical owner.
    Ok(())
}

pub(in super::super) fn install_object_binder_well_definedness_store_results(
    binder: &SuccessVerifyBinderObjectWellDefinedResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    match binder {
        SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => {
            install_child_object_well_definedness_store_results(
                &result.parameter_carrier,
                environment_stack,
                visited,
            )?;
            install_binder_premise_well_definedness_store_results(
                &result.parameter,
                environment_stack,
            )?;
            for condition in &result.conditions {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    condition.well_definedness.proof.as_ref(),
                    environment_stack,
                )?;
            }
        }
        SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => {
            for child in &result.parameter_carriers {
                install_child_object_well_definedness_store_results(
                    child,
                    environment_stack,
                    visited,
                )?;
            }
            for premise in result.parameters.iter().chain(result.domains.iter()) {
                install_binder_premise_well_definedness_store_results(premise, environment_stack)?;
            }
            install_child_object_well_definedness_store_results(
                &result.return_carrier,
                environment_stack,
                visited,
            )?;
        }
        SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => {
            for child in &result.parameter_carriers {
                install_child_object_well_definedness_store_results(
                    child,
                    environment_stack,
                    visited,
                )?;
            }
            for premise in result.parameters.iter().chain(result.domains.iter()) {
                install_binder_premise_well_definedness_store_results(premise, environment_stack)?;
            }
            install_child_object_well_definedness_store_results(
                &result.return_carrier,
                environment_stack,
                visited,
            )?;
            // `result.body` may cite the anonymous parameter. Its intrinsic
            // stores are installed by
            // `compile_anonymous_function_well_definedness_context` after the
            // exact binder aliases exist; publishing them here would leak a
            // binder-local FactId into the surrounding scope.
        }
        SuccessVerifyBinderObjectWellDefinedResult::Iteration(result) => {
            if let Some(scalar_return) = result.scalar_return.as_deref() {
                install_iteration_scalar_return_well_definedness_store_results(
                    scalar_return,
                    environment_stack,
                    visited,
                )?;
            }
            install_iteration_interval_well_definedness_store_results(
                result.interval.as_ref(),
                environment_stack,
                visited,
            )?;
        }
        SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result) => {
            if let Some(scalar_return) = result.scalar_return.as_deref() {
                install_iteration_scalar_return_well_definedness_store_results(
                    scalar_return,
                    environment_stack,
                    visited,
                )?;
            }
            match &result.mode {
                SuccessVerifyFiniteAggregateModeResult::Elements(elements) => {
                    for application in &elements.applications {
                        install_child_object_well_definedness_store_results(
                            application,
                            environment_stack,
                            visited,
                        )?;
                    }
                }
                SuccessVerifyFiniteAggregateModeResult::ClosedRange(range) => {
                    install_child_object_well_definedness_store_results(
                        &range.aggregate_dependency,
                        environment_stack,
                        visited,
                    )?;
                }
                SuccessVerifyFiniteAggregateModeResult::Empty(_)
                | SuccessVerifyFiniteAggregateModeResult::Symbolic(_) => {}
            }
        }
        SuccessVerifyBinderObjectWellDefinedResult::Reduce(result) => {
            if let Some(laws) = result.operation_laws.as_deref() {
                install_child_object_well_definedness_store_results(
                    &laws.parameter_carrier,
                    environment_stack,
                    visited,
                )?;
                for premise in &laws.parameters {
                    install_binder_premise_well_definedness_store_results(
                        premise,
                        environment_stack,
                    )?;
                }
            }
            match &result.mode {
                SuccessVerifyReduceModeResult::Interval(interval) => {
                    install_iteration_interval_well_definedness_store_results(
                        interval.interval.as_ref(),
                        environment_stack,
                        visited,
                    )?;
                }
                SuccessVerifyReduceModeResult::Elements(elements) => {
                    for application in &elements.applications {
                        install_child_object_well_definedness_store_results(
                            application,
                            environment_stack,
                            visited,
                        )?;
                    }
                }
                SuccessVerifyReduceModeResult::Empty(_)
                | SuccessVerifyReduceModeResult::Symbolic(_) => {}
            }
        }
        SuccessVerifyBinderObjectWellDefinedResult::Structure(result) => {
            for field in &result.fields {
                install_child_object_well_definedness_store_results(
                    &field.carrier,
                    environment_stack,
                    visited,
                )?;
                install_binder_premise_well_definedness_store_results(
                    &field.premise,
                    environment_stack,
                )?;
            }
            for equivalent in &result.equivalent_facts {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    equivalent.well_definedness.proof.as_ref(),
                    environment_stack,
                )?;
            }
        }
    }
    Ok(())
}
