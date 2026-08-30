//! Object, binder, iteration, child, target, and evaluation result validation.

use super::super::*;

pub(in super::super) fn validate_success_obj_binder_well_defined_result(
    binder: &SuccessVerifyBinderObjectWellDefinedResult,
    owner: &Obj,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    match (binder, owner) {
        (SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result), Obj::SetBuilder(_)) => {
            validate_success_obj_well_defined_child(&result.parameter_carrier, visited)?;
        }
        (SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result), Obj::FnSet(_)) => {
            validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
            validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result),
            Obj::AnonymousFn(_),
        ) => {
            validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
            validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
            validate_success_obj_well_defined_child(&result.body, visited)?;
            validate_success_obj_target_requirement(&result.body_membership)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(result),
            Obj::Sum(_) | Obj::Product(_),
        ) => {
            if let Some(scalar_return) = &result.scalar_return {
                validate_success_iteration_scalar_return_result(scalar_return, visited)?;
            }
            validate_success_iteration_interval_result(&result.interval, visited)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result),
            Obj::SumOfFiniteSet(_) | Obj::ProductOfFiniteSet(_),
        ) => {
            if let Some(scalar_return) = &result.scalar_return {
                validate_success_iteration_scalar_return_result(scalar_return, visited)?;
            }
            match &result.mode {
                SuccessVerifyFiniteAggregateModeResult::Empty(result) => {
                    validate_success_obj_fact_check(&result.empty_set)?;
                }
                SuccessVerifyFiniteAggregateModeResult::Elements(result) => {
                    for membership in &result.body_memberships {
                        validate_success_obj_fact_check(membership)?;
                    }
                    validate_success_obj_well_defined_children(&result.applications, visited)?;
                }
                SuccessVerifyFiniteAggregateModeResult::ClosedRange(result) => {
                    validate_success_obj_well_defined_child(&result.aggregate_dependency, visited)?;
                }
                SuccessVerifyFiniteAggregateModeResult::Symbolic(_) => {}
            }
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(result),
            Obj::Reduce(_) | Obj::FiniteSetReduce(_),
        ) => {
            validate_success_obj_fact_check(&result.seed_membership)?;
            if let Some(laws) = &result.operation_laws {
                validate_success_obj_well_defined_child(&laws.parameter_carrier, visited)?;
                validate_success_obj_fact_check(&laws.associativity)?;
                validate_success_obj_fact_check(&laws.commutativity)?;
            }
            match &result.mode {
                SuccessVerifyReduceModeResult::Empty(result) => {
                    validate_success_obj_fact_check(&result.empty_range_or_set)?;
                }
                SuccessVerifyReduceModeResult::Interval(result) => {
                    validate_success_iteration_interval_result(&result.interval, visited)?;
                }
                SuccessVerifyReduceModeResult::Elements(result) => {
                    for membership in &result.body_memberships {
                        validate_success_obj_fact_check(membership)?;
                    }
                    validate_success_obj_well_defined_children(&result.applications, visited)?;
                }
                SuccessVerifyReduceModeResult::Symbolic(result) => {
                    if let SuccessVerifyFiniteReduceDomainCoverageResult::Subset(result) =
                        &result.coverage
                    {
                        validate_success_obj_fact_check(&result.subset)?;
                    }
                }
            }
        }
        (SuccessVerifyBinderObjectWellDefinedResult::Structure(result), Obj::StructObj(_)) => {
            for argument in &result.header_arguments {
                validate_success_obj_fact_check(&argument.verification)?;
            }
            for domain in &result.header_domains {
                validate_success_obj_fact_check(domain)?;
            }
            for field in &result.fields {
                validate_success_obj_well_defined_child(&field.carrier, visited)?;
            }
        }
        _ => {
            return Err(format!(
                "object `{owner}` retained a well-definedness binder owned by another constructor"
            ));
        }
    }
    Ok(())
}

pub(in super::super) fn validate_success_iteration_scalar_return_result(
    result: &SuccessVerifyIterationScalarReturnResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
    validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
    validate_success_obj_fact_check(&result.return_subset)
}

pub(in super::super) fn validate_success_iteration_interval_result(
    result: &SuccessVerifyIterationIntervalResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
    validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
    if let Some(body) = &result.body {
        validate_success_obj_well_defined_child(body, visited)?;
    }
    if let Some(body_membership) = &result.body_membership {
        validate_success_obj_target_requirement(body_membership)?;
    }
    match &result.coverage {
        SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(_) => {}
        SuccessVerifyIterationCoverageResult::Enumerated(result) => {
            for check in &result.checks {
                validate_success_obj_fact_check(check)?;
            }
        }
        SuccessVerifyIterationCoverageResult::Endpoint(result) => {
            validate_success_obj_fact_check(&result.check)?;
        }
        SuccessVerifyIterationCoverageResult::IntervalSubset(result) => {
            validate_success_obj_fact_check(&result.check)?;
        }
    }
    Ok(())
}

pub(in super::super) fn validate_success_obj_well_defined_children(
    children: &[SuccessVerifyChildObjWellDefinedResult],
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    for child in children {
        validate_success_obj_well_defined_child(child, visited)?;
    }
    Ok(())
}

pub(in super::super) fn validate_success_obj_well_defined_child(
    child: &SuccessVerifyChildObjWellDefinedResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_result(child.result.as_ref(), &child.source_object, visited)
}

pub(in super::super) fn validate_success_obj_fact_check(
    check: &SuccessVerifyFactForObjWellDefinedResult,
) -> Result<(), String> {
    if check.expected_proposition.to_string() != check.verification.fact().to_string() {
        return Err("binder WD fact check changed its verified proposition".into());
    }
    Ok(())
}

pub(in super::super) fn validate_success_obj_target_requirement(
    requirement: &SuccessVerifyObjTargetRequirementResult,
) -> Result<(), String> {
    if requirement.expected_proposition.to_string() != requirement.verification.fact().to_string() {
        return Err("binder WD target requirement changed its verified proposition".into());
    }
    Ok(())
}

pub(in super::super) fn validate_success_evaluate_obj_result(
    result: &SuccessEvaluateObjResult,
) -> Result<(), String> {
    let recomputed = result
        .expression
        .evaluate_to_normalized_decimal_number_with_result()
        .ok_or_else(|| "closed numeric evaluation expression no longer evaluates".to_string())?;
    compare_success_evaluate_obj_results(result, &recomputed)
}

pub(in super::super) fn compare_success_evaluate_obj_results(
    retained: &SuccessEvaluateObjResult,
    recomputed: &SuccessEvaluateObjResult,
) -> Result<(), String> {
    if obj_equality_key(&retained.expression) != obj_equality_key(&recomputed.expression)
        || retained.value.normalized_value != recomputed.value.normalized_value
    {
        return Err("closed numeric evaluation changed its expression or value".into());
    }
    match (&retained.step, &recomputed.step) {
        (
            SuccessEvaluateObjStepResult::Literal(retained),
            SuccessEvaluateObjStepResult::Literal(recomputed),
        ) if retained.literal.normalized_value == recomputed.literal.normalized_value => Ok(()),
        (
            SuccessEvaluateObjStepResult::Unary(retained),
            SuccessEvaluateObjStepResult::Unary(recomputed),
        ) if retained.operator == recomputed.operator => {
            compare_success_evaluate_obj_results(&retained.argument, &recomputed.argument)
        }
        (
            SuccessEvaluateObjStepResult::Binary(retained),
            SuccessEvaluateObjStepResult::Binary(recomputed),
        ) if retained.operator == recomputed.operator => {
            compare_success_evaluate_obj_results(&retained.left, &recomputed.left)?;
            compare_success_evaluate_obj_results(&retained.right, &recomputed.right)
        }
        (
            SuccessEvaluateObjStepResult::Shape(retained),
            SuccessEvaluateObjStepResult::Shape(recomputed),
        ) if retained.operator == recomputed.operator
            && retained.inputs.len() == recomputed.inputs.len()
            && retained.evaluated_children.len() == recomputed.evaluated_children.len() =>
        {
            for (retained_input, recomputed_input) in
                retained.inputs.iter().zip(recomputed.inputs.iter())
            {
                if obj_equality_key(retained_input) != obj_equality_key(recomputed_input) {
                    return Err("closed numeric shape evaluation changed an input".into());
                }
            }
            for (retained_child, recomputed_child) in retained
                .evaluated_children
                .iter()
                .zip(recomputed.evaluated_children.iter())
            {
                compare_success_evaluate_obj_results(retained_child, recomputed_child)?;
            }
            Ok(())
        }
        _ => Err("closed numeric evaluation changed its recursive operation tree".into()),
    }
}
