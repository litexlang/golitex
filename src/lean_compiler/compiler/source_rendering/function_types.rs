//! Telescope requirements and function-set type rendering.

use super::super::*;

pub(in super::super) fn render_telescope_signature(
    function: &LeanTargetFunctionTypeRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    validate_function_type(function)?;
    let mut nested = context.clone();
    let mut prefixes = Vec::with_capacity(function.parameters.len() + 1);
    for (index, parameter) in function.parameters.iter().enumerate() {
        let domain = render_lean_source_for_target_set_representation(&parameter.set, &nested)?;
        let alpha = format!("__alpha{}", index + 1);
        let argument = format!("__arg{}", index + 1);
        let membership = format!("__arg{}_in", index + 1);
        prefixes.push(format!(
            "(Litex.FnTelescope.parameter {domain} (fun {{{alpha} : Type}} ({argument} : {alpha}) ({membership} : Litex.In {argument} {domain}) => "
        ));
        nested.symbol_names.insert(parameter.symbol_id, argument);
        if let Some(real) =
            membership_real_value(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested.numeric_real_values.insert(parameter.symbol_id, real);
        }
        if let Some(integer) =
            membership_integer_value(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested
                .numeric_integer_values
                .insert(parameter.symbol_id, integer);
        }
        if let Some(rational) =
            membership_rational_value(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested
                .numeric_rational_values
                .insert(parameter.symbol_id, rational);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) =
            membership_numeric_proof(&parameter.set, &format!("__arg{}", index + 1), &membership)
        {
            nested
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
    }
    if !function.domain_facts.is_empty() {
        let requirements = function
            .domain_facts
            .iter()
            .map(|fact| render_telescope_domain_requirement(function, fact, &nested))
            .collect::<Result<Vec<_>, _>>()?;
        prefixes.push(format!(
            "(Litex.FnTelescope.requirement ({}) (fun __domain => ",
            conjunction(&requirements)
        ));
    }
    let codomain =
        render_lean_source_for_target_set_representation(function.return_set.as_ref(), &nested)?;
    let universe = if matches!(
        function.return_set.as_ref(),
        LeanTargetObjectRepresentation::FunctionSet { .. }
    ) {
        1
    } else {
        0
    };
    let signature = format!(
        "{}(Litex.FnTelescope.done {codomain}){}",
        prefixes.concat(),
        "))".repeat(prefixes.len())
    );
    Ok(format!("({signature} : Litex.FnTelescope.{{{universe}}})"))
}

/// A bounded `N+` source parameter is heterogeneous in Lean. Its source
/// domain fact still compares the original Litex argument, so the telescope
/// requirement retains that comparison through an existential complex
/// observation instead of silently comparing a chosen carrier value.
pub(in super::super) fn render_telescope_domain_requirement(
    function: &LeanTargetFunctionTypeRepresentation,
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Some((parameter_symbol_id, natural_bound)) =
        positive_natural_parameter_less_equal_natural_bound(function, fact)?
    {
        let parameter_name = context
            .symbol_names
            .get(&parameter_symbol_id)
            .ok_or_else(|| "bounded positive-natural parameter has no compiler name".to_string())?;
        return Ok(format!(
            "Litex.positiveNaturalParameterLessEqualNaturalBound {parameter_name} {natural_bound}"
        ));
    }
    render_fact(fact, context)
}

pub(in super::super) fn positive_natural_parameter_less_equal_natural_bound(
    function: &LeanTargetFunctionTypeRepresentation,
    fact: &Fact,
) -> Result<Option<(SymbolId, String)>, String> {
    let Fact::AtomicFact(AtomicFact::LessEqualFact(comparison)) = fact else {
        return Ok(None);
    };
    let Some(parameter) = function.parameters.iter().find(|parameter| {
        parameter.set
            == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural)
            && object_is_symbol(&comparison.left, parameter.symbol_id)
    }) else {
        return Ok(None);
    };
    let lowered_bound = LeanTargetObjectRepresentation::lower(&comparison.right)?;
    let natural_bound = render_natural_endpoint(&lowered_bound)?;
    Ok(Some((parameter.symbol_id, natural_bound)))
}

pub(in super::super) fn render_function_requirement(
    function: &LeanTargetFunctionTypeRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function.domain_facts.is_empty() {
        return Err("total function has no source-domain requirement".into());
    }
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(function.parameters[0].symbol_id, "__arg".into());
    let requirements = function
        .domain_facts
        .iter()
        .map(|fact| render_fact(fact, &nested))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!(
        "(fun {{__alpha}} (__arg : __alpha) => {})",
        conjunction(&requirements)
    ))
}

pub(in super::super) fn render_function_type(
    function: &LeanTargetFunctionTypeRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function_uses_telescope(function) {
        return Ok(format!(
            "Litex.FnTelescope.Carrier {}",
            render_telescope_signature(function, context)?
        ));
    }
    validate_unary_function_type(function)?;
    let domain =
        render_lean_source_for_target_set_representation(&function.parameters[0].set, context)?;
    let codomain =
        render_lean_source_for_target_set_representation(function.return_set.as_ref(), context)?;
    if function.domain_facts.is_empty() {
        Ok(format!("Litex.Fn {domain} {codomain}"))
    } else {
        Ok(format!(
            "Litex.FnWhere {domain} {codomain} {}",
            render_function_requirement(function, context)?
        ))
    }
}

pub(in super::super) fn render_function_set(
    function: &LeanTargetFunctionTypeRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function_uses_telescope(function) {
        return Ok(format!(
            "(Litex.fnTelescopeSet {})",
            render_telescope_signature(function, context)?
        ));
    }
    validate_unary_function_type(function)?;
    let render_base_set = |set: &LeanTargetObjectRepresentation| -> Result<String, String> {
        let rendered = render_lean_source_for_target_set_representation(set, context)?;
        if matches!(set, LeanTargetObjectRepresentation::Symbol { .. }) {
            Ok(format!("({rendered} : Litex.Set.{{0}})"))
        } else {
            Ok(rendered)
        }
    };
    let domain = render_base_set(&function.parameters[0].set)?;
    let codomain = match function.return_set.as_ref() {
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            render_nested_function_set(function, context)?
        }
        return_set => render_base_set(return_set)?,
    };
    if function.domain_facts.is_empty() {
        Ok(format!("(Litex.fnSet {domain} {codomain})"))
    } else {
        Ok(format!(
            "(Litex.fnSetWhere {domain} {codomain} {})",
            render_function_requirement(function, context)?
        ))
    }
}

pub(in super::super) fn render_nested_function_set(
    function: &LeanTargetFunctionTypeRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if function_uses_telescope(function) {
        return Ok(format!(
            "(Litex.fnTelescopeSet {})",
            render_telescope_signature(function, context)?
        ));
    }
    validate_unary_function_type(function)?;
    let render_base_set = |set: &LeanTargetObjectRepresentation| -> Result<String, String> {
        let rendered = render_lean_source_for_target_set_representation(set, context)?;
        if matches!(set, LeanTargetObjectRepresentation::Symbol { .. }) {
            Ok(format!("({rendered} : Litex.Set.{{0}})"))
        } else {
            Ok(rendered)
        }
    };
    let domain = render_base_set(&function.parameters[0].set)?;
    let codomain = match function.return_set.as_ref() {
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            render_nested_function_set(function, context)?
        }
        return_set => render_base_set(return_set)?,
    };
    if function.domain_facts.is_empty() {
        Ok(format!("(Litex.fnSet {domain} {codomain})"))
    } else {
        Ok(format!(
            "(Litex.fnSetWhere {domain} {codomain} {})",
            render_function_requirement(function, context)?
        ))
    }
}
