use super::*;

pub(super) fn render_fact(
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match fact {
        Fact::AtomicFact(atomic) => match atomic {
            AtomicFact::NormalAtomicFact(fact) => {
                let source_name = fact.predicate.to_string();
                if source_name == PRIME && fact.body.len() == 1 {
                    return Ok(format!(
                        "Litex.Prime {}",
                        render_obj(&fact.body[0], context)?
                    ));
                }
                if source_name == COPRIME && fact.body.len() == 2 {
                    return Ok(format!(
                        "Litex.Coprime {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                let binding = context
                    .predicate_bindings
                    .get(&source_name)
                    .ok_or_else(|| format!("unavailable concrete predicate `{source_name}`"))?;
                if fact.body.len() != binding.parameter_count {
                    return Err(format!(
                        "predicate `{source_name}` expected {} arguments, retained {}",
                        binding.parameter_count,
                        fact.body.len()
                    ));
                }
                let arguments = fact
                    .body
                    .iter()
                    .map(|argument| render_obj(argument, context))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("{} {}", binding.lean_name, arguments.join(" ")))
            }
            AtomicFact::NotNormalAtomicFact(fact) => {
                let source_name = fact.predicate.to_string();
                if source_name == PRIME && fact.body.len() == 1 {
                    return Ok(format!(
                        "¬ Litex.Prime {}",
                        render_obj(&fact.body[0], context)?
                    ));
                }
                if source_name == COPRIME && fact.body.len() == 2 {
                    return Ok(format!(
                        "¬ Litex.Coprime {} {}",
                        render_obj(&fact.body[0], context)?,
                        render_obj(&fact.body[1], context)?
                    ));
                }
                let binding = context
                    .predicate_bindings
                    .get(&source_name)
                    .ok_or_else(|| format!("unavailable concrete predicate `{source_name}`"))?;
                if fact.body.len() != binding.parameter_count {
                    return Err(format!(
                        "predicate `{source_name}` expected {} arguments, retained {}",
                        binding.parameter_count,
                        fact.body.len()
                    ));
                }
                let arguments = fact
                    .body
                    .iter()
                    .map(|argument| render_obj(argument, context))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("¬ {} {}", binding.lean_name, arguments.join(" ")))
            }
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                render_obj(&fact.element, context)?,
                render_obj(&fact.set, context)?
            )),
            AtomicFact::NotInFact(fact) => Ok(format!(
                "¬ Litex.In {} {}",
                render_obj(&fact.element, context)?,
                render_obj(&fact.set, context)?
            )),
            AtomicFact::SubsetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::SupersetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                render_obj(&fact.right, context)?,
                render_obj(&fact.left, context)?
            )),
            AtomicFact::NotSubsetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::NotSupersetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                render_obj(&fact.right, context)?,
                render_obj(&fact.left, context)?
            )),
            AtomicFact::EqualFact(fact) => Ok(format!(
                "Litex.Same {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::NotEqualFact(fact) => Ok(format!(
                "¬ Litex.Same {} {}",
                render_obj(&fact.left, context)?,
                render_obj(&fact.right, context)?
            )),
            AtomicFact::LessFact(fact) => render_order_fact(&fact.left, &fact.right, true, context),
            AtomicFact::GreaterFact(fact) => {
                render_order_fact(&fact.right, &fact.left, true, context)
            }
            AtomicFact::LessEqualFact(fact) => {
                render_order_fact(&fact.left, &fact.right, false, context)
            }
            AtomicFact::GreaterEqualFact(fact) => {
                render_order_fact(&fact.right, &fact.left, false, context)
            }
            AtomicFact::NotLessFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.left, &fact.right, true, context)?
            )),
            AtomicFact::NotGreaterFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.right, &fact.left, true, context)?
            )),
            AtomicFact::NotLessEqualFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.left, &fact.right, false, context)?
            )),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(format!(
                "¬ {}",
                render_order_fact(&fact.right, &fact.left, false, context)?
            )),
            AtomicFact::IsNonemptySetFact(fact) => Ok(format!(
                "Litex.Set.Nonempty {}",
                render_obj(&fact.set, context)?
            )),
            AtomicFact::IsFiniteSetFact(fact) => Ok(format!(
                "Litex.Set.Finite {}",
                render_obj(&fact.set, context)?
            )),
            // A Litex set parameter is represented as a Lean value whose type
            // is already `Litex.Set`; its explicit source-level sethood check
            // therefore lowers to the proposition `True`.
            AtomicFact::IsSetFact(_) => Ok("True".to_string()),
            AtomicFact::NotIsSetFact(_) => Ok("¬ True".to_string()),
            AtomicFact::IsTupleFact(fact) => {
                Ok(format!("Litex.IsTuple {}", render_obj(&fact.set, context)?))
            }
            _ => Err(format!("unsupported compiler atomic fact `{fact}`")),
        },
        Fact::AndFact(_) | Fact::ChainFact(_) => {
            let components = conjunction_components(fact)?;
            let rendered = components
                .iter()
                .map(|component| render_fact(component, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(conjunction(&rendered))
        }
        Fact::OrFact(_) => {
            let branches = disjunction_components(fact)?;
            let rendered = branches
                .iter()
                .map(|branch| render_fact(branch, context))
                .collect::<Result<Vec<_>, _>>()?;
            if rendered.is_empty() {
                return Err("compiler disjunction retained no branches".into());
            }
            Ok(rendered.join(" ∨ "))
        }
        Fact::ExistFact(existential) => render_existential_fact(existential, context),
        Fact::ForallFact(forall) => render_forall_fact_type(forall, context),
        _ => Err(format!("unsupported compiler fact `{fact}`")),
    }
}

pub(super) fn render_order_fact(
    left: &Obj,
    right: &Obj,
    strict: bool,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if left.to_string() == "0" {
        let predicate = if strict {
            "Litex.Positive"
        } else {
            "Litex.Nonnegative"
        };
        return Ok(format!("{predicate} {}", render_obj(right, context)?));
    }
    if right.to_string() == "0" {
        let predicate = if strict {
            "Litex.Negative"
        } else {
            "Litex.Nonpositive"
        };
        return Ok(format!("{predicate} {}", render_obj(left, context)?));
    }
    let predicate = if strict { "Litex.Lt" } else { "Litex.Le" };
    Ok(format!(
        "{predicate} {} {}",
        render_numeric_obj(left, context)?,
        render_numeric_obj(right, context)?
    ))
}

pub(super) fn render_numeric_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    // Bound identifiers are not all stored as the same `Atom` constructor.
    // Lowering supplies their canonical SymbolId, which is the identity used
    // by the compiler environment regardless of the source atom shape.
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(obj)
    {
        if let Some(representation) = context.numeric_representations.get(&symbol_id) {
            return Ok(representation.clone());
        }
    }
    if let Obj::Atom(atom) = obj {
        if let Some(representation) = atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_representations.get(&symbol.id()))
        {
            return Ok(representation.clone());
        }
    }
    match obj {
        Obj::Add(operation) => Ok(format!(
            "({} + {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        Obj::Sub(operation) => Ok(format!(
            "({} - {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        Obj::Mul(operation) => Ok(format!(
            "({} * {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        Obj::Div(operation) => Ok(format!(
            "({} / {})",
            render_numeric_obj(operation.left.as_ref(), context)?,
            render_numeric_obj(operation.right.as_ref(), context)?
        )),
        _ => render_obj(obj, context),
    }
}

pub(super) fn install_structured_induction_shape_symbol(
    symbol_id: SymbolId,
    rendered: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) {
    let rendered = rendered.to_string();
    context.symbol_names.insert(symbol_id, rendered.clone());
    context
        .numeric_representations
        .insert(symbol_id, rendered.clone());
    context
        .numeric_integer_values
        .insert(symbol_id, rendered.clone());
    context
        .numeric_rational_values
        .insert(symbol_id, rendered.clone());
    context.numeric_real_values.insert(symbol_id, rendered);
}

pub(super) fn install_structured_induction_native_integer_symbol(
    symbol_id: SymbolId,
    native_integer: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) {
    let complex = format!("((({native_integer}) : ℂ))");
    context.symbol_names.insert(symbol_id, complex.clone());
    context.numeric_representations.insert(symbol_id, complex);
    context
        .numeric_integer_values
        .insert(symbol_id, native_integer.to_string());
    context
        .numeric_rational_values
        .insert(symbol_id, format!("((({native_integer}) : ℚ))"));
    context
        .numeric_real_values
        .insert(symbol_id, format!("((({native_integer}) : ℝ))"));
}

pub(super) fn fact_matches_structured_induction_goal_substitution(
    source: &Fact,
    target: &Fact,
    parameter_symbol_id: SymbolId,
    replacement: &Obj,
) -> bool {
    let argument_pairs = match (source, target) {
        (Fact::AtomicFact(source), Fact::AtomicFact(target)) => {
            Runtime::_verify_atomic_fact_the_same_type_and_return_matched_args(source, target)
        }
        (Fact::AndFact(source), Fact::AndFact(target)) => {
            Runtime::_verify_and_fact_the_same_type_and_return_matched_args(source, target)
        }
        (Fact::ChainFact(source), Fact::ChainFact(target)) => {
            Runtime::_verify_chain_fact_the_same_type_and_return_matched_args(source, target)
        }
        _ => return false,
    };
    let Some(argument_pairs) = argument_pairs.ok().flatten() else {
        return false;
    };
    argument_pairs.iter().all(|(source, target)| {
        object_matches_structured_induction_substitution(
            source,
            target,
            parameter_symbol_id,
            replacement,
        )
    })
}

pub(super) fn object_matches_structured_induction_substitution(
    source: &Obj,
    target: &Obj,
    parameter_symbol_id: SymbolId,
    replacement: &Obj,
) -> bool {
    if object_is_symbol(source, parameter_symbol_id) {
        return objects_align_by_nested_rational_normalization_for_result_compiler(
            replacement,
            target,
        );
    }
    if obj_equality_key(source) == obj_equality_key(target) {
        return true;
    }
    let comparison: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
        source,
        target,
        &mut |source_argument, target_argument| {
            Ok(object_matches_structured_induction_substitution(
                source_argument,
                target_argument,
                parameter_symbol_id,
                replacement,
            ))
        },
    );
    comparison.unwrap_or(false)
}

/// Render one source object in the exact integer view selected by visible
/// membership evidence. `%` is an integer-only source constructor; silently
/// applying a made-up Complex remainder operation would change its semantics.
pub(super) fn render_integer_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(obj)
    {
        if let Some(integer) = context.numeric_integer_values.get(&symbol_id) {
            return Ok(integer.clone());
        }
    }
    if let Obj::Atom(atom) = obj {
        if let Some(integer) = atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_integer_values.get(&symbol.id()))
        {
            return Ok(integer.clone());
        }
    }
    match obj {
        Obj::Number(number) if number.normalized_value.parse::<i128>().is_ok() => {
            Ok(format!("({} : ℤ)", number.normalized_value))
        }
        Obj::Add(operation) => Ok(format!(
            "({} + {})",
            render_integer_obj(operation.left.as_ref(), context)?,
            render_integer_obj(operation.right.as_ref(), context)?
        )),
        Obj::Sub(operation) => Ok(format!(
            "({} - {})",
            render_integer_obj(operation.left.as_ref(), context)?,
            render_integer_obj(operation.right.as_ref(), context)?
        )),
        Obj::Mul(operation) => Ok(format!(
            "({} * {})",
            render_integer_obj(operation.left.as_ref(), context)?,
            render_integer_obj(operation.right.as_ref(), context)?
        )),
        Obj::Mod(operation) => Ok(format!(
            "({} % {})",
            render_integer_obj(operation.left.as_ref(), context)?,
            render_integer_obj(operation.right.as_ref(), context)?
        )),
        _ => Err(format!(
            "integer-only compiler operator has no exact visible integer representation for `{obj}`"
        )),
    }
}

/// Render a source object in the exact rational view selected by visible
/// membership evidence. The rational-power verifier independently retains the
/// integer exponent premise; this helper never guesses a coercion from the
/// ordinary Complex observation.
pub(super) fn render_rational_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(obj)
    {
        if let Some(rational) = context.numeric_rational_values.get(&symbol_id) {
            return Ok(rational.clone());
        }
    }
    if let Obj::Atom(atom) = obj {
        if let Some(rational) = atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_rational_values.get(&symbol.id()))
        {
            return Ok(rational.clone());
        }
    }
    match obj {
        Obj::Number(number) if number.normalized_value.parse::<i128>().is_ok() => {
            Ok(format!("({} : ℚ)", number.normalized_value))
        }
        Obj::Add(operation) => Ok(format!(
            "({} + {})",
            render_rational_obj(operation.left.as_ref(), context)?,
            render_rational_obj(operation.right.as_ref(), context)?
        )),
        Obj::Sub(operation) => Ok(format!(
            "({} - {})",
            render_rational_obj(operation.left.as_ref(), context)?,
            render_rational_obj(operation.right.as_ref(), context)?
        )),
        Obj::Mul(operation) => Ok(format!(
            "({} * {})",
            render_rational_obj(operation.left.as_ref(), context)?,
            render_rational_obj(operation.right.as_ref(), context)?
        )),
        Obj::Div(operation) => Ok(format!(
            "({} / {})",
            render_rational_obj(operation.left.as_ref(), context)?,
            render_rational_obj(operation.right.as_ref(), context)?
        )),
        Obj::Pow(operation) => Ok(format!(
            "({} ^ {})",
            render_rational_obj(operation.base.as_ref(), context)?,
            render_integer_obj(operation.exponent.as_ref(), context)?
        )),
        _ => Err(format!(
            "rational-only compiler operator has no exact visible rational representation for `{obj}`"
        )),
    }
}

pub(super) fn render_existential_fact(
    existential: &ExistFactEnum,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let name = lean_identifier(group.params[0].name());
    render_existential_fact_with_names(existential, context, &name, &format!("__carrier_{name}"))
}

pub(super) fn render_existential_fact_with_names(
    existential: &ExistFactEnum,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    witness_name: &str,
    carrier_name: &str,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let set = parameter_set(&group.param_type)?;
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(group.params[0].id(), witness_name.to_string());
    nested
        .existential_names
        .insert(group.params[0].name().to_string(), witness_name.to_string());
    let requirement = format!("Litex.In {witness_name} {}", render_obj(set, &nested)?);
    let body = render_fact(&existential.facts()[0].from_ref_to_cloned_fact(), &nested)?;
    let binders = match set {
        Obj::FnSet(_) => format!("({carrier_name} : Type 1) ({witness_name} : {carrier_name})"),
        set if set_requires_heterogeneous_carrier(set) => {
            format!("({carrier_name} : Type) ({witness_name} : {carrier_name})")
        }
        _ => format!("({witness_name} : ℂ)"),
    };
    Ok(format!("∃ {binders}, {requirement} ∧ {body}"))
}

pub(super) fn one_witness_existential_group(
    existential: &ExistFactEnum,
) -> Result<&TypedParameterGroup, String> {
    if !existential.is_plain_exist()
        || existential.typed_parameters().number_of_params() != 1
        || existential.facts().len() != 1
    {
        return Err(
            "compiler existential facts support one positive witness and one body fact".into(),
        );
    }
    let group = &existential.typed_parameters().groups[0];
    if group.params.len() != 1 {
        return Err("compiler existential fact requires one singleton parameter group".into());
    }
    parameter_set(&group.param_type)?;
    Ok(group)
}

pub(super) fn one_witness_existentials_are_alpha_equal(
    source: &Fact,
    target: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    let (Fact::ExistFact(source), Fact::ExistFact(target)) = (source, target) else {
        return Ok(false);
    };
    Ok(
        render_existential_fact_with_names(source, context, "__bound", "__bound_carrier")?
            == render_existential_fact_with_names(target, context, "__bound", "__bound_carrier")?,
    )
}

pub(super) fn render_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match obj {
        Obj::Atom(AtomObj::Bound(parameter)) => context
            .symbol_names
            .get(&parameter.symbol.id())
            .cloned()
            .or_else(|| context.existential_names.get(parameter.name()).cloned())
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(AtomObj::Identifier(identifier)) => identifier
            .symbol
            .as_ref()
            .and_then(|symbol| context.symbol_names.get(&symbol.id()))
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Atom(atom) => atom
            .symbol_ref()
            .and_then(|symbol| context.symbol_names.get(&symbol.id()))
            .cloned()
            .ok_or_else(|| format!("unbound compiler symbol `{obj}`")),
        Obj::Number(number) => render_normalized_complex_number(&number.normalized_value),
        Obj::ImaginaryUnit(_) => Ok("Complex.I".into()),
        Obj::EulerNumber(_) => Ok("((Real.exp 1 : ℝ) : ℂ)".into()),
        Obj::Pi(_) => Ok("((Real.pi : ℝ) : ℂ)".into()),
        Obj::Add(addition) => Ok(format!(
            "({} + {})",
            render_numeric_obj(addition.left.as_ref(), context)?,
            render_numeric_obj(addition.right.as_ref(), context)?
        )),
        Obj::Sub(subtraction) => Ok(format!(
            "({} - {})",
            render_numeric_obj(subtraction.left.as_ref(), context)?,
            render_numeric_obj(subtraction.right.as_ref(), context)?
        )),
        Obj::Mul(multiplication) => Ok(format!(
            "({} * {})",
            render_numeric_obj(multiplication.left.as_ref(), context)?,
            render_numeric_obj(multiplication.right.as_ref(), context)?
        )),
        Obj::Div(division) => Ok(format!(
            "({} / {})",
            render_numeric_obj(division.left.as_ref(), context)?,
            render_numeric_obj(division.right.as_ref(), context)?
        )),
        Obj::Mod(remainder) => Ok(format!(
            "(({} % {} : ℤ) : ℂ)",
            render_integer_obj(remainder.left.as_ref(), context)?,
            render_integer_obj(remainder.right.as_ref(), context)?
        )),
        Obj::Pow(power) => render_numeric_power(power, context),
        Obj::FnSet(function_set) => {
            let function = LeanTargetFunctionTypeRepresentation::lower(function_set)?;
            render_function_set(&function, context)
        }
        Obj::SetBuilder(_) => {
            let lowered = LeanTargetObjectRepresentation::lower(obj)?;
            render_lean_source_for_target_set_representation(&lowered, context)
        }
        Obj::AnonymousFn(_) => {
            let LeanTargetObjectRepresentation::AnonymousFunction(function) =
                LeanTargetObjectRepresentation::lower(obj)?
            else {
                return Err("anonymous function lowered to another object".into());
            };
            render_anonymous_function(&function, context)
        }
        Obj::FnObj(application) => {
            let LeanTargetObjectRepresentation::FunctionApplication(application) =
                LeanTargetObjectRepresentation::lower(&application.clone().into())?
            else {
                return Err("function application lowered to a non-application object".into());
            };
            render_function_application(&application, context)
        }
        Obj::InstantiatedTemplateObj(application) => {
            if let Some(rendered) = context.symbol_names.get(&application.symbol.id()) {
                return Ok(rendered.clone());
            }
            let binding = context
                .template_set_alias_bindings
                .get(&application.template_name.to_string())
                .ok_or_else(|| format!("unbound compiler Template application `{obj}`"))?;
            if application.args.len() != binding.parameter_count {
                return Err(format!(
                    "Template application `{obj}` changed its compiled argument count"
                ));
            }
            let arguments = application
                .args
                .iter()
                .map(|argument| render_obj(argument, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("({} {})", binding.lean_name, arguments.join(" ")))
        }
        Obj::StandardSet(set) => render_standard_set(*set).map(str::to_string),
        _ => render_lean_source_for_target_object_representation(
            &LeanTargetObjectRepresentation::lower(obj)?,
            context,
        ),
    }
}

/// Preserve the existing exact-rational power representation whenever both
/// operands have visible rational/integer views. Complex calculate adds the
/// complementary representation for a literal integral exponent whose base
/// is only available as a native complex value.
pub(super) fn render_numeric_power(
    power: &Pow,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let (Ok(base), Ok(exponent)) = (
        render_rational_obj(power.base.as_ref(), context),
        render_integer_obj(power.exponent.as_ref(), context),
    ) {
        return Ok(format!("(({base} ^ {exponent} : ℚ) : ℂ)"));
    }

    let exponent = power
        .exponent
        .evaluate_to_normalized_decimal_number()
        .and_then(|number| number.normalized_value.parse::<i128>().ok())
        .ok_or_else(|| {
            format!(
                "complex power `{}` requires a literal integral exponent in the Lean target",
                Obj::from(power.clone())
            )
        })?;
    let base = render_numeric_obj(power.base.as_ref(), context)?;
    if exponent >= 0 {
        Ok(format!("({base} ^ ({exponent} : ℕ))"))
    } else {
        Ok(format!("({base} ^ ({exponent} : ℤ))"))
    }
}

pub(super) fn validate_set_parameter_premise(
    symbol_id: SymbolId,
    premise: &Fact,
) -> Result<(), String> {
    let Fact::AtomicFact(AtomicFact::IsSetFact(is_set)) = premise else {
        return Err(format!(
            "set parameter retained non-set evidence `{premise}`"
        ));
    };
    let Obj::Atom(atom) = &is_set.set else {
        return Err("set parameter evidence targets a non-symbol object".into());
    };
    if atom.symbol_ref().map(|symbol| symbol.id()) != Some(symbol_id) {
        return Err("set parameter evidence changed its SymbolId".into());
    }
    Ok(())
}

pub(super) fn validate_object_parameter_premise(
    symbol_id: SymbolId,
    expected_set: &Obj,
    premise: &Fact,
) -> Result<(), String> {
    let (element, set) = membership_parts(premise)?;
    if !object_is_symbol(element, symbol_id) {
        return Err("object parameter evidence changed its SymbolId".into());
    }
    if obj_equality_key(set) != obj_equality_key(expected_set) {
        return Err("object parameter evidence changed its carrier set".into());
    }
    Ok(())
}

pub(super) fn validate_refined_set_parameter_premise(
    symbol_id: SymbolId,
    param_type: &ParamType,
    premise: &Fact,
) -> Result<(), String> {
    let target = match (param_type, premise) {
        (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property))) => {
            &property.set
        }
        (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property))) => {
            &property.set
        }
        (ParamType::NonemptySet(_), _) => {
            return Err(format!(
                "nonempty-set parameter retained different evidence `{premise}`"
            ));
        }
        (ParamType::FiniteSet(_), _) => {
            return Err(format!(
                "finite-set parameter retained different evidence `{premise}`"
            ));
        }
        _ => return Err("refined-set validator received another parameter type".into()),
    };
    let Obj::Atom(atom) = target else {
        return Err("refined-set parameter evidence targets a non-symbol object".into());
    };
    if atom.symbol_ref().map(|symbol| symbol.id()) != Some(symbol_id) {
        return Err("refined-set parameter evidence changed its SymbolId".into());
    }
    Ok(())
}

pub(super) fn set_requires_heterogeneous_carrier(set: &Obj) -> bool {
    matches!(set, Obj::Atom(AtomObj::Bound(_)))
}

pub(super) fn validate_unary_function_type(
    function: &LeanTargetFunctionTypeRepresentation,
) -> Result<(), String> {
    if function.parameters.len() != 1 {
        return Err("compiler function-set MVP supports exactly one parameter".into());
    }
    if let LeanTargetObjectRepresentation::FunctionSet { function } = function.return_set.as_ref() {
        validate_unary_function_type(function)?;
    }
    Ok(())
}

pub(super) fn validate_function_type(
    function: &LeanTargetFunctionTypeRepresentation,
) -> Result<(), String> {
    if function.parameters.is_empty() {
        return Err("compiler function set retained an empty source parameter layer".into());
    }
    if let LeanTargetObjectRepresentation::FunctionSet { function } = function.return_set.as_ref() {
        validate_function_type(function)?;
    }
    Ok(())
}

pub(super) fn function_uses_telescope(function: &LeanTargetFunctionTypeRepresentation) -> bool {
    if function.parameters.len() != 1 {
        return true;
    }
    if !function.domain_facts.is_empty()
        && matches!(
            function.parameters[0].set,
            LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural)
        )
    {
        // The finite-sequence bound depends on the natural representative
        // selected by the parameter's `N+` membership proof. A `FnWhere`
        // predicate receives only the heterogeneous value, while the
        // telescope parameter node owns both that value and its membership.
        return true;
    }
    let parameter_symbols = function
        .parameters
        .iter()
        .map(|parameter| parameter.symbol_id)
        .collect::<HashSet<_>>();
    function
        .parameters
        .iter()
        .any(|parameter| !object_ir_is_independent_of_symbols(&parameter.set, &parameter_symbols))
        || !object_ir_is_independent_of_symbols(function.return_set.as_ref(), &parameter_symbols)
}

pub(super) fn object_ir_is_independent_of_symbols(
    object: &LeanTargetObjectRepresentation,
    symbol_ids: &HashSet<SymbolId>,
) -> bool {
    match object {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => !symbol_ids.contains(symbol_id),
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            function
                .parameters
                .iter()
                .all(|parameter| object_ir_is_independent_of_symbols(&parameter.set, symbol_ids))
                && object_ir_is_independent_of_symbols(function.return_set.as_ref(), symbol_ids)
        }
        LeanTargetObjectRepresentation::FunctionApplication(application) => {
            object_ir_is_independent_of_symbols(application.head.as_ref(), symbol_ids)
                && application.argument_layers.iter().all(|layer| {
                    layer
                        .iter()
                        .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids))
                })
        }
        LeanTargetObjectRepresentation::ClosedRange { start, end }
        | LeanTargetObjectRepresentation::Range { start, end } => {
            object_ir_is_independent_of_symbols(start, symbol_ids)
                && object_ir_is_independent_of_symbols(end, symbol_ids)
        }
        LeanTargetObjectRepresentation::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => {
            object_ir_is_independent_of_symbols(index_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_function, symbol_ids)
        }
        LeanTargetObjectRepresentation::SequenceSet { values, length } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && length
                    .as_ref()
                    .is_none_or(|length| object_ir_is_independent_of_symbols(length, symbol_ids))
        }
        LeanTargetObjectRepresentation::MatrixSet {
            values,
            row_count,
            column_count,
        } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && object_ir_is_independent_of_symbols(row_count, symbol_ids)
                && object_ir_is_independent_of_symbols(column_count, symbol_ids)
        }
        LeanTargetObjectRepresentation::Aggregate { arguments, .. } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        LeanTargetObjectRepresentation::TupleDimension(object) => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
        }
        LeanTargetObjectRepresentation::IndexedAccess { object, index } => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
                && object_ir_is_independent_of_symbols(index, symbol_ids)
        }
        LeanTargetObjectRepresentation::BuiltinApp { arguments, .. }
        | LeanTargetObjectRepresentation::Collection {
            items: arguments, ..
        } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        // Binder-owning objects are kept on the dependent telescope path. The
        // owned binder itself may hide a reference to an outer parameter in
        // one of its source facts, which the flattened IR does not erase.
        LeanTargetObjectRepresentation::SetBuilder(_)
        | LeanTargetObjectRepresentation::AnonymousFunction(_) => false,
        LeanTargetObjectRepresentation::Number { .. }
        | LeanTargetObjectRepresentation::Constant(_)
        | LeanTargetObjectRepresentation::StandardSet(_) => true,
    }
}

pub(super) fn exact_set_real_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("(((({value}).val : ℕ)) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("(({value} : ℕ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("(({value} : ℤ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("(({value} : ℚ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(
            LeanTargetStandardSet::PositiveRational | LeanTargetStandardSet::NegativeRational,
        ) => Some(format!("((({value}).val : ℚ) : ℝ)")),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("((({value}).val : ℤ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(
            LeanTargetStandardSet::PositiveReal | LeanTargetStandardSet::NegativeReal,
        ) => Some(format!("(({value}).val : ℝ)")),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("({value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_real_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(super) fn exact_set_integer_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("((({value}).val : ℕ) : ℤ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("(({value} : ℕ) : ℤ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("({value} : ℤ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("(({value}).val : ℤ)"))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => {
            Some(format!("(({value}).val : ℤ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_integer_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(super) fn exact_set_rational_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("((({value}).val : ℕ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("(({value} : ℕ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("(({value} : ℤ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("({value} : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(
            LeanTargetStandardSet::PositiveRational | LeanTargetStandardSet::NegativeRational,
        ) => Some(format!("(({value}).val : ℚ)")),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("((({value}).val : ℤ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_rational_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(super) fn exact_set_numeric_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("(((({value}).val : ℕ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("((({value} : ℕ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("((({value} : ℤ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("((({value} : ℚ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("((({value} : ℝ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(format!("({value} : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!("(((({value}).val : ℚ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("(((({value}).val : ℤ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => {
            Some(format!("(((({value}).val : ℤ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!("(((({value}).val : ℝ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_numeric_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(super) fn membership_real_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_real_value(set, &format!("Litex.In.rep {value} {membership}"))
}

pub(super) fn membership_integer_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_integer_value(set, &format!("Litex.In.rep {value} {membership}"))
}

pub(super) fn membership_rational_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_rational_value(set, &format!("Litex.In.rep {value} {membership}"))
}

pub(super) fn membership_numeric_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_numeric_value(set, &format!("Litex.In.rep {value} {membership}"))
}

/// Construct the exact `Same source selected_numeric_complex_value` bridge
/// owned by one visible membership proof. This is target representation state,
/// not a new proof search: every step is determined by the carrier and the
/// same `Litex.In.rep` expression used by `membership_numeric_value`.
pub(super) fn membership_numeric_equality(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    let representative = format!("Litex.In.rep {value} {membership}");
    let representative_to_numeric = exact_set_numeric_equality(set, &representative)?;
    Some(format!(
        "Litex.Same.trans (Litex.In.same_rep {value} ({membership})) ({representative_to_numeric})"
    ))
}

pub(super) fn exact_set_numeric_equality(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.natComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("Litex.Same.natComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("Litex.Same.intComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("Litex.Same.ratComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("Litex.Same.realComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(format!("Litex.Same.refl ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.ratComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.intComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => Some(format!(
            "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.intComplex (({value}).val))"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.realComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            let base_value = format!("({value}).val");
            let base_equality = exact_set_numeric_equality(builder.set.as_ref(), &base_value)?;
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) ({base_equality})"
            ))
        }
        _ => None,
    }
}

pub(super) fn membership_numeric_proof(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    let representative = format!("Litex.In.rep {value} {membership}");
    exact_set_numeric_proof(set, &representative)
}

pub(super) fn exact_set_numeric_proof(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!(
                "Litex.Rules.complexEqNatInNPos (((({value}).val : ℕ) : ℂ)) (({value}).val : ℕ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => Some(format!(
            "Litex.Rules.complexEqNatInN ((({value} : ℕ) : ℂ)) ({value} : ℕ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => Some(format!(
            "Litex.Rules.complexEqIntInZ ((({value} : ℤ) : ℂ)) ({value} : ℤ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => Some(format!(
            "Litex.Rules.complexEqRatInQ ((({value} : ℚ) : ℂ)) ({value} : ℚ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("Litex.Rules.complexRealInR ({value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(format!("Litex.Rules.complexInC ({value} : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational) => {
            Some(format!(
                "Litex.Rules.complexEqRatInQPos (((({value}).val : ℚ) : ℂ)) (({value}).val : ℚ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!(
                "Litex.Rules.complexEqIntInZNeg (((({value}).val : ℤ) : ℂ)) (({value}).val : ℤ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => Some(format!(
            "Litex.Rules.complexEqIntInZ (((({value}).val : ℤ) : ℂ)) (({value}).val : ℤ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!(
                "Litex.Rules.complexEqRatInQNeg (((({value}).val : ℚ) : ℂ)) (({value}).val : ℚ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal) => {
            Some(format!(
                "Litex.Rules.complexEqRealInRPos (((({value}).val : ℝ) : ℂ)) (({value}).val : ℝ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!(
                "Litex.Rules.complexEqRealInRNeg (((({value}).val : ℝ) : ℂ)) (({value}).val : ℝ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_numeric_proof(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(super) fn render_telescope_signature(
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
pub(super) fn render_telescope_domain_requirement(
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

pub(super) fn positive_natural_parameter_less_equal_natural_bound(
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

pub(super) fn render_function_requirement(
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

pub(super) fn render_function_type(
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

pub(super) fn render_function_set(
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

pub(super) fn render_nested_function_set(
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

/// Render the target value for a direct named-function Result.
/// Binder names are the same names installed by the parent Result compiler's
/// child environment, so the nesting of the generated Lean term mirrors the
/// nesting of `SuccessVerifyFunctionDefinitionResult`. A native-real return
/// can be represented directly; every other return carrier is selected from
/// the exact recursive membership proof retained by that Result.
pub(super) fn render_named_function_value_from_result(
    function: &LeanTargetFunctionTypeRepresentation,
    body: &LeanTargetObjectRepresentation,
    source_body: &Obj,
    return_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(String, bool), String> {
    let real_signature = function.parameters.iter().all(|parameter| {
        parameter.set == LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real)
    }) && function.return_set.as_ref()
        == &LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real);
    if function_uses_telescope(function) {
        validate_function_type(function)?;
        let mut binders = Vec::with_capacity(function.parameters.len() + 1);
        let mut parameter_representations = HashMap::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let suffix = index + 1;
            let alpha = format!("__alpha{suffix}");
            let argument = format!("__arg{suffix}");
            let membership = format!("__arg{suffix}_in");
            let domain = render_lean_source_for_target_set_representation(&parameter.set, context)?;
            binders.push(format!(
                "fun {{{alpha} : Type}} ({argument} : {alpha}) ({membership} : Litex.In {argument} {domain}) => "
            ));
            parameter_representations.insert(
                parameter.symbol_id,
                format!("Litex.In.rep {argument} {membership}"),
            );
        }
        if !function.domain_facts.is_empty() {
            binders.push("fun __arg_domain => ".into());
        }
        let body = if real_signature {
            render_real_function_body_with_parameters(body, &parameter_representations, context)?
        } else {
            let rendered_source_body = render_obj(source_body, context)?;
            format!("Litex.In.rep {rendered_source_body} ({return_proof})")
        };
        return Ok((
            format!("{}ULift.up ({body})", binders.concat()),
            real_signature,
        ));
    }

    validate_unary_function_type(function)?;
    let body = if real_signature {
        render_real_function_body(
            body,
            function.parameters[0].symbol_id,
            "Litex.In.rep __arg __arg_in",
            context,
        )?
    } else {
        let rendered_source_body = render_obj(source_body, context)?;
        format!("Litex.In.rep {rendered_source_body} ({return_proof})")
    };
    if function.domain_facts.is_empty() {
        Ok((
            format!("{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {body} }}"),
            real_signature,
        ))
    } else {
        Ok((
            format!(
                "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {body} }}"
            ),
            real_signature,
        ))
    }
}

pub(super) fn render_real_function_body(
    body: &LeanTargetObjectRepresentation,
    parameter_symbol_id: SymbolId,
    parameter_representation: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_real_function_body_with_parameters(
        body,
        &HashMap::from([(parameter_symbol_id, parameter_representation.to_string())]),
        context,
    )
}

pub(super) fn render_real_function_body_with_parameters(
    body: &LeanTargetObjectRepresentation,
    parameter_representations: &HashMap<SymbolId, String>,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match body {
        LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
            if parameter_representations.contains_key(symbol_id) =>
        {
            Ok(parameter_representations[symbol_id].clone())
        }
        LeanTargetObjectRepresentation::Number { normalized_value }
            if !normalized_value.is_empty()
                && normalized_value
                    .chars()
                    .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!("({normalized_value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } if arguments.len() == 2
            && matches!(
                operator,
                LeanTargetBuiltinObjectOperator::Add
                    | LeanTargetBuiltinObjectOperator::Sub
                    | LeanTargetBuiltinObjectOperator::Mul
                    | LeanTargetBuiltinObjectOperator::Div
            ) =>
        {
            let left = render_real_function_body_with_parameters(
                &arguments[0],
                parameter_representations,
                context,
            )?;
            let right = render_real_function_body_with_parameters(
                &arguments[1],
                parameter_representations,
                context,
            )?;
            let operator = match operator {
                LeanTargetBuiltinObjectOperator::Add => "+",
                LeanTargetBuiltinObjectOperator::Sub => "-",
                LeanTargetBuiltinObjectOperator::Mul => "*",
                LeanTargetBuiltinObjectOperator::Div => "/",
                _ => unreachable!("guarded real binary operator"),
            };
            Ok(format!("({left} {operator} {right})"))
        }
        LeanTargetObjectRepresentation::Symbol { .. } => render_ir_symbol(body, context),
        other => Err(format!(
            "compiler real named-function body does not support {other:?}"
        )),
    }
}

pub(super) fn render_anonymous_function(
    function: &LeanTargetAnonymousFunctionRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    validate_function_type(&function.function)?;
    let occurrence = function.source_occurrence_id.ok_or_else(|| {
        "anonymous function has no parser-owned source occurrence identity".to_string()
    })?;
    let result_context = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "anonymous function has no active Result-owned WD context".to_string())?;
    let anonymous_context = result_context
        .anonymous_functions
        .get(&occurrence)
        .ok_or_else(|| {
            format!(
                "anonymous function occurrence {} has no exact recursive Result context",
                occurrence.value()
            )
        })?;
    if obj_equality_key(&anonymous_context.source_function) != function.semantic_key {
        return Err(
            "anonymous function Result context changed its source body or signature".into(),
        );
    }

    let mut nested = context.clone();
    let uses_telescope = function_uses_telescope(&function.function);
    let mut binders = Vec::with_capacity(function.function.parameters.len());
    let mut parameter_values = HashMap::new();
    for (parameter_index, parameter) in function.function.parameters.iter().enumerate() {
        let matches = anonymous_context
            .parameters
            .iter()
            .filter(|premise| {
                matches!(
                    premise.role,
                    WellDefinedBinderPremiseRole::ParameterMembership { .. }
                ) && premise.symbol_id == Some(parameter.symbol_id)
            })
            .collect::<Vec<_>>();
        let [parameter_premise] = matches.as_slice() else {
            return Err(format!(
                "anonymous function requires one exact membership premise for parameter {parameter_index}"
            ));
        };
        let suffix = if uses_telescope {
            (parameter_index + 1).to_string()
        } else {
            String::new()
        };
        let argument = format!("__arg{suffix}");
        let membership = format!("__arg{suffix}_in");
        let domain = render_lean_source_for_target_set_representation(&parameter.set, &nested)?;
        if uses_telescope {
            binders.push(format!(
                "fun {{__alpha{} : Type}} ({argument} : __alpha{}) ({membership} : Litex.In {argument} {domain}) => ",
                parameter_index + 1,
                parameter_index + 1,
            ));
        }
        nested
            .symbol_names
            .insert(parameter.symbol_id, argument.clone());
        nested
            .fact_names
            .insert(parameter_premise.fact_id, membership.clone());
        nested.fact_propositions.insert(
            parameter_premise.fact_id,
            parameter_premise.proposition.clone(),
        );
        if let Some(real) = membership_real_value(&parameter.set, &argument, &membership) {
            nested.numeric_real_values.insert(parameter.symbol_id, real);
        }
        if let Some(integer) = membership_integer_value(&parameter.set, &argument, &membership) {
            nested
                .numeric_integer_values
                .insert(parameter.symbol_id, integer);
        }
        if let Some(rational) = membership_rational_value(&parameter.set, &argument, &membership) {
            nested
                .numeric_rational_values
                .insert(parameter.symbol_id, rational);
        }
        if let Some(representation) =
            membership_numeric_value(&parameter.set, &argument, &membership)
        {
            nested
                .numeric_representations
                .insert(parameter.symbol_id, representation);
        }
        if let Some(proof) = membership_numeric_proof(&parameter.set, &argument, &membership) {
            nested
                .numeric_representation_memberships
                .insert(parameter.symbol_id, proof);
        }
        parameter_values.insert(parameter.symbol_id, (argument, membership));
    }

    let domain_premises = &anonymous_context.domains;
    if domain_premises.len() != function.function.domain_facts.len() {
        return Err("anonymous function binder scope changed its domain-premise count".into());
    }
    for (index, premise) in domain_premises.iter().enumerate() {
        let selector = conjunction_selector(index, domain_premises.len())?;
        let name = if domain_premises.len() == 1 {
            "__arg_domain".into()
        } else {
            format!("__arg_domain{selector}")
        };
        nested.fact_names.insert(premise.fact_id, name);
        nested
            .fact_propositions
            .insert(premise.fact_id, premise.proposition.clone());
    }
    if uses_telescope && !domain_premises.is_empty() {
        binders.push("fun __arg_domain => ".into());
    }

    let mut inferred_lets = Vec::new();
    for step in &anonymous_context.compiled_inference_fact_proof_steps {
        inferred_lets.push(format!("{}; ", step.render_as_local_let_statement()));
        nested
            .fact_names
            .insert(step.fact_id, step.local_lean_name.clone());
        nested
            .fact_propositions
            .insert(step.fact_id, step.fact.clone());
    }

    let closure = &anonymous_context.closure;
    let selected_return = match closure.role {
        WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
            let (body, return_set) = membership_parts(&closure.expected_proposition)?;
            if LeanTargetObjectRepresentation::lower(body)? != *function.body
                || LeanTargetObjectRepresentation::lower(return_set)?
                    != *function.function.return_set
            {
                return Err(
                    "anonymous function return closure changed its exact body or carrier".into(),
                );
            }
            format!(
                "Litex.In.rep {} ({})",
                render_obj(body, &nested)?,
                closure.proof_expression.as_ref().ok_or_else(|| {
                    "anonymous function body-membership Result was not compiled".to_string()
                })?
            )
        }
        WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
            parameter_group_index: _,
            parameter_index,
        } => {
            let parameter = function
                .function
                .parameters
                .get(parameter_index)
                .ok_or_else(|| {
                    "anonymous subset closure changed its bound parameter index".to_string()
                })?;
            let (argument, membership) =
                parameter_values.get(&parameter.symbol_id).ok_or_else(|| {
                    "anonymous subset closure lost its parameter evidence".to_string()
                })?;
            format!("Litex.In.rep {argument} {membership}")
        }
        _ => return Err("anonymous function retained an unsupported return-closure route".into()),
    };
    let checked_body = format!("{}{}", inferred_lets.concat(), selected_return);
    let value = if uses_telescope {
        format!("{}ULift.up ({checked_body})", binders.concat())
    } else if function.function.domain_facts.is_empty() {
        format!("{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in => {checked_body} }}")
    } else {
        format!(
            "{{ call := fun {{__alpha}} (__arg : __alpha) __arg_in __arg_domain => {checked_body} }}"
        )
    };
    Ok(format!(
        "({value} : {})",
        render_function_type(&function.function, context)?
    ))
}

pub(super) fn render_lean_source_for_target_set_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LeanTargetObjectRepresentation::Symbol { symbol_id, name } => context
            .symbol_names
            .get(symbol_id)
            .cloned()
            .ok_or_else(|| format!("unbound compiler set symbol `{name}`")),
        LeanTargetObjectRepresentation::StandardSet(set) => {
            render_lean_source_for_standard_set_representation(*set)
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            let base =
                render_lean_source_for_target_set_representation(builder.set.as_ref(), context)?;
            let parameter = lean_identifier(&builder.name);
            let mut nested = context.clone();
            nested
                .symbol_names
                .insert(builder.symbol_id, parameter.clone());
            if let Some(real) = exact_set_real_value(builder.set.as_ref(), &parameter) {
                nested.numeric_real_values.insert(builder.symbol_id, real);
            }
            if let Some(integer) = exact_set_integer_value(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_integer_values
                    .insert(builder.symbol_id, integer);
            }
            if let Some(rational) = exact_set_rational_value(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_rational_values
                    .insert(builder.symbol_id, rational);
            }
            if let Some(representation) = exact_set_numeric_value(builder.set.as_ref(), &parameter)
            {
                nested
                    .numeric_representations
                    .insert(builder.symbol_id, representation);
            }
            if let Some(proof) = exact_set_numeric_proof(builder.set.as_ref(), &parameter) {
                nested
                    .numeric_representation_memberships
                    .insert(builder.symbol_id, proof);
            }
            let facts = builder
                .facts
                .iter()
                .map(|fact| render_fact(fact, &nested))
                .collect::<Result<Vec<_>, _>>()?;
            if facts.is_empty() {
                return Err("compiler set builder retained an empty predicate".into());
            }
            Ok(format!(
                "(Litex.setBuilder {base} (fun ({parameter} : {base}.Carrier) => {}))",
                conjunction(&facts)
            ))
        }
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            render_function_set(function, context)
        }
        other => Err(format!(
            "unsupported compiler function domain/codomain `{other:?}`"
        )),
    }
}

fn matches_directly_or_after_one_transparent_definition_pass(
    source: &Obj,
    target: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    if obj_equality_key(source) == obj_equality_key(target) {
        return Ok(true);
    }
    let substitutions = context
        .transparent_object_definitions
        .iter()
        .map(|(symbol_id, definition)| (symbol_id.substitution_key(), definition.value.clone()))
        .collect::<HashMap<_, _>>();
    if substitutions.is_empty() {
        return Ok(false);
    }
    let reduced = Runtime::new()
        .inst_obj(source, &substitutions, SubstitutionMode::Exact)
        .map_err(|error| {
            format!(
                "compiler could not replay transparent definition source alignment: {}",
                error.trace_message()
            )
        })?;
    Ok(obj_equality_key(&reduced) == obj_equality_key(target))
}

pub(super) fn render_function_application(
    application: &LeanTargetFunctionApplicationRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if application.argument_layers.is_empty()
        || application.argument_layers.len() != application.source_argument_layers.len()
        || application
            .argument_layers
            .iter()
            .zip(application.source_argument_layers.iter())
            .any(|(arguments, source_arguments)| {
                arguments.is_empty() || arguments.len() != source_arguments.len()
            })
    {
        return Err(
            "compiler function application changed a retained source argument layer".into(),
        );
    }
    let Obj::FnObj(source_application) = &application.source_application else {
        return Err("function application retained a non-application source object".into());
    };
    let result_context = context
        .well_definedness
        .as_ref()
        .ok_or_else(|| "function application has no active Result-owned WD context".to_string())?;
    let application_context = result_context
        .function_applications
        .get(&application.source_occurrence_id)
        .ok_or_else(|| {
            let available_occurrences = result_context
                .function_applications
                .keys()
                .map(|source_occurrence_id| source_occurrence_id.value().to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "function application occurrence {} has no exact recursive Result context; active child occurrences are [{}]",
                application.source_occurrence_id.value(),
                available_occurrences,
            )
        })?;
    if !matches_directly_or_after_one_transparent_definition_pass(
        &application_context.source_application,
        &application.source_application,
        context,
    )? {
        return Err("function application Result context changed its source occurrence".into());
    }

    let layer_count = application.argument_layers.len();
    if application_context.layers.len() != layer_count {
        return Err("function application Result context changed its layer count".into());
    }
    for (layer_index, layer_context) in application_context.layers.iter().enumerate() {
        let source_prefix = source_application.prefix_obj(layer_index + 1);
        if !matches_directly_or_after_one_transparent_definition_pass(
            &layer_context.source_prefix,
            &source_prefix,
            context,
        )? {
            return Err(format!(
                "application layer {layer_index} changed its verifier-owned source prefix"
            ));
        }
    }

    let root_contracts = application_context.function_contracts.clone();
    let (mut function, mut head, mut membership_proof, mut direct) = match application.head.as_ref()
    {
        LeanTargetObjectRepresentation::Symbol {
            symbol_id: head_symbol_id,
            ..
        } => {
            let [WellDefinedFunctionContract::StoredMembershipFact(contract_fact_id)] =
                root_contracts.as_slice()
            else {
                return Err(
                    "named application requires one verifier-selected membership FactId".into(),
                );
            };
            let binding = context
                .function_bindings
                .get(contract_fact_id)
                .ok_or_else(|| {
                    format!("unavailable function membership FactId `{contract_fact_id}`")
                })?;
            if *head_symbol_id != binding.symbol_id {
                let definition = context
                    .transparent_object_definitions
                    .get(head_symbol_id)
                    .ok_or_else(|| {
                        "function membership FactId belongs to another head symbol".to_string()
                    })?;
                let retained_fact = context
                    .fact_propositions
                    .get(&definition.defining_equality_fact_id)
                    .ok_or_else(|| {
                        "transparent callable alias lost its defining equality FactId".to_string()
                    })?;
                if retained_fact.to_string() != definition.defining_equality.to_string()
                    || !context
                        .fact_names
                        .contains_key(&definition.defining_equality_fact_id)
                {
                    return Err(
                        "transparent callable alias changed its defining equality citation".into(),
                    );
                }
                let lowered_definition = LeanTargetObjectRepresentation::lower(&definition.value)?;
                if !matches!(
                    lowered_definition,
                    LeanTargetObjectRepresentation::Symbol { symbol_id, .. }
                        if symbol_id == binding.symbol_id
                ) {
                    return Err(
                        "transparent callable alias does not reduce once to the selected function contract"
                            .into(),
                    );
                }
            }
            (
                binding.function.clone(),
                render_ir_symbol(application.head.as_ref(), context)?,
                binding.membership_proof_name.clone(),
                binding.direct,
            )
        }
        LeanTargetObjectRepresentation::AnonymousFunction(anonymous) => {
            if !root_contracts.is_empty() {
                return Err("anonymous application retained an unexpected named contract".into());
            }
            let head_object = application_context
                .anonymous_function_head
                .as_ref()
                .ok_or_else(|| {
                    "anonymous application requires one exact FunctionHead child Result".to_string()
                })?;
            if obj_equality_key(head_object) != anonymous.semantic_key {
                return Err("anonymous application changed its verifier-owned head".into());
            }
            let head = render_anonymous_function(anonymous, context)?;
            let function_set = render_function_set(&anonymous.function, context)?;
            (
                anonymous.function.clone(),
                head.clone(),
                format!("(Litex.In.own {function_set} {head})"),
                true,
            )
        }
        _ => return Err("compiler function application requires a named or anonymous head".into()),
    };
    let mut layer_lets = Vec::new();
    for layer_index in 0..layer_count {
        validate_function_type(&function)?;
        let layer_context = &application_context.layers[layer_index];
        if layer_context.function_contracts != root_contracts {
            return Err(format!(
                "application layer {layer_index} changed its root function contract"
            ));
        }
        if function.parameters.len() != application.argument_layers[layer_index].len() {
            return Err(format!(
                "application layer {layer_index} expected {} parameters, retained {} arguments",
                function.parameters.len(),
                application.argument_layers[layer_index].len()
            ));
        }
        for (source_argument, retained_argument) in application.source_argument_layers[layer_index]
            .iter()
            .zip(application.argument_layers[layer_index].iter())
        {
            if LeanTargetObjectRepresentation::lower(source_argument)? != *retained_argument {
                return Err(format!(
                    "application layer {layer_index} changed its retained argument IR"
                ));
            }
        }

        let mut argument_requirements = vec![None; function.parameters.len()];
        let mut domain_requirements = vec![None; function.domain_facts.len()];
        for requirement in &layer_context.requirements {
            match requirement.role {
                WellDefinednessRequirementRole::FunctionArgumentMembership {
                    layer_index: retained_layer_index,
                    parameter_index,
                } if retained_layer_index == layer_index
                    && parameter_index < argument_requirements.len() =>
                {
                    if argument_requirements[parameter_index]
                        .replace(requirement)
                        .is_some()
                    {
                        return Err(format!(
                            "application layer {layer_index} retained duplicate argument-membership requirement {parameter_index}"
                        ));
                    }
                }
                WellDefinednessRequirementRole::FunctionDomain {
                    layer_index: retained_layer_index,
                    domain_index,
                } if retained_layer_index == layer_index
                    && domain_index < domain_requirements.len() =>
                {
                    if domain_requirements[domain_index]
                        .replace(requirement)
                        .is_some()
                    {
                        return Err(format!(
                            "application layer {layer_index} retained duplicate domain requirement {domain_index}"
                        ));
                    }
                }
                role => {
                    return Err(format!(
                        "application layer {layer_index} retained an unexpected target requirement {role:?}"
                    ));
                }
            }
        }
        if argument_requirements.iter().any(Option::is_none) {
            return Err(format!(
                "application layer {layer_index} lost a checked argument-membership requirement"
            ));
        }
        if domain_requirements.iter().any(Option::is_none) {
            return Err(format!(
                "application layer {layer_index} lost a checked source-domain requirement"
            ));
        }
        let mut nested = context.clone();
        // Domain verification in Result is about the original source
        // arguments. The target telescope may separately observe a
        // heterogeneous parameter through its membership proof, so keep a
        // source-facing rendering context for exact Result validation.
        let mut source_domain_nested = context.clone();
        let mut arguments = Vec::with_capacity(function.parameters.len());
        let mut argument_memberships = Vec::with_capacity(function.parameters.len());
        for (_parameter_index, ((parameter, source_argument), requirement)) in function
            .parameters
            .iter()
            .zip(application.source_argument_layers[layer_index].iter())
            .zip(argument_requirements.into_iter())
            .enumerate()
        {
            let requirement = requirement.expect("argument requirements checked above");
            let argument = render_obj(source_argument, context)?;
            let expected_argument_membership = format!(
                "Litex.In {argument} {}",
                render_lean_source_for_target_set_representation(&parameter.set, &nested)?
            );
            let retained_argument_membership =
                render_fact(&requirement.expected_proposition, context)?;
            if retained_argument_membership != expected_argument_membership {
                return Err(format!(
                    "application layer {layer_index} expected `{expected_argument_membership}`, retained `{retained_argument_membership}`"
                ));
            }
            let argument_membership =
                render_function_application_requirement_proof(requirement, context)?;
            arguments.push(argument.clone());
            argument_memberships.push(argument_membership.clone());
            nested
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
            source_domain_nested
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
            source_domain_nested
                .numeric_representations
                .insert(parameter.symbol_id, argument.clone());
            if let Some(real) = membership_real_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested.numeric_real_values.insert(parameter.symbol_id, real);
            }
            if let Some(integer) = membership_integer_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_integer_values
                    .insert(parameter.symbol_id, integer);
            }
            if let Some(rational) = membership_rational_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_rational_values
                    .insert(parameter.symbol_id, rational);
            }
            if let Some(representation) = membership_numeric_value(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_representations
                    .insert(parameter.symbol_id, representation);
            }
            if let Some(proof) = membership_numeric_proof(
                &parameter.set,
                arguments.last().expect("argument was just retained"),
                &argument_membership,
            ) {
                nested
                    .numeric_representation_memberships
                    .insert(parameter.symbol_id, proof);
            }
        }
        let mut domain_proofs = Vec::with_capacity(domain_requirements.len());
        for (_domain_index, (source_fact, requirement)) in function
            .domain_facts
            .iter()
            .zip(domain_requirements.into_iter())
            .enumerate()
        {
            let requirement = requirement.expect("domain requirements checked above");
            let expected = render_fact(source_fact, &source_domain_nested)?;
            let retained = render_fact(&requirement.expected_proposition, context)?;
            if expected != retained {
                return Err(format!(
                    "application layer {layer_index} expected domain clause {expected}, retained {retained}"
                ));
            }
            let retained_proof =
                render_function_application_requirement_proof(requirement, context)?;
            if positive_natural_parameter_less_equal_natural_bound(&function, source_fact)?
                .is_some()
            {
                domain_proofs.push(format!(
                    "Litex.positiveNaturalParameterLessEqualNaturalBoundOfComplex ({retained_proof})"
                ));
            } else {
                domain_proofs.push(retained_proof);
            }
        }

        let application_term = if !function_uses_telescope(&function) {
            let apply = match (direct, domain_proofs.is_empty()) {
                (true, true) => "Litex.fnApplyOwn",
                (false, true) => "Litex.fnApply",
                (true, false) => "Litex.fnApplyWhereOwn",
                (false, false) => "Litex.fnApplyWhere",
            };
            let argument = &arguments[0];
            let argument_membership = &argument_memberships[0];
            if domain_proofs.is_empty() {
                format!("({apply} {head} {membership_proof} {argument} ({argument_membership}))")
            } else {
                let domain_proof = if domain_proofs.len() == 1 {
                    domain_proofs[0].clone()
                } else {
                    format!("⟨{}⟩", domain_proofs.join(", "))
                };
                format!(
                    "({apply} {head} {membership_proof} {argument} ({argument_membership}) ({domain_proof}))"
                )
            }
        } else {
            let apply = if direct {
                "Litex.fnTelescopeApplyOwn"
            } else {
                "Litex.fnTelescopeApply"
            };
            let mut term = format!("({apply} {head} {membership_proof})");
            for (argument, argument_membership) in arguments.iter().zip(argument_memberships.iter())
            {
                term = format!("({term} {argument} ({argument_membership}))");
            }
            if !domain_proofs.is_empty() {
                let domain_proof = if domain_proofs.len() == 1 {
                    domain_proofs[0].clone()
                } else {
                    format!("⟨{}⟩", domain_proofs.join(", "))
                };
                term = format!("({term} ({domain_proof}))");
            }
            format!("({term}).down")
        };

        if layer_index + 1 == layer_count {
            head = application_term;
            continue;
        }
        let LeanTargetObjectRepresentation::FunctionSet {
            function: next_function,
        } = function.return_set.as_ref()
        else {
            return Err(format!(
                "application layer {layer_index} does not return the next function set"
            ));
        };
        let retained_result_set = layer_context.intrinsic_result_set.as_ref().ok_or_else(|| {
            format!("application layer {layer_index} lost its Result-owned intrinsic result set")
        })?;
        if LeanTargetObjectRepresentation::lower(retained_result_set)? != *function.return_set {
            return Err(format!(
                "application layer {layer_index} lost its exact verifier-owned result set"
            ));
        }
        let next_function_set = render_function_set(next_function, context)?;
        let layer_name = format!("__fn_layer{}", layer_index + 1);
        layer_lets.push(format!("(let {layer_name} := {application_term}; "));
        head = layer_name;
        membership_proof = format!("(Litex.In.own {next_function_set} {head})");
        function = next_function.as_ref().clone();
        direct = true;
    }
    Ok(format!(
        "{}{}{}",
        layer_lets.concat(),
        head,
        ")".repeat(layer_lets.len())
    ))
}

pub(super) fn render_ir_symbol(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let LeanTargetObjectRepresentation::Symbol { symbol_id, name } = object else {
        return Err("expected a compiler symbol".into());
    };
    context
        .symbol_names
        .get(symbol_id)
        .cloned()
        .ok_or_else(|| format!("unbound compiler symbol `{name}`"))
}

pub(super) fn render_lean_source_for_native_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    render_lean_source_for_target_object_representation(object, context)
}

pub(super) fn render_lean_source_for_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match object {
        LeanTargetObjectRepresentation::Symbol { .. } => render_ir_symbol(object, context),
        LeanTargetObjectRepresentation::Number { normalized_value } => {
            render_normalized_complex_number(normalized_value)
        }
        LeanTargetObjectRepresentation::Constant(constant) => Ok(match constant {
            LeanTargetConstantObject::ImaginaryUnit => "Complex.I".into(),
            LeanTargetConstantObject::EulerNumber => "((Real.exp 1 : ℝ) : ℂ)".into(),
            LeanTargetConstantObject::Pi => "((Real.pi : ℝ) : ℂ)".into(),
        }),
        LeanTargetObjectRepresentation::StandardSet(set) => {
            render_lean_source_for_standard_set_representation(*set)
        }
        LeanTargetObjectRepresentation::FunctionSet { function } => {
            render_function_set(function, context)
        }
        LeanTargetObjectRepresentation::SetBuilder(_) => {
            render_lean_source_for_target_set_representation(object, context)
        }
        LeanTargetObjectRepresentation::AnonymousFunction(function) => {
            render_anonymous_function(function, context)
        }
        LeanTargetObjectRepresentation::FunctionApplication(application) => {
            render_function_application(application, context)
        }
        LeanTargetObjectRepresentation::Range { start, end } => Ok(format!(
            "(Litex.range {} {})",
            render_integer_endpoint(start, context)?,
            render_integer_endpoint(end, context)?
        )),
        LeanTargetObjectRepresentation::ClosedRange { start, end } => Ok(format!(
            "(Litex.closedRange {} {})",
            render_integer_endpoint(start, context)?,
            render_integer_endpoint(end, context)?
        )),
        LeanTargetObjectRepresentation::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => Ok(format!(
            "(Litex.generalCart {} {} {})",
            render_lean_source_for_target_object_representation(index_set, context)?,
            render_lean_source_for_target_object_representation(family_set, context)?,
            render_lean_source_for_target_object_representation(family_function, context)?
        )),
        LeanTargetObjectRepresentation::SequenceSet { values, length } => match length {
            Some(length) => Ok(format!(
                "(Litex.finiteSequenceSet.{{0}} {} {})",
                render_lean_source_for_target_set_representation(values, context)?,
                render_natural_endpoint(length)?
            )),
            None => Ok(format!(
                "(Litex.sequenceSet {})",
                render_lean_source_for_target_set_representation(values, context)?
            )),
        },
        LeanTargetObjectRepresentation::MatrixSet {
            values,
            row_count,
            column_count,
        } => Ok(format!(
            "(Litex.matrixSet.{{0}} {} {} {})",
            render_lean_source_for_target_set_representation(values, context)?,
            render_natural_endpoint(row_count)?,
            render_natural_endpoint(column_count)?,
        )),
        LeanTargetObjectRepresentation::Aggregate {
            kind, arguments, ..
        } => render_aggregate_object(*kind, arguments, context),
        LeanTargetObjectRepresentation::TupleDimension(tuple) => Ok(format!(
            "(Litex.tupleDim {})",
            render_lean_source_for_target_object_representation(tuple, context)?
        )),
        LeanTargetObjectRepresentation::IndexedAccess { object, index } => {
            render_literal_indexed_access(object, index, context)
        }
        LeanTargetObjectRepresentation::BuiltinApp {
            operator,
            arguments,
            ..
        } => render_builtin_object(*operator, arguments, context),
        LeanTargetObjectRepresentation::Collection {
            constructor: LeanTargetCollectionObjectConstructor::Tuple,
            items,
            ..
        } => render_typed_spine(items, context),
        LeanTargetObjectRepresentation::Collection {
            constructor: LeanTargetCollectionObjectConstructor::SequenceLiteral,
            items,
            ..
        } => Ok(format!(
            "(Litex.SequenceLiteral.mk {})",
            render_typed_spine(items, context)?
        )),
        LeanTargetObjectRepresentation::Collection {
            constructor: LeanTargetCollectionObjectConstructor::ListSet,
            items,
            ..
        } => render_list_set(items, context),
    }
}

pub(super) fn render_list_set(
    items: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut set = "Litex.Set.empty".to_string();
    for item in items.iter().rev() {
        set = format!(
            "(Litex.Set.coproduct (Litex.Set.singleton {}) {set})",
            render_lean_source_for_target_object_representation(item, context)?
        );
    }
    Ok(set)
}

/// Build the exact carrier bridge needed to consume a complex-binder forall
/// Result as a heterogeneous Lean `Subset`. This first reviewed constructor
/// is deliberately limited to finite source list sets whose elements already
/// have direct Complex representations in the active compiler environment.
pub(super) fn render_proof_that_every_set_carrier_value_has_a_complex_representative(
    set: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Obj::ListSet(list_set) = set else {
        return Err(format!(
            "by-extension set `{set}` has no reviewed carrier-to-complex representation proof"
        ));
    };
    let mut proof = "Litex.Set.emptyEveryCarrierValueHasComplexRepresentative".to_string();
    for item in list_set.list.iter().rev() {
        let rendered_item =
            render_source_object_as_direct_complex_value_for_set_carrier(item.as_ref(), context)?;
        proof = format!(
            "Litex.Set.coproductEveryCarrierValueHasComplexRepresentative (Litex.Set.singletonEveryCarrierValueHasComplexRepresentative {rendered_item}) ({proof})"
        );
    }
    Ok(proof)
}

pub(super) fn render_source_object_as_direct_complex_value_for_set_carrier(
    object: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(object)
    {
        if context.numeric_representations.contains_key(&symbol_id) {
            return render_numeric_obj(object, context);
        }
    }
    match object {
        Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::Add(_)
        | Obj::Sub(_)
        | Obj::Mul(_)
        | Obj::Div(_)
        | Obj::Mod(_)
        | Obj::Pow(_) => render_obj(object, context),
        _ => Err(format!(
            "set carrier item `{object}` has no direct Complex representation in the current compiler environment"
        )),
    }
}

pub(super) fn render_list_set_finiteness(
    items: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut set = "Litex.Set.empty".to_string();
    let mut proof = "Litex.Set.empty_finite".to_string();
    for item in items.iter().rev() {
        let item = render_lean_source_for_target_object_representation(item, context)?;
        proof = format!(
            "Litex.Set.coproduct_finite (Litex.Set.singleton {item}) {set} (Litex.Set.singleton_finite {item}) ({proof})"
        );
        set = format!("(Litex.Set.coproduct (Litex.Set.singleton {item}) {set})");
    }
    Ok(proof)
}

pub(super) fn render_integer_endpoint(
    object: &LeanTargetObjectRepresentation,
    _context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let LeanTargetObjectRepresentation::Number { normalized_value } = object else {
        return Err("integer range endpoints currently require closed integer numerals".into());
    };
    if normalized_value.parse::<i128>().is_err() {
        return Err(format!(
            "integer range endpoint `{normalized_value}` is not a closed integer numeral"
        ));
    }
    Ok(format!("({normalized_value} : ℤ)"))
}

pub(super) fn render_natural_endpoint(
    object: &LeanTargetObjectRepresentation,
) -> Result<String, String> {
    let LeanTargetObjectRepresentation::Number { normalized_value } = object else {
        return Err("finite sequence length currently requires a closed natural numeral".into());
    };
    if normalized_value.is_empty()
        || !normalized_value
            .chars()
            .all(|character| character.is_ascii_digit())
    {
        return Err(format!(
            "finite sequence length `{normalized_value}` is not a natural numeral"
        ));
    }
    Ok(format!("({normalized_value} : Nat)"))
}

pub(super) fn render_typed_spine(
    items: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let mut tail = "Litex.HNil.nil".to_string();
    for item in items.iter().rev() {
        tail = format!(
            "(Litex.HCons.mk {} {tail})",
            render_lean_source_for_target_object_representation(item, context)?
        );
    }
    Ok(tail)
}

pub(super) fn render_aggregate_object(
    kind: LeanTargetAggregateObjectConstructor,
    arguments: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (name, arity) = match kind {
        LeanTargetAggregateObjectConstructor::Sum => ("Litex.sum", 3),
        LeanTargetAggregateObjectConstructor::Product => ("Litex.product", 3),
        LeanTargetAggregateObjectConstructor::FiniteSetSum => ("Litex.finiteSetSum", 2),
        LeanTargetAggregateObjectConstructor::FiniteSetProduct => ("Litex.finiteSetProduct", 2),
        LeanTargetAggregateObjectConstructor::Reduce => ("Litex.reduce", 5),
        LeanTargetAggregateObjectConstructor::FiniteSetReduce => ("Litex.finiteSetReduce", 4),
    };
    if arguments.len() != arity {
        return Err(format!(
            "aggregate `{kind:?}` changed its exact source arity"
        ));
    }
    let rendered = arguments
        .iter()
        .map(|argument| render_lean_source_for_target_object_representation(argument, context))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!("({name} {})", rendered.join(" ")))
}

pub(super) fn render_literal_indexed_access(
    object: &LeanTargetObjectRepresentation,
    index: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } = object {
        if let Some(binding) = context.indexed_tuple_bindings.get(symbol_id) {
            let tuple = render_lean_source_for_target_object_representation(object, context)?;
            let exact_index = match index {
                LeanTargetObjectRepresentation::Symbol {
                    symbol_id: index_symbol_id,
                    ..
                } => context
                    .exact_tuple_indices
                    .get(index_symbol_id)
                    .cloned()
                    .ok_or_else(|| {
                        "indexed tuple projection has no exact checked index representative"
                            .to_string()
                    })?,
                LeanTargetObjectRepresentation::Number { normalized_value } => {
                    let value = normalized_value.parse::<usize>().map_err(|_| {
                        "indexed tuple projection index is not a natural numeral".to_string()
                    })?;
                    if value == 0 || value > binding.dimension {
                        return Err(
                            "indexed tuple projection index is outside its checked dimension"
                                .into(),
                        );
                    }
                    format!("⟨({value} : ℤ), by norm_num⟩")
                }
                _ => {
                    return Err(
                        "indexed tuple projection needs a checked range representative".into(),
                    );
                }
            };
            return Ok(format!("(Litex.indexedTupleAt {tuple} {exact_index})"));
        }
    }
    let LeanTargetObjectRepresentation::Number { normalized_value } = index else {
        return Err("literal tuple access requires a closed natural index".into());
    };
    let index = normalized_value
        .parse::<usize>()
        .map_err(|_| "literal tuple access has an invalid natural index".to_string())?;
    let LeanTargetObjectRepresentation::Collection { items, .. } = object else {
        return Err(
            "generic heterogeneous indexed access needs a checked projection recipe".into(),
        );
    };
    let item = items.get(index.saturating_sub(1)).ok_or_else(|| {
        "literal tuple access index is outside the retained source arity".to_string()
    })?;
    render_lean_source_for_target_object_representation(item, context)
}

pub(super) fn render_builtin_object(
    operator: LeanTargetBuiltinObjectOperator,
    arguments: &[LeanTargetObjectRepresentation],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let binary_symbol = match operator {
        LeanTargetBuiltinObjectOperator::Add => Some("+"),
        LeanTargetBuiltinObjectOperator::Sub => Some("-"),
        LeanTargetBuiltinObjectOperator::Mul => Some("*"),
        LeanTargetBuiltinObjectOperator::Div => Some("/"),
        _ => None,
    };
    if let Some(symbol) = binary_symbol {
        let [left, right] = arguments else {
            return Err(format!("numeric operator `{operator:?}` changed its arity"));
        };
        return Ok(format!(
            "({} {symbol} {})",
            render_lean_source_for_numeric_target_object_representation(left, context)?,
            render_lean_source_for_numeric_target_object_representation(right, context)?
        ));
    }
    match (operator, arguments) {
        (LeanTargetBuiltinObjectOperator::Union, [left, right]) => Ok(format!(
            "(Litex.union {} {})",
            render_lean_source_for_target_object_representation(left, context)?,
            render_lean_source_for_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::Intersect, [left, right]) => Ok(format!(
            "(Litex.intersect {} {})",
            render_lean_source_for_target_object_representation(left, context)?,
            render_lean_source_for_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::SetMinus, [left, right]) => Ok(format!(
            "(Litex.setMinus {} {})",
            render_lean_source_for_target_object_representation(left, context)?,
            render_lean_source_for_target_object_representation(right, context)?
        )),
        (LeanTargetBuiltinObjectOperator::BigUnion, [family]) => Ok(format!(
            "(Litex.bigUnion {})",
            render_lean_source_for_target_object_representation(family, context)?
        )),
        (LeanTargetBuiltinObjectOperator::BigIntersect, [family]) => Ok(format!(
            "(Litex.bigIntersect {})",
            render_lean_source_for_target_object_representation(family, context)?
        )),
        (LeanTargetBuiltinObjectOperator::PowerSet, [base]) => Ok(format!(
            "(Litex.powerSet {})",
            render_lean_source_for_target_object_representation(base, context)?
        )),
        _ => Err(format!(
            "unsupported typed builtin object `{operator:?}` with {} arguments",
            arguments.len()
        )),
    }
}

pub(super) fn render_lean_source_for_numeric_target_object_representation(
    object: &LeanTargetObjectRepresentation,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } = object {
        if let Some(value) = context.numeric_representations.get(symbol_id) {
            return Ok(value.clone());
        }
    }
    render_lean_source_for_target_object_representation(object, context)
}

pub(super) fn parameter_set(param_type: &ParamType) -> Result<&Obj, String> {
    match param_type {
        ParamType::Obj(set) => Ok(set),
        _ => Err(format!(
            "unsupported compiler parameter type `{param_type}`"
        )),
    }
}

pub(super) fn render_lean_source_for_standard_set_representation(
    set: LeanTargetStandardSet,
) -> Result<String, String> {
    let name = match set {
        LeanTargetStandardSet::PositiveNatural => "Litex.NPos",
        LeanTargetStandardSet::Natural => "Litex.N",
        LeanTargetStandardSet::Integer => "Litex.Z",
        LeanTargetStandardSet::Rational => "Litex.Q",
        LeanTargetStandardSet::Real => "Litex.R",
        LeanTargetStandardSet::Complex => "Litex.C",
        LeanTargetStandardSet::PositiveRational => "Litex.QPos",
        LeanTargetStandardSet::PositiveReal => "Litex.RPos",
        LeanTargetStandardSet::NegativeInteger => "Litex.ZNeg",
        LeanTargetStandardSet::NegativeRational => "Litex.QNeg",
        LeanTargetStandardSet::NegativeReal => "Litex.RNeg",
        LeanTargetStandardSet::NonzeroInteger => "Litex.ZStar",
        LeanTargetStandardSet::NonzeroRational => "Litex.QStar",
        LeanTargetStandardSet::NonzeroReal => "Litex.RStar",
        LeanTargetStandardSet::NonzeroComplex => "Litex.CStar",
    };
    Ok(name.into())
}

pub(super) fn render_normalized_complex_number(normalized_value: &str) -> Result<String, String> {
    let unsigned = normalized_value
        .strip_prefix('-')
        .unwrap_or(normalized_value);
    let mut decimal_parts = unsigned.split('.');
    let integer = decimal_parts.next().unwrap_or_default();
    let fractional = decimal_parts.next();
    let is_normalized_decimal = !integer.is_empty()
        && integer.chars().all(|character| character.is_ascii_digit())
        && fractional.is_none_or(|digits| {
            !digits.is_empty() && digits.chars().all(|character| character.is_ascii_digit())
        })
        && decimal_parts.next().is_none();
    if !is_normalized_decimal {
        return Err(format!(
            "compiler received invalid normalized numeric literal `{normalized_value}`"
        ));
    }
    Ok(format!("({normalized_value} : ℂ)"))
}

pub(super) fn render_standard_set(set: StandardSet) -> Result<&'static str, String> {
    match set {
        StandardSet::N => Ok("Litex.N"),
        StandardSet::NPos => Ok("Litex.NPos"),
        StandardSet::Z => Ok("Litex.Z"),
        StandardSet::ZStar => Ok("Litex.ZStar"),
        StandardSet::Q => Ok("Litex.Q"),
        StandardSet::QPos => Ok("Litex.QPos"),
        StandardSet::QNeg => Ok("Litex.QNeg"),
        StandardSet::QStar => Ok("Litex.QStar"),
        StandardSet::R => Ok("Litex.R"),
        StandardSet::RPos => Ok("Litex.RPos"),
        StandardSet::RNeg => Ok("Litex.RNeg"),
        StandardSet::RStar => Ok("Litex.RStar"),
        StandardSet::C => Ok("Litex.C"),
        StandardSet::CStar => Ok("Litex.CStar"),
        StandardSet::ZNeg => Ok("Litex.ZNeg"),
    }
}

pub(super) fn membership_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(fact)) => Ok((&fact.element, &fact.set)),
        _ => Err(format!("expected membership fact, found `{fact}`")),
    }
}

pub(super) fn subset_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::SubsetFact(fact)) => Ok((&fact.left, &fact.right)),
        Fact::AtomicFact(AtomicFact::SupersetFact(fact)) => Ok((&fact.right, &fact.left)),
        _ => Err(format!("expected subset fact, found `{fact}`")),
    }
}

pub(super) fn validate_forall_fact_as_subset(
    candidate: &Fact,
    expected_subset: &Fact,
) -> Result<(), String> {
    let Fact::ForallFact(candidate) = candidate else {
        return Err("child is neither the expected subset nor a forall spelling".into());
    };
    let (expected_source, expected_target) = subset_parts(expected_subset)?;
    let parameters = candidate
        .typed_parameters
        .collect_param_bindings_with_types();
    let [parameter] = parameters.as_slice() else {
        return Err("subset forall must retain exactly one parameter".into());
    };
    let ParamType::Obj(ref parameter_set) = parameter.1 else {
        return Err("subset forall parameter has no object-set type".into());
    };
    if obj_equality_key(parameter_set) != obj_equality_key(expected_source)
        || !candidate.dom_facts.is_empty()
        || candidate.then_facts.len() != 1
    {
        return Err("subset forall changed its source, domains, or conclusion arity".into());
    }
    let conclusion = candidate.then_facts[0].clone().to_fact();
    let (element, target_set) = membership_parts(&conclusion)?;
    let expected_element = obj_for_bound_param_in_scope(&parameter.0);
    if obj_equality_key(element) != obj_equality_key(&expected_element)
        || obj_equality_key(target_set) != obj_equality_key(expected_target)
    {
        return Err("subset forall changed its bound element or target set".into());
    }
    Ok(())
}

/// Returns the semantic subset orientation `(source, target)`, whether the
/// relation is negated, and whether the source used subset rather than
/// superset spelling.
pub(super) fn normalized_set_relation_parts(
    fact: &Fact,
) -> Result<(&Obj, &Obj, bool, bool), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::SubsetFact(fact)) => {
            Ok((&fact.left, &fact.right, false, true))
        }
        Fact::AtomicFact(AtomicFact::SupersetFact(fact)) => {
            Ok((&fact.right, &fact.left, false, false))
        }
        Fact::AtomicFact(AtomicFact::NotSubsetFact(fact)) => {
            Ok((&fact.left, &fact.right, true, true))
        }
        Fact::AtomicFact(AtomicFact::NotSupersetFact(fact)) => {
            Ok((&fact.right, &fact.left, true, false))
        }
        _ => Err(format!("expected a set relation, found `{fact}`")),
    }
}

pub(super) fn finite_set_parts(fact: &Fact) -> Result<&Obj, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::IsFiniteSetFact(fact)) => Ok(&fact.set),
        _ => Err(format!("expected finite-set fact, found `{fact}`")),
    }
}

pub(super) fn nonempty_set_parts(fact: &Fact) -> Result<&Obj, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) => Ok(&fact.set),
        _ => Err(format!("expected nonempty-set fact, found `{fact}`")),
    }
}

pub(super) fn nonmembership_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotInFact(fact)) => Ok((&fact.element, &fact.set)),
        _ => Err(format!("expected non-membership fact, found `{fact}`")),
    }
}

pub(super) fn equality_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected equality fact, found `{fact}`")),
    }
}

pub(super) fn not_equal_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotEqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected not-equality fact, found `{fact}`")),
    }
}

pub(super) fn positive_order_parts(fact: &Fact, strict: bool) -> Result<(&Obj, &Obj), String> {
    match (strict, fact) {
        (true, Fact::AtomicFact(AtomicFact::LessFact(fact))) => Ok((&fact.left, &fact.right)),
        (true, Fact::AtomicFact(AtomicFact::GreaterFact(fact))) => Ok((&fact.right, &fact.left)),
        (false, Fact::AtomicFact(AtomicFact::LessEqualFact(fact))) => Ok((&fact.left, &fact.right)),
        (false, Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact))) => {
            Ok((&fact.right, &fact.left))
        }
        (true, _) => Err(format!(
            "expected strict positive-order fact, found `{fact}`"
        )),
        (false, _) => Err(format!(
            "expected non-strict positive-order fact, found `{fact}`"
        )),
    }
}

pub(super) fn order_relation_parts(fact: &Fact) -> Result<(&Obj, &Obj, bool), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::LessFact(fact)) => Ok((&fact.left, &fact.right, true)),
        Fact::AtomicFact(AtomicFact::GreaterFact(fact)) => Ok((&fact.right, &fact.left, true)),
        Fact::AtomicFact(AtomicFact::LessEqualFact(fact)) => Ok((&fact.left, &fact.right, false)),
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact)) => {
            Ok((&fact.right, &fact.left, false))
        }
        _ => Err(format!(
            "expected positive ordered relation, found `{fact}`"
        )),
    }
}

pub(super) fn is_literal_zero(object: &Obj) -> bool {
    matches!(object, Obj::Number(number) if number.normalized_value == "0")
}

pub(super) fn addition_parts(object: &Obj) -> Result<(&Obj, &Obj), String> {
    let Obj::Add(addition) = object else {
        return Err(format!("expected an addition object, found `{object}`"));
    };
    Ok((addition.left.as_ref(), addition.right.as_ref()))
}

pub(super) fn conjunction(facts: &[String]) -> String {
    match facts {
        [] => "True".to_string(),
        [only] => only.clone(),
        _ => facts.join(" ∧ "),
    }
}

pub(super) fn conjunction_components(fact: &Fact) -> Result<Vec<Fact>, String> {
    match fact {
        Fact::AndFact(and_fact) => Ok(and_fact.facts.iter().cloned().map(Fact::from).collect()),
        Fact::ChainFact(chain_fact) => chain_fact
            .facts()
            .map(|facts| facts.into_iter().map(Fact::from).collect())
            .map_err(|error| format!("invalid retained relation chain: {error:?}")),
        _ => Err(format!(
            "expected conjunction or relation chain, found `{fact}`"
        )),
    }
}

pub(super) fn disjunction_components(fact: &Fact) -> Result<Vec<Fact>, String> {
    let Fact::OrFact(or_fact) = fact else {
        return Err(format!("expected disjunction, found `{fact}`"));
    };
    Ok(or_fact.facts.iter().cloned().map(Fact::from).collect())
}

pub(super) fn right_associated_conjunction_proof(proofs: &[String]) -> Result<String, String> {
    let Some(last) = proofs.last() else {
        return Err("conjunction introduction retained no component proofs".into());
    };
    let mut result = last.clone();
    for proof in proofs[..proofs.len() - 1].iter().rev() {
        result = format!("⟨{proof}, {result}⟩");
    }
    Ok(result)
}

pub(super) fn right_associated_disjunction_injection(
    proof: String,
    selected_index: usize,
    count: usize,
) -> Result<String, String> {
    if count == 0 || selected_index >= count {
        return Err("disjunction introduction selected an out-of-range branch".into());
    }
    if count == 1 {
        return Ok(proof);
    }
    let mut result = if selected_index + 1 < count {
        format!("Or.inl ({proof})")
    } else {
        proof
    };
    for _ in 0..selected_index {
        result = format!("Or.inr ({result})");
    }
    Ok(result)
}

pub(super) fn conjunction_projection(
    source: &str,
    index: usize,
    count: usize,
) -> Result<String, String> {
    if count == 0 || index >= count {
        return Err("conjunction projection selected an out-of-range component".into());
    }
    if count == 1 {
        return Ok(source.to_string());
    }
    let mut projection = source.to_string();
    for _ in 0..index {
        projection.push_str(".2");
    }
    if index + 1 < count {
        projection.push_str(".1");
    }
    Ok(projection)
}

pub(super) fn lean_identifier(source: &str) -> String {
    let mut result = source
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    if result.is_empty() {
        result.push('_');
    }
    result
}

pub(super) fn indent_lines(text: &str, spaces: usize) -> String {
    let indentation = " ".repeat(spaces);
    text.lines()
        .map(|line| format!("{indentation}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}
