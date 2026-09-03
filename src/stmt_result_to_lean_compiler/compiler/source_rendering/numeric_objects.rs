//! Integer, rational, power, and normalized numeric object rendering.

use super::super::*;

pub(in super::super) fn render_numeric_obj(
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
        Obj::Sum(_) => Ok(format!("(({} : ℤ) : ℂ)", render_obj(obj, context)?)),
        _ => render_obj(obj, context),
    }
}

/// Render one source object in the exact integer view selected by visible
/// membership evidence. `%` is an integer-only source constructor; silently
/// applying a made-up Complex remainder operation would change its semantics.
pub(in super::super) fn render_integer_obj(
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
        Obj::Sum(_) => render_obj(obj, context),
        Obj::FnObj(_) => {
            let rendered = render_obj(obj, context)?;
            if rendered.starts_with("(Litex.fnApplyCarrier ")
                || rendered.starts_with("(Litex.fnApplySelectedCarrier ")
            {
                Ok(rendered)
            } else {
                Err(format!(
                    "function application has no exact visible integer representation for `{obj}`"
                ))
            }
        }
        _ => Err(format!(
            "integer-only compiler operator has no exact visible integer representation for `{obj}`"
        )),
    }
}

/// Render a source object in the exact real carrier selected by a checked
/// `R` membership. This is used only where the target function can receive an
/// exact carrier argument, so no heterogeneous `In.rep` choice is introduced.
pub(in super::super) fn render_real_obj(
    obj: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) =
        LeanTargetObjectRepresentation::lower(obj)
    {
        if let Some(real) = context.numeric_real_values.get(&symbol_id) {
            return Ok(real.clone());
        }
    }
    if let Obj::Atom(atom) = obj {
        if let Some(real) = atom
            .symbol_ref()
            .and_then(|symbol| context.numeric_real_values.get(&symbol.id()))
        {
            return Ok(real.clone());
        }
    }
    match obj {
        Obj::Number(number) => Ok(format!("({} : ℝ)", number.normalized_value)),
        Obj::Add(operation) => Ok(format!(
            "({} + {})",
            render_real_obj(operation.left.as_ref(), context)?,
            render_real_obj(operation.right.as_ref(), context)?
        )),
        Obj::Sub(operation) => Ok(format!(
            "({} - {})",
            render_real_obj(operation.left.as_ref(), context)?,
            render_real_obj(operation.right.as_ref(), context)?
        )),
        Obj::Mul(operation) => Ok(format!(
            "({} * {})",
            render_real_obj(operation.left.as_ref(), context)?,
            render_real_obj(operation.right.as_ref(), context)?
        )),
        Obj::Div(operation) => Ok(format!(
            "({} / {})",
            render_real_obj(operation.left.as_ref(), context)?,
            render_real_obj(operation.right.as_ref(), context)?
        )),
        _ => Err(format!(
            "real-only compiler argument has no exact visible real representation for `{obj}`"
        )),
    }
}

/// Render a source object in the exact rational view selected by visible
/// membership evidence. The rational-power verifier independently retains the
/// integer exponent premise; this helper never guesses a coercion from the
/// ordinary Complex observation.
pub(in super::super) fn render_rational_obj(
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

/// Preserve the existing exact-rational power representation whenever both
/// operands have visible rational/integer views. Complex calculate adds the
/// complementary representation for a literal integral exponent whose base
/// is only available as a native complex value.
pub(in super::super) fn render_numeric_power(
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

pub(in super::super) fn render_normalized_complex_number(
    normalized_value: &str,
) -> Result<String, String> {
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
