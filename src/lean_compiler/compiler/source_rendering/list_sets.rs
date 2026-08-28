//! Finite list-set values, finiteness, and carrier representatives.

use super::super::*;

pub(in super::super) fn render_list_set(
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
pub(in super::super) fn render_proof_that_every_set_carrier_value_has_a_complex_representative(
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

pub(in super::super) fn render_source_object_as_direct_complex_value_for_set_carrier(
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

pub(in super::super) fn render_list_set_finiteness(
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
