//! Abstract predicate declarations.

use super::super::*;

pub(in super::super) fn construct_lean_source_parts_for_abstract_predicate_definition(
    source_name: &str,
    parameter_names: &[String],
    declarations: &mut Vec<String>,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    if context.predicate_bindings.contains_key(source_name) {
        return Err(format!(
            "duplicate compiler predicate definition `{}`",
            source_name
        ));
    }
    let name = lean_identifier(source_name);
    let mut universe_names = Vec::with_capacity(parameter_names.len());
    let mut binders = Vec::with_capacity(parameter_names.len() * 2);
    for (index, parameter_name) in parameter_names.iter().enumerate() {
        let suffix = index + 1;
        let universe = format!("u__{name}_{suffix}");
        let carrier = format!("__abstract_carrier{suffix}");
        universe_names.push(universe.clone());
        binders.push(format!("{{{carrier} : Type {universe}}}"));
        binders.push(format!("({} : {carrier})", lean_identifier(parameter_name)));
    }
    let universe_declaration = if universe_names.is_empty() {
        String::new()
    } else {
        format!("universe {}\n", universe_names.join(" "))
    };
    let binder_suffix = if binders.is_empty() {
        String::new()
    } else {
        format!(" {}", binders.join(" "))
    };
    declarations.push(format!(
        "{universe_declaration}axiom {name}{binder_suffix} : Prop"
    ));
    context.predicate_bindings.insert(
        source_name.to_string(),
        PredicateBinding {
            lean_name: name,
            parameter_count: parameter_names.len(),
            exact_parameters: vec![false; parameter_names.len()],
            requirement_count: 0,
            clause_count: 0,
            dependent_parameter_evidence: false,
            definition: None,
            definition_well_definedness: None,
        },
    );
    Ok(())
}
