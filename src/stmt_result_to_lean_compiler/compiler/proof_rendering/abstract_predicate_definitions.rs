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
    let mut carrier_binders = Vec::with_capacity(parameter_names.len());
    let mut argument_binders = Vec::with_capacity(parameter_names.len());
    for (index, parameter_name) in parameter_names.iter().enumerate() {
        let suffix = index + 1;
        let universe = format!("u__{name}_{suffix}");
        let carrier = format!("__abstract_carrier{suffix}");
        universe_names.push(universe.clone());
        carrier_binders.push(format!("{{{carrier} : Type {universe}}}"));
        argument_binders.push(format!("({} : {carrier})", lean_identifier(parameter_name)));
    }
    let universe_declaration = if universe_names.is_empty() {
        String::new()
    } else {
        format!("universe {}\n", universe_names.join(" "))
    };
    let (lean_name, same_congruence_name) = if parameter_names.is_empty() {
        declarations.push(format!("{universe_declaration}axiom {name} : Prop"));
        (name.clone(), None)
    } else {
        let specification_name = format!("__LitexAbstractPredicate_{name}");
        let source_carriers = parameter_names
            .iter()
            .enumerate()
            .map(|(index, _)| {
                format!(
                    "{{__source_carrier{} : Type {}}}",
                    index + 1,
                    universe_names[index]
                )
            })
            .collect::<Vec<_>>();
        let target_carriers = parameter_names
            .iter()
            .enumerate()
            .map(|(index, _)| {
                format!(
                    "{{__target_carrier{} : Type {}}}",
                    index + 1,
                    universe_names[index]
                )
            })
            .collect::<Vec<_>>();
        let observer_binders = parameter_names
            .iter()
            .enumerate()
            .flat_map(|(index, _)| {
                let suffix = index + 1;
                [
                    format!("[Litex.ComplexObserver __source_carrier{suffix}]"),
                    format!("[Litex.ComplexObserver __target_carrier{suffix}]"),
                ]
            })
            .collect::<Vec<_>>();
        let source_arguments = parameter_names
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let suffix = index + 1;
                format!("(__source{suffix} : __source_carrier{suffix})")
            })
            .collect::<Vec<_>>();
        let target_arguments = parameter_names
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let suffix = index + 1;
                format!("(__target{suffix} : __target_carrier{suffix})")
            })
            .collect::<Vec<_>>();
        let same_arguments = parameter_names
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let suffix = index + 1;
                format!("Litex.Same __source{suffix} __target{suffix}")
            })
            .collect::<Vec<_>>();
        let source_application = (1..=parameter_names.len())
            .map(|index| format!("__source{index}"))
            .collect::<Vec<_>>()
            .join(" ");
        let target_application = (1..=parameter_names.len())
            .map(|index| format!("__target{index}"))
            .collect::<Vec<_>>()
            .join(" ");
        declarations.push(format!(
            "{universe_declaration}structure {specification_name} where\n  holds : {} → {} → Prop\n  respectsSame :\n    {} →\n    {} →\n    {} →\n    {} →\n    {} →\n    {} →\n    (holds {source_application} ↔ holds {target_application})\n\naxiom {name} : {specification_name}",
            carrier_binders.join(" → "),
            argument_binders.join(" → "),
            source_carriers.join(" → "),
            target_carriers.join(" → "),
            observer_binders.join(" → "),
            source_arguments.join(" → "),
            target_arguments.join(" → "),
            same_arguments.join(" → "),
        ));
        (
            format!("{name}.holds"),
            Some(format!("{name}.respectsSame")),
        )
    };
    context.predicate_bindings.insert(
        source_name.to_string(),
        PredicateBinding {
            lean_name,
            same_congruence_name,
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
