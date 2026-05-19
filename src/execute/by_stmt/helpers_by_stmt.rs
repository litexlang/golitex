use crate::prelude::*;

pub(super) fn impossible_proof_error_message(
    impossible_fact: &AtomicFact,
    option_case_fact_string: Option<String>,
) -> String {
    match option_case_fact_string {
        Some(case_fact) => format!(
            "failed to prove impossible `{}` under case `{}`",
            impossible_fact, case_fact
        ),
        None => format!("failed to prove impossible `{}`", impossible_fact),
    }
}

pub(super) fn user_defined_prop_arity(rt: &Runtime, prop_name: &str) -> Option<usize> {
    if let Some(definition) = rt.get_abstract_prop_definition_by_name(prop_name) {
        return Some(definition.params.len());
    }
    if let Some(definition) = rt.get_prop_definition_by_name(prop_name) {
        return Some(definition.params_def_with_type.collect_param_names().len());
    }
    None
}
