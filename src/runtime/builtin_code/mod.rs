pub mod builtin_families;
pub mod common_comparison_properties;
pub mod common_functions;
pub mod fundamental_comparison;
pub mod set_operators;

fn concat_builtin_env_lit_fragments() -> String {
    let mut out = String::new();
    out.push_str(fundamental_comparison::BUILTIN_ENV_CODE_FOR_FUNDAMENTAL_COMPARISON);
    out.push_str(common_comparison_properties::KNOW_REAL_LINE_TRICHOTOMY);
    out.push_str(common_comparison_properties::ORDER_TRANSITIVITY_PROP_DECLS);
    out.push_str(common_comparison_properties::KNOW_ORDER_TRANSITIVITY_CHAIN);
    out.push_str(
        common_comparison_properties::BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES,
    );
    out.push_str(common_functions::BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS);
    out.push_str(builtin_families::BUILTIN_ENV_CODE_FOR_BUILTIN_FAMILIES);
    out.push_str(set_operators::BUILTIN_ENV_CODE_FOR_SET_OPERATORS);
    out
}

pub fn builtin_code() -> String {
    concat_builtin_env_lit_fragments()
}
