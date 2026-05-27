pub mod common_comparison_properties;
pub mod common_facts;
pub mod common_functions;
pub mod fundamental_comparison;
pub mod fundamental_number_properties;
pub mod set_operators;

fn concat_builtin_env_lit_fragments() -> String {
    let mut out = String::new();
    out.push_str(fundamental_comparison::BUILTIN_ENV_CODE_FOR_FUNDAMENTAL_COMPARISON);
    out.push_str(common_comparison_properties::KNOW_REAL_LINE_TRICHOTOMY);
    out.push_str(common_comparison_properties::ORDER_TRANSITIVITY_THMS);
    out.push_str(common_comparison_properties::BUILTIN_ENV_CODE_FOR_COMMON_COMPARISON_PROPERTIES);
    out.push_str(common_functions::BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS);
    out.push_str(common_facts::COMMON_FACTS);
    out.push_str(fundamental_number_properties::FUNDAMENTAL_NUMBER_PROPERTIES);
    out.push_str(set_operators::BUILTIN_ENV_CODE_FOR_SET_OPERATORS);
    out
}

pub fn builtin_code() -> String {
    concat_builtin_env_lit_fragments()
}
