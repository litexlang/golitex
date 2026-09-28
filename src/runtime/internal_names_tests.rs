use crate::launch_command::LaunchCommand;
use crate::runtime::internal_names::{
    format_internal_fact_name, format_internal_param_name, INTERNAL_FACT_PREFIX,
    INTERNAL_PARAM_PREFIX,
};
use crate::runtime::Runtime;

#[test]
fn fresh_internal_param_names_match_identifier_ids() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
    });
    let a = rt.fresh_internal_param();
    let b = rt.fresh_internal_param();
    assert_ne!(a.id, b.id);
    assert_eq!(a.name, format_internal_param_name(a.id));
    assert_eq!(b.name, format_internal_param_name(b.id));
    assert!(a.name.starts_with(INTERNAL_PARAM_PREFIX));
    assert!(b.name.starts_with(INTERNAL_PARAM_PREFIX));
}

#[test]
fn fresh_internal_fact_names_match_fact_ids() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
    });
    let (name, id) = rt.fresh_internal_fact_name();
    assert_eq!(name, format_internal_fact_name(id));
    assert!(name.starts_with(INTERNAL_FACT_PREFIX));
}
