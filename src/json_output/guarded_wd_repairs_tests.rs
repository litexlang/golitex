use super::{project_stmt_detailed, project_stmt_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn field<'a>(value: &'a JsonValue, key: &str, language: OutputLanguage) -> &'a JsonValue {
    value
        .as_object()
        .unwrap()
        .get(&super::json_keys::localize_key(key, language))
        .unwrap_or_else(|| panic!("missing {key}: {value:?}"))
}

#[test]
fn def_prop_wd_failure_preserves_the_actual_stage_and_obligation_in_both_profiles() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (source, stage, obligation) in [
            ("prop broken(x R):\n    1 / 0 = x\n", "iff_fact_well_defined", "0 != 0"),
            ("prop broken(x {1 / 0}):\n    x = x\n", "parameter_type", "0 != 0"),
            ("prop broken(x R):\n    not forall y R:\n        y = y\n        =>:\n            1 / y != 1 / y\n", "iff_fact_well_defined", "y != 0"),
        ] {
            let mut rt = Runtime::new(LaunchCommand::Eval {
                code: String::new(), session: false, strict: true, language,
            });
            let run = rt.run_litex_code(source).unwrap();
            assert!(run.session_error.is_none(), "{:?}", run.session_error);
            let result = &run.statement_results[0];
            assert!(result.is_failed());
            let normal = project_stmt_normal(result, &rt);
            let detailed = project_stmt_detailed(result, &rt);
            let normal_failure = field(field(&normal, "why_failed", language), "failure", language);
            let detailed_failure = field(&detailed, "failure", language);
            assert_eq!(normal_failure, detailed_failure, "same runtime evidence in both profiles");
            assert_eq!(field(normal_failure, "phase", language).as_str(), Ok(stage));
            assert!(normal_failure.stringify().contains(obligation), "{}", normal_failure.stringify());
            for key in ["stores", "infers"] {
                assert!(field(&normal, key, language).as_array().unwrap().is_empty());
            }
            let reuse = rt.run_litex_code("prop broken(x R):\n    x = x\n").unwrap();
            assert!(reuse.success && reuse.session_error.is_none(), "failed definition must roll back");
        }
    }
}
