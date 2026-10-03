use crate::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::execute::execute_def_struct_stmt::{ExecDefStructStmtFailed, ExecDefStructStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    })
}

#[test]
fn dependent_struct_fields_check_then_bind_and_keep_evidence_local() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!("../../../../examples/wd/struct_dependent_fields.lit")).unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(ExecDefStructStmtResult::Success(s))) = &run.statement_results[0] else { panic!("struct failed") };
    assert_eq!(s.field_scope.fields.len(), 2);
    for field in &s.field_scope.fields {
        assert!(!field.defined.stored_fact_ids.is_empty());
        for id in &field.defined.stored_fact_ids {
            assert!(s.field_scope.field_local_env.facts.facts_by_id.contains_key(id));
            assert!(rt.fact_by_id_in_stack(*id).is_none());
        }
    }
    let detailed = format!("{:?}", crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt));
    assert!(detailed.contains("local_definition"), "{detailed}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("point $in R").unwrap().success);
}

#[test]
fn dependent_struct_fields_reject_forward_and_self_references() {
    for fields in ["    at fn(x R: x = point) R\n    point R", "    point {point}\n    tag N"] {
        let mut rt = runtime();
        let run = rt.run_litex_code(&format!("struct Bad:\n{fields}")).unwrap();
        assert!(!run.success, "{fields}");
        assert!(rt.def_struct_visible_in_stack("Bad").is_none());
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn dependent_struct_fields_rollback_a_later_invalid_type() {
    let mut rt = runtime();
    let run = rt.run_litex_code("struct Bad:\n    point R\n    at fn(x R: 1 / 0 = x) R").unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(matches!(&run.statement_results[0], ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(ExecDefStructStmtResult::Failed(ExecDefStructStmtFailed::FieldType(_))))));
    assert!(rt.def_struct_visible_in_stack("Bad").is_none());
    assert!(!rt.run_litex_code("point = point").unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(rt.run_litex_code("struct Bad:\n    point R\n    at fn(x R: x = point) R").unwrap().success);
}

#[test]
fn dependent_struct_fields_do_not_erase_guards_carriers_or_laws() {
    for goal in ["s.at(0) = s.at(0)", "s.at(i) = s.at(i)", "s.at(s.point) = 42"] {
        let mut rt = runtime();
        assert!(rt.run_litex_code("struct Guarded:\n    point R\n    at fn(x R: x = point) R").unwrap().success);
        let run = rt.run_litex_code(&format!("thm bad:\n    ? forall s &Guarded:\n        {goal}")).unwrap();
        assert!(!run.success, "{goal}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(!rt.run_litex_code("0 = 1").unwrap().success);
    }
    let mut rt = runtime();
    assert!(rt.run_litex_code("struct CarrierValue:\n    carrier power_set(R)\n    value carrier").unwrap().success);
    assert!(!rt.run_litex_code("({0}, 1) $in &CarrierValue").unwrap().success);
}

#[test]
fn forall_wd_releases_only_direct_struct_laws_and_keeps_them_local() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("struct NonzeroPoint:\n    point R\n    call fn(x R: x != 0) R\n    <=>:\n        point != 0").unwrap().success);
    let run = rt.run_litex_code("thm call_at_point:\n    ? forall s &NonzeroPoint:\n        s.call(s.point) = s.call(s.point)").unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let detailed = format!("{:?}", crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt));
    assert!(detailed.contains("auto_opened_struct_layers"), "{detailed}");
    assert!(!rt.run_litex_code("thm bad:\n    ? forall s &NonzeroPoint:\n        s.call(0) = s.call(0)").unwrap().success);
    assert!(rt.run_litex_code("struct Nested:\n    inner &NonzeroPoint\n    tag N").unwrap().success);
    assert!(!rt.run_litex_code("thm nested_guard:\n    ? forall s &Nested:\n        s.inner.call(s.inner.point) = s.inner.call(s.inner.point)").unwrap().success);
    assert!(!rt.run_litex_code("0 != 0").unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
