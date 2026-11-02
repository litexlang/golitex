use crate::execute::execute_def_struct_stmt::{ExecDefStructStmtFailed, ExecDefStructStmtResult};
use crate::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

#[test]
fn struct_ordered_conditions_can_use_prior_conditions_and_stay_local() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/stmt_nodes/definition/struct_ordered_conditions.lit"
        ))
        .unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        ExecDefStructStmtResult::Success(s),
    )) = &run.statement_results[0]
    else {
        panic!("struct failed")
    };
    assert_eq!(s.field_scope.equivalent_facts.len(), 2);
    for proof in &s.field_scope.equivalent_facts {
        assert!(s
            .field_scope
            .field_local_env
            .facts
            .facts_by_id
            .contains_key(&proof.store.primary_fact_id()));
        assert!(rt
            .fact_by_id_in_stack(proof.store.primary_fact_id())
            .is_none());
    }
    let detailed = format!(
        "{:?}",
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
    );
    assert!(detailed.contains("local_store"), "{detailed}");
    assert!(!rt.run_litex_code("x != 0\n").unwrap().success);
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn struct_condition_cannot_supply_its_own_or_later_wd_premise() {
    for conditions in [
        "        1 / x = 1 / x\n",
        "        1 / x = 1 / x\n        x != 0\n",
    ] {
        let mut rt = runtime();
        let code = format!("struct NonzeroCoordinate:\n    x R\n    y R\n    <=>:\n{conditions}");
        let run = rt.run_litex_code(&code).unwrap();
        assert!(run.session_error.is_none(), "{:?}", run.session_error);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
            ExecDefStructStmtResult::Failed(ExecDefStructStmtFailed::Local(local)),
        )) = &run.statement_results[0]
        else {
            panic!("expected retained struct failure")
        };
        let crate::execute::DefStructLocalFailed::Fields { field_failure, .. } = &local.failure
        else {
            panic!("expected field-scope failure")
        };
        let crate::execute::DefStructFieldLocalFailed::Condition {
            fields,
            equivalent_facts,
            ..
        } = &field_failure.failure
        else {
            panic!("expected condition WD failure")
        };
        assert_eq!(fields.len(), 2);
        assert!(
            equivalent_facts.is_empty(),
            "a condition cannot justify its own WD"
        );
        assert!(rt
            .def_struct_visible_in_stack("NonzeroCoordinate")
            .is_none());
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(rt.run_litex_code("struct NonzeroCoordinate:\n    x R\n    y R\n    <=>:\n        x != 0\n        1 / x = 1 / x\n").unwrap().success);
    }
}
