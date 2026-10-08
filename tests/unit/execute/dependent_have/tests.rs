use crate::execute::execute_have_obj_equal_stmt::{
    ExecHaveObjEqualStmtFailed, ExecHaveObjEqualStmtResult,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::{
    ExecHaveObjInNonemptySetStmtFailed, ExecHaveObjInNonemptySetStmtResult,
};
use crate::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict,
        language: OutputLanguage::English,
    })
}

#[test]
fn dependent_have_telescope_and_equal_rhs_carriers_succeed() {
    let mut rt = runtime(true);
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/stmt_nodes/definition/dependent_have.lit"
        ))
        .unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let detail = format!(
        "{:?}",
        crate::json_output::project_stmt_detailed(&run.statement_results[2], &rt)
    );
    assert!(detail.contains("membership_checks"), "{detail}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn dependent_have_requires_nonempty_before_defining_its_own_witness() {
    let mut rt = runtime(true);
    let run = rt.run_litex_code("have A set, x A\n").unwrap();
    assert!(run.session_error.is_none());
    assert!(matches!(
        &run.statement_results[0],
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            crate::execute::ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Failed(
                    ExecHaveObjInNonemptySetStmtFailed::NonemptyCheck(_)
                )
            )
        ))
    ));
    assert!(
        rt.run_litex_code("have A nonempty_set, x A\nx $in A\n")
            .unwrap()
            .success
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn dependent_have_equal_rejects_later_mismatch_and_rolls_back_all_bindings() {
    let mut rt = runtime(true);
    let run = rt
        .run_litex_code("have A set, x A, n N = R, 0, -1\n")
        .unwrap();
    assert!(run.session_error.is_none());
    assert!(matches!(
        &run.statement_results[0],
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            crate::execute::ExecDefineObjStmtResult::HaveObjEqual(
                ExecHaveObjEqualStmtResult::Failed(ExecHaveObjEqualStmtFailed::Membership(_))
            )
        ))
    ));
    assert!(
        rt.run_litex_code("have A set, x A, n N = R, 0, 1\nx = 0\nn = 1\n")
            .unwrap()
            .success
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn dependent_trust_have_preserves_the_current_wd_gate_and_strict_rejection() {
    let code = "trust have A nonempty_set, x A:\n    x = x\nx $in A\n";
    let mut rt = runtime(false);
    let run = rt.run_litex_code(code).unwrap();
    assert!(run.success, "{:?}", run.session_error);
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!runtime(true).run_litex_code(code).unwrap().success);
    let mut rt = runtime(false);
    assert!(
        !rt.run_litex_code("trust have A nonempty_set, x A:\n    1 / 0 = 1 / 0\n")
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code(code).unwrap().success);
}
