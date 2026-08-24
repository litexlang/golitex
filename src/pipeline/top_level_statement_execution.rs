use super::record_pipeline_step;
use crate::error::{short_exec_error, RuntimeError};
use crate::infer::SuccessInferResult;
use crate::module_manager::{
    discover_isolated_module_import, discover_isolated_std_import, ImportTarget, ModuleStatus,
};
use crate::result::{
    StmtResult, SuccessCommandStmtResult, SuccessExecutedImportResult,
    SuccessImportExecutionResult, SuccessImportStmtResult, SuccessReusedImportResult,
    SuccessStmtCommonResult,
};
use crate::runtime::{ExecutionMode, Runtime};
use crate::stmt::tooling_stmt::ImportStmt;
use crate::stmt::{CommandStmt, Stmt};

pub fn execute_top_level_statement(
    stmt: &Stmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    record_pipeline_step(
        "execute",
        "pipeline::execute_top_level_statement",
        "src/pipeline/top_level_statement_execution.rs",
    );
    match stmt {
        Stmt::Command(CommandStmt::ImportStmt(import)) => {
            let result = run_isolated_import(import, runtime);
            runtime.finish_statement_execution(result, ExecutionMode::Verified)
        }
        _ => runtime.execute_statement(stmt),
    }
}

pub fn execute_top_level_statement_in_trusted_prefix_run(
    stmt: &Stmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    match stmt {
        Stmt::Command(CommandStmt::ImportStmt(import)) => {
            let result = run_isolated_import(import, runtime);
            runtime
                .finish_statement_execution_in_trusted_prefix_run(result, ExecutionMode::Verified)
        }
        _ => runtime.execute_statement_in_trusted_prefix_run(stmt),
    }
}

fn run_isolated_import(
    import: &ImportStmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    if !runtime.current_source_allows_inline_imports() {
        return Err(short_exec_error(
            import.clone().into(),
            "source import is only available in an isolated terminal".to_string(),
            None,
            vec![],
        ));
    }

    let module_manager_before = runtime.module_manager.clone();
    let discovery = match import {
        ImportStmt::Module(stmt) => discover_isolated_module_import(
            runtime,
            stmt.path.as_str(),
            stmt.alias.as_str(),
            stmt.line_file.clone(),
        ),
        ImportStmt::Std(stmt) => {
            discover_isolated_std_import(runtime, stmt.name.as_str(), stmt.line_file.clone())
        }
    };
    let module_id = match discovery {
        Ok(module_id) => module_id,
        Err(error) => {
            runtime.module_manager = module_manager_before;
            return Err(error);
        }
    };
    let import_target = ImportTarget::Module(module_id);
    let execution_mode = if runtime.strict_mode {
        ExecutionMode::Verified
    } else {
        let name = runtime
            .module_manager
            .canonical_name_for_target(import_target)
            .unwrap_or("isolated import")
            .to_string();
        let kind = match import {
            ImportStmt::Module(_) => "isolated_import",
            ImportStmt::Std(_) => "isolated_std_import",
        };
        runtime.record_unverified_import(kind, name, import.line_file());
        ExecutionMode::Trusted
    };
    let module_status_before = runtime
        .module_manager
        .module(module_id)
        .expect("discovered import module should be registered")
        .status;
    let (statement_results, runtime_error) =
        super::repository_execution::run_repository_module_target_with_mode(
            runtime,
            module_id,
            execution_mode,
            None,
        );
    if let Some(error) = runtime_error {
        runtime.module_manager = module_manager_before;
        return Err(error);
    }
    let execution = if module_status_before == ModuleStatus::Loaded {
        SuccessImportExecutionResult::Reused(SuccessReusedImportResult {
            module_id,
            execution_mode,
        })
    } else {
        SuccessImportExecutionResult::Executed(Box::new(SuccessExecutedImportResult {
            module_id,
            execution_mode,
            statement_results,
        }))
    };
    Ok(
        SuccessCommandStmtResult::ImportStmt(Box::new(SuccessImportStmtResult {
            statement: import.clone(),
            common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
            execution,
        }))
        .into(),
    )
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/top_level_statement_execution/path_import_tests.rs"]
mod path_import_tests;
