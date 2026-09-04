use super::command::{ExecuteCommandOptions, GraphCommandOptions};
use super::json_output::{execution_target, render_artifact, render_run, simple_error};
use crate::prelude::*;
use std::fs;
use std::path::Path;

pub(super) const VERSION: &str = env!("CARGO_PKG_VERSION");

pub(super) fn run_execute_command(target: &str, options: ExecuteCommandOptions) -> bool {
    let execution_options = options.litex_execution_options();
    let outcome = match options.execution {
        LitexExecution::Eval => run_code(target, execution_options),
        LitexExecution::File => run_file(target, execution_options),
        LitexExecution::IsolatedFile => run_isolated_file(target, execution_options),
        LitexExecution::Repository => run_repository(target, execution_options),
        LitexExecution::Repl | LitexExecution::Session | LitexExecution::IsolatedSession => {
            unreachable!("run command was resolved to a non-batch target")
        }
    };
    let (_, has_path) = execution_target(options.execution);
    let output = render_run(&outcome, has_path.then_some(target));
    println!("{}", output);
    outcome.ok
}

pub(super) fn run_graph_command(
    graph_kind: GraphKind,
    target: &str,
    save_path: Option<&str>,
    options: GraphCommandOptions,
) -> bool {
    let hide_file_paths = !options.output_detail.is_detailed();
    let execution_options = options.litex_execution_options();
    let outcome = match options.execution {
        LitexExecution::Eval => run_code(target, execution_options),
        LitexExecution::File => run_file(target, execution_options),
        LitexExecution::IsolatedFile => run_isolated_file(target, execution_options),
        LitexExecution::Repository => run_repository(target, execution_options),
        LitexExecution::Repl | LitexExecution::Session | LitexExecution::IsolatedSession => {
            unreachable!("graph command was resolved to a non-batch target")
        }
    };
    let (ok, output) = render_graph(graph_kind, outcome, hide_file_paths);
    let (target_kind, has_path) = execution_target(options.execution);
    let input_path = has_path.then_some(target);
    let artifact_kind = match graph_kind {
        GraphKind::Result => "result_graph",
        GraphKind::Fact => "fact_graph",
        GraphKind::Definition => "definition_graph",
    };
    let trimmed_output = output.trim();
    if !ok {
        println!(
            "{}",
            render_artifact(
                artifact_kind,
                "json",
                target_kind,
                input_path,
                save_path,
                JsonValue::Null,
                JsonValue::RawJson(trimmed_output.to_string()),
            )
        );
        return false;
    }

    if let Some(save_path) = save_path {
        let path = Path::new(save_path);
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                if let Err(error) = fs::create_dir_all(parent) {
                    let message = format!(
                        "failed to create {} output directory for {}: {}",
                        graph_kind.output_name(),
                        save_path,
                        error
                    );
                    println!(
                        "{}",
                        render_artifact(
                            artifact_kind,
                            "json",
                            target_kind,
                            input_path,
                            Some(save_path),
                            JsonValue::Null,
                            simple_error("artifact_write_error", message.as_str()),
                        )
                    );
                    return false;
                }
            }
        }
        if let Err(error) = fs::write(path, format!("{}\n", trimmed_output)) {
            let message = format!(
                "failed to write {} JSON to {}: {}",
                graph_kind.output_name(),
                save_path,
                error
            );
            println!(
                "{}",
                render_artifact(
                    artifact_kind,
                    "json",
                    target_kind,
                    input_path,
                    Some(save_path),
                    JsonValue::Null,
                    simple_error("artifact_write_error", message.as_str()),
                )
            );
            return false;
        }
        println!(
            "{}",
            render_artifact(
                artifact_kind,
                "json",
                target_kind,
                input_path,
                Some(save_path),
                JsonValue::Null,
                JsonValue::Null,
            )
        );
        return true;
    }

    println!(
        "{}",
        render_artifact(
            artifact_kind,
            "json",
            target_kind,
            input_path,
            None,
            JsonValue::RawJson(trimmed_output.to_string()),
            JsonValue::Null,
        )
    );
    true
}
