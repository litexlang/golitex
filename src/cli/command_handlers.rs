use super::json_output::{execution_target, render_artifact, render_run, simple_error};
use crate::prelude::*;
use std::fs;
use std::path::Path;

pub(super) const VERSION: &str = env!("CARGO_PKG_VERSION");

pub(super) fn run_code_command(code: &str, options: RunOptions) -> bool {
    let outcome = run_code(code, options);
    println!("{}", render_run(&outcome, None));
    outcome.ok
}

pub(super) fn run_file_command(file_flag: &str, options: RunOptions) -> bool {
    let mut outcome = run_file(file_flag, options);
    let output = render_run(&outcome, Some(file_flag));
    if outcome.ok && options.is_isolated() {
        println!("{}", render_json_value_compact(&JsonValue::RawJson(output)));
        run_isolated_repl_with_runtime(VERSION, &mut outcome.runtime);
    } else {
        println!("{}", output);
    }
    outcome.ok
}

pub(super) fn run_repository_command(repo_path: &str, options: RunOptions) -> bool {
    let outcome = run_repository(repo_path, options);
    println!("{}", render_run(&outcome, Some(repo_path)));
    outcome.ok
}

pub(super) fn run_graph_command(
    graph_kind: GraphKind,
    target: &str,
    save_path: Option<&str>,
    options: RunOptions,
) -> bool {
    let hide_file_paths = !options.output_style().is_detailed();
    let outcome = match options.execution() {
        ExecutionOption::Eval => run_code(target, options),
        ExecutionOption::File | ExecutionOption::IsolatedFile => run_file(target, options),
        ExecutionOption::Repo => run_repository(target, options),
        ExecutionOption::Repl | ExecutionOption::Session | ExecutionOption::IsolatedSession => {
            unreachable!("graph command was resolved to a non-batch target")
        }
    };
    let (ok, output) = render_graph(graph_kind, outcome, hide_file_paths);
    let (target_kind, has_path) = execution_target(options);
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
