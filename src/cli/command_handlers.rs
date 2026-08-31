use crate::prelude::*;
use std::fs;
use std::path::Path;

pub(super) const VERSION: &str = env!("CARGO_PKG_VERSION");

pub(super) fn run_code_command(code: &str, options: RunOptions) {
    let outcome = run_code(code, options);
    println!("{}", outcome.output.trim());
}

pub(super) fn run_file_command(file_flag: &str, options: RunOptions) {
    let mut outcome = run_file(file_flag, options);
    if let Some(message) = outcome.target_error.as_ref() {
        eprintln!("Error: {}", message);
        return;
    }
    println!("{}", outcome.output.trim());
    if outcome.ok && options.is_isolated() {
        run_isolated_repl_with_runtime(VERSION, &mut outcome.runtime);
    }
}

pub(super) fn run_repository_command(repo_path: &str, options: RunOptions) {
    let outcome = run_repository(repo_path, options);
    println!("{}", outcome.output.trim());
}

pub(super) fn run_graph_command(
    graph_kind: GraphKind,
    target: &str,
    options: RunOptions,
) -> (bool, String) {
    let hide_file_paths = !options.output_style().is_detailed();
    let outcome = match options.execution() {
        ExecutionOption::Eval => run_code(target, options),
        ExecutionOption::File | ExecutionOption::IsolatedFile => run_file(target, options),
        ExecutionOption::Repo => run_repository(target, options),
        ExecutionOption::Repl | ExecutionOption::Session | ExecutionOption::IsolatedSession => {
            unreachable!("graph command was resolved to a non-batch target")
        }
    };
    render_graph(graph_kind, outcome, hide_file_paths)
}

pub(super) fn print_or_save_graph_output(
    graph_kind: GraphKind,
    output: &str,
    save_path: Option<&str>,
) -> Result<(), String> {
    let trimmed_output = output.trim();
    let Some(save_path) = save_path else {
        println!("{}", trimmed_output);
        return Ok(());
    };

    let path = Path::new(save_path);
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|error| {
                format!(
                    "failed to create {} output directory for {}: {}",
                    graph_kind.output_name(),
                    save_path,
                    error
                )
            })?;
        }
    }
    fs::write(path, format!("{}\n", trimmed_output)).map_err(|error| {
        format!(
            "failed to write {} JSON to {}: {}",
            graph_kind.output_name(),
            save_path,
            error
        )
    })?;
    println!("saved {} JSON to {}", graph_kind.output_name(), save_path);
    Ok(())
}
