use super::arguments::{read_any_value_after_flag, read_non_flag_value_after_flag};
use crate::graph::{run_graph, GraphKind, GraphRequest};
use crate::pipeline::{run, run_isolated_repl_with_runtime, RunOptions, RunRequest, RunTarget};
use crate::runner::{run_runner, RunnerRequest};
use std::fs;
use std::path::Path;

pub(super) const VERSION: &str = env!("CARGO_PKG_VERSION");

pub(super) fn run_code_command(code: &str, options: RunOptions) {
    let outcome = run(RunRequest::new(RunTarget::code(code, "-e"), options));
    println!("{}", outcome.output.trim());
}

pub(super) fn run_file_command(file_flag: &str, options: RunOptions) {
    let mut outcome = run(RunRequest::new(RunTarget::file(file_flag), options));
    if let Some(message) = outcome.target_error.as_ref() {
        eprintln!("Error: {}", message);
        return;
    }
    println!("{}", outcome.output.trim());
    if outcome.ok && outcome.runtime.current_source_allows_inline_imports() {
        run_isolated_repl_with_runtime(VERSION, &mut outcome.runtime);
    }
}

pub(super) fn run_repository_command(repo_path: &str, options: RunOptions) {
    let outcome = run(RunRequest::new(RunTarget::repository(repo_path), options));
    println!("{}", outcome.output.trim());
}

pub(super) fn run_runner_command(
    args: &[String],
    index: &mut usize,
    options: RunOptions,
) -> Result<(bool, String), String> {
    let target_flag = read_any_value_after_flag(args, index, "-runner")?;
    let hide_file_paths = !options.output_style.is_detailed();
    let target = match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            RunTarget::code(code.as_str(), "-runner -e")
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            RunTarget::file(file_path.as_str())
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            RunTarget::repository(repo_path.as_str())
        }
        _ => {
            return Err(
                "-runner must be followed by one of: -f <file>, -e <code>, -r <repo>".to_string(),
            )
        }
    };
    Ok(run_runner(RunnerRequest::new(
        RunRequest::new(target, options),
        hide_file_paths,
    )))
}

pub(super) fn run_graph_command(
    graph_kind: GraphKind,
    args: &[String],
    index: &mut usize,
    options: RunOptions,
) -> Result<(bool, String, Option<String>), String> {
    let command_flag = graph_kind.flag();
    let target_flag = read_any_value_after_flag(args, index, command_flag)?;
    let target = match target_flag.as_str() {
        "-e" | "-f" | "-r" => read_non_flag_value_after_flag(args, index, target_flag.as_str())?,
        _ => {
            return Err(format!(
                "{} must be followed by one of: -f <file> [json], -e <code> [json], -r <repo> [json]",
                command_flag
            ));
        }
    };
    let save_path = read_optional_graph_save_path(args, index, command_flag)?;
    let hide_file_paths = !options.output_style.is_detailed();
    let run_target = match target_flag.as_str() {
        "-e" => RunTarget::code(&target, format!("{} -e", command_flag).as_str()),
        "-f" => RunTarget::file(&target),
        "-r" => RunTarget::repository(&target),
        _ => unreachable!("graph target flag was already validated"),
    };
    let output = run_graph(GraphRequest::new(
        graph_kind,
        RunRequest::new(run_target, options),
        hide_file_paths,
    ));

    Ok((output.0, output.1, save_path))
}

pub(super) fn read_optional_graph_save_path(
    args: &[String],
    index: &mut usize,
    command_flag: &str,
) -> Result<Option<String>, String> {
    let save_path = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => {
            *index += 1;
            Some(candidate.clone())
        }
        _ => None,
    };

    if let Some(unexpected) = args.get(*index) {
        return Err(format!(
            "unexpected argument after {} target: {}",
            command_flag, unexpected
        ));
    }

    Ok(save_path)
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
