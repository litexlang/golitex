use super::arguments::{read_any_value_after_flag, read_non_flag_value_after_flag};
use crate::prelude::*;
use std::fs;
use std::path::Path;
use std::process;

pub(super) const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone, Copy)]
pub(super) enum GraphKind {
    Result,
    Fact,
    Definition,
}

impl GraphKind {
    pub(super) fn flag(self) -> &'static str {
        match self {
            Self::Result => "-graph",
            Self::Fact => "-factgraph",
            Self::Definition => "-defgraph",
        }
    }

    pub(super) fn output_name(self) -> &'static str {
        match self {
            Self::Result => "graph",
            Self::Fact => "fact graph",
            Self::Definition => "definition graph",
        }
    }
}

pub(super) fn run_code_command(
    code: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize_output: bool,
) {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("-e");
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;

    let (stmt_results, runtime_error) = run_source_code(code, &mut runtime);
    let mut output = render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true).1;
    if summarize_output {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    println!("{}", output.trim());
}

pub(super) fn run_file_command(
    file_flag: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize_output: bool,
    force_isolated: bool,
    trust_before_line: Option<usize>,
) {
    let path_string = match resolve_source_file_path(file_flag) {
        Ok(path) => path,
        Err(message) => {
            eprintln!("Error: {}", message);
            return;
        }
    };

    let mut runtime = Runtime::new();
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let (stmt_results, runtime_error, trusted_prefix_report, trusted_prefix_setup_rejected) =
        run_file_with_project_context_and_trusted_prefix(
            path_string.as_str(),
            &mut runtime,
            force_isolated,
            trust_before_line,
        );
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if let Some(report) = trusted_prefix_report.as_ref() {
        let mut trusted_prefix_output = display_trusted_prefix_report_json(report);
        if !output.trim().is_empty() {
            trusted_prefix_output.push('\n');
            trusted_prefix_output.push_str(output.trim());
        }
        output = trusted_prefix_output;
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime_and_trusted_prefix(
                &runtime,
                &stmt_results,
                &runtime_error,
                report,
            )
            .as_str(),
        );
        output.push('\n');
    } else if summarize_output {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
    if trusted_prefix_setup_rejected {
        process::exit(2);
    }
    if ok && runtime.current_source_allows_inline_imports() && trust_before_line.is_none() {
        run_isolated_repl_with_runtime(VERSION, &mut runtime);
    }
}

pub(super) fn run_repository_command(
    repo_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize_output: bool,
) {
    let path = remove_windows_carriage_return(repo_path);
    let (_, output) = run_repository(
        path.as_str(),
        RunOutputOptions {
            output_style,
            strict_mode,
            output_language,
            summarize: summarize_output,
        },
    );
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
}

pub(super) fn run_runner_command(
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> Result<(bool, String), String> {
    let target_flag = read_any_value_after_flag(args, index, "-runner")?;
    let hide_file_paths = !output_style.is_detailed();
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let output = if strict_mode {
                run_runner_for_code_strict_with_language(
                    code.as_str(),
                    "-runner -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                crate::runner::run_runner_on_source(
                    "code",
                    "-runner -e",
                    code.as_str(),
                    hide_file_paths,
                    false,
                    output_language,
                )
            };
            Ok(output)
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            Ok(run_runner_for_file_with_strict_language_and_isolation(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            ))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            Ok(run_runner_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            ))
        }
        _ => Err("-runner must be followed by one of: -f <file>, -e <code>, -r <repo>".to_string()),
    }
}

pub(super) fn run_graph_command(
    graph_kind: GraphKind,
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
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
    let hide_file_paths = !output_style.is_detailed();
    let output = match (graph_kind, target_flag.as_str()) {
        (GraphKind::Result, "-e") => {
            if strict_mode {
                run_graph_for_code_strict_with_language(
                    &target,
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_graph_for_code_with_language(
                    &target,
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            }
        }
        (GraphKind::Fact, "-e") => {
            if strict_mode {
                run_fact_graph_for_code_strict_with_language(
                    &target,
                    "-factgraph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_fact_graph_for_code_with_language(
                    &target,
                    "-factgraph -e",
                    hide_file_paths,
                    output_language,
                )
            }
        }
        (GraphKind::Definition, "-e") => {
            if strict_mode {
                run_definition_graph_for_code_strict_with_language(
                    &target,
                    "-defgraph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_definition_graph_for_code_with_language(
                    &target,
                    "-defgraph -e",
                    hide_file_paths,
                    output_language,
                )
            }
        }
        (GraphKind::Result, "-f") => run_graph_for_file_with_strict_language_and_isolation(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
            force_isolated,
        ),
        (GraphKind::Fact, "-f") => run_fact_graph_for_file_with_strict_language_and_isolation(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
            force_isolated,
        ),
        (GraphKind::Definition, "-f") => {
            run_definition_graph_for_file_with_strict_language_and_isolation(
                &target,
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            )
        }
        (GraphKind::Result, "-r") => run_graph_for_repo_with_strict_and_language(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
        ),
        (GraphKind::Fact, "-r") => run_fact_graph_for_repo_with_strict_and_language(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
        ),
        (GraphKind::Definition, "-r") => run_definition_graph_for_repo_with_strict_and_language(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
        ),
        _ => unreachable!("graph target flag was already validated"),
    };

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
    let trimmed_output = string_with_trimmed_outer_newlines(output);
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

pub(super) fn string_with_trimmed_outer_newlines(text: &str) -> String {
    text.trim().to_string()
}
