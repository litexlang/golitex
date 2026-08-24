use crate::prelude::{FileRunOptions, OutputLanguage, OutputStyle, RunOutputOptions};

// Legacy public signatures. New callers should prefer `run_file` or
// `run_repository` with named options.
pub fn run_source_code_in_file(entry_file_path: &str) -> String {
    super::run_file(entry_file_path, FileRunOptions::default()).1
}

pub fn run_source_code_in_file_for_cli(entry_file_path: &str, detail_output: bool) -> String {
    run_source_code_in_file_for_cli_with_strict(entry_file_path, detail_output, false)
}

pub fn run_source_code_in_file_for_cli_with_strict(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> String {
    run_source_code_in_file_for_cli_with_strict_and_language(
        entry_file_path,
        detail_output,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_source_code_in_file_for_cli_with_strict_and_language(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> String {
    run_source_code_in_file_for_cli_with_summary_and_language(
        entry_file_path,
        detail_output,
        strict_mode,
        output_language,
        false,
    )
}

pub fn run_source_code_in_file_for_cli_with_summary_and_language(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    super::run_file(
        entry_file_path,
        FileRunOptions {
            output: RunOutputOptions {
                output_style: output_style_from_detail_output(detail_output),
                strict_mode,
                output_language,
                summarize,
            },
            force_isolated: false,
        },
    )
    .1
}

pub fn run_source_code_in_file_for_cli_with_summary_and_language_and_isolation(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
    force_isolated: bool,
) -> String {
    super::run_file(
        entry_file_path,
        FileRunOptions {
            output: RunOutputOptions {
                output_style: output_style_from_detail_output(detail_output),
                strict_mode,
                output_language,
                summarize,
            },
            force_isolated,
        },
    )
    .1
}

pub fn run_source_code_in_file_for_cli_with_output_style_and_summary_and_language_and_isolation(
    entry_file_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
    force_isolated: bool,
) -> String {
    super::run_file(
        entry_file_path,
        FileRunOptions {
            output: RunOutputOptions {
                output_style,
                strict_mode,
                output_language,
                summarize,
            },
            force_isolated,
        },
    )
    .1
}

pub fn run_source_code_in_file_with_ok(entry_file_path: &str) -> (bool, String) {
    super::run_file(entry_file_path, FileRunOptions::default())
}

pub fn run_source_code_in_repository_for_cli_with_summary_and_language(
    repository_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    super::run_repository(
        repository_path,
        RunOutputOptions {
            output_style: output_style_from_detail_output(detail_output),
            strict_mode,
            output_language,
            summarize,
        },
    )
    .1
}

pub fn run_source_code_in_repository_for_cli_with_output_style_and_summary_and_language(
    repository_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    super::run_repository(
        repository_path,
        RunOutputOptions {
            output_style,
            strict_mode,
            output_language,
            summarize,
        },
    )
    .1
}

pub fn run_repository_with_output(
    repository_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    super::run_repository(
        repository_path,
        RunOutputOptions {
            output_style: output_style_from_detail_output(detail_output),
            strict_mode,
            output_language,
            summarize,
        },
    )
}

pub fn run_repository_with_output_style(
    repository_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    super::run_repository(
        repository_path,
        RunOutputOptions {
            output_style,
            strict_mode,
            output_language,
            summarize,
        },
    )
}

fn output_style_from_detail_output(detail_output: bool) -> OutputStyle {
    if detail_output {
        OutputStyle::Detailed
    } else {
        OutputStyle::Normal
    }
}
