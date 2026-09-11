// Copyright Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

use litex::cli::run_command_line_commands;
use litex::new_pipeline::run::{run as run_new_pipeline, DispatchOutcome};
use litex::new_pipeline::runtime::PipelineError;
use std::process;

const CLI_STACK_SIZE: usize = 64 * 1024 * 1024;

fn main() {
    std::thread::Builder::new()
        .name("litex-cli".to_string())
        .stack_size(CLI_STACK_SIZE)
        .spawn(run_selected_cli)
        .expect("start Litex CLI thread")
        .join()
        .expect("Litex CLI thread panicked");
}

fn run_selected_cli() {
    if use_new_pipeline_track() {
        run_new_pipeline_track();
    } else {
        run_command_line_commands();
    }
}

/// Dual-track switch.  Default remains the legacy CLI.
fn use_new_pipeline_track() -> bool {
    match std::env::var("LITEX_NEW_PIPELINE") {
        Ok(value) => {
            let value = value.trim();
            !(value.is_empty() || value == "0" || value.eq_ignore_ascii_case("false"))
        }
        Err(_) => false,
    }
}

fn run_new_pipeline_track() {
    match run_new_pipeline() {
        Ok(DispatchOutcome::Ran) => {}
        Ok(DispatchOutcome::Help | DispatchOutcome::Version) => {}
        Err(error) => {
            eprintln!("{}", format_pipeline_error(&error));
            let code = match error {
                PipelineError::InvalidArguments(_) => 2,
                _ => 1,
            };
            process::exit(code);
        }
    }
}

fn format_pipeline_error(error: &PipelineError) -> String {
    match error {
        PipelineError::InvalidArguments(message) => format!("cli_error: {}", message),
        PipelineError::Io { path, message } => {
            format!("io_error: {}: {}", path.display(), message)
        }
        PipelineError::Unsupported(message) => format!("unsupported: {}", message),
        PipelineError::Invariant(message) => format!("invariant: {}", message),
    }
}
