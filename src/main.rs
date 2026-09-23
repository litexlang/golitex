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
use litex::new_pipeline::run::launch as launch_new_pipeline;
use litex::new_pipeline::runtime::RuntimeError;
use litex::new_pipeline::LITEX;
use std::process;

const CLI_STACK_SIZE: usize = 64 * 1024 * 1024;

fn main() {
    std::thread::Builder::new()
        .name(format!("{}-cli", LITEX.to_ascii_lowercase()))
        .stack_size(CLI_STACK_SIZE)
        .spawn(run_selected_cli)
        .expect(&format!("start {} CLI thread", LITEX))
        .join()
        .expect(&format!("{} CLI thread panicked", LITEX));
}

fn run_selected_cli() {
    if use_new_pipeline_track() {
        launch_new_pipeline_track();
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

fn launch_new_pipeline_track() {
    match launch_new_pipeline() {
        Ok(outcome) => {
            if outcome.process_failed() {
                // Soft Failed / session_error stay in the outcome payload for later JSON.
                process::exit(1);
            }
        }
        Err(error) => {
            eprintln!("{}", format_runtime_error(&error));
            let code = match error {
                RuntimeError::InvalidArguments(_) => 2,
                _ => 1,
            };
            process::exit(code);
        }
    }
}

fn format_runtime_error(error: &RuntimeError) -> String {
    match error {
        RuntimeError::InvalidArguments(message) => format!("cli_error: {}", message),
        RuntimeError::Io { path, message } => {
            format!("io_error: {}: {}", path.display(), message)
        }
        RuntimeError::ParseError(error) => {
            format!(
                "parse_error: {} at line {} in {}",
                error.message, error.line, error.path
            )
        }
        RuntimeError::Unsupported(message) => format!("unsupported: {}", message),
        RuntimeError::InternalBug(message) => format!("internal_bug: {}", message),
    }
}
