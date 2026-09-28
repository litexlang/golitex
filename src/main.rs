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

use litex::run::launch;
use litex::runtime::RuntimeError;
use litex::LITEX;
use std::process;

const CLI_STACK_SIZE: usize = 64 * 1024 * 1024;

fn main() {
    std::thread::Builder::new()
        .name(format!("{}-cli", LITEX.to_ascii_lowercase()))
        .stack_size(CLI_STACK_SIZE)
        .spawn(run_cli)
        .expect(&format!("start {} CLI thread", LITEX))
        .join()
        .expect(&format!("{} CLI thread panicked", LITEX));
}

fn run_cli() {
    match launch() {
        Ok(outcome) => {
            if outcome.process_failed() {
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
