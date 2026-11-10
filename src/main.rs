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

use litex::launch_command::parse_launch_with_feedback;
use litex::launch_command::LaunchCommand;
use litex::run::run_command::run_command_with_feedback;
use litex::runtime::RuntimeError;
use litex::LITEX;
use std::io::Write;
use std::process;

const LAUNCH_STACK_SIZE: usize = 64 * 1024 * 1024;

fn main() {
    std::thread::Builder::new()
        .name(format!("{}-launch", LITEX.to_ascii_lowercase()))
        .stack_size(LAUNCH_STACK_SIZE)
        .spawn(run_launch)
        .expect(&format!("start {} launch thread", LITEX))
        .join()
        .expect(&format!("{} launch thread panicked", LITEX));
}

fn run_launch() {
    let args = std::env::args_os()
        .skip(1)
        .enumerate()
        .map(|(index, arg)| {
            arg.into_string().unwrap_or_else(|_| {
                report_error(
                    None,
                    &RuntimeError::InvalidArguments(format!(
                        "argument {} must be valid UTF-8",
                        index + 1
                    )),
                )
            })
        })
        .collect::<Vec<_>>();
    match litex::reading::parse_reading_command(&args) {
        Ok(Some(command)) => match litex::run::run_reading::run_reading(command) {
            Ok(true) => return,
            Ok(false) => process::exit(1),
            Err(error) => report_error(None, &error),
        },
        Ok(None) => {}
        Err(error) => report_error(None, &error),
    }
    let (command, compact) = match parse_launch_with_feedback(&args) {
        Ok(command) => command,
        Err(error) => report_error(None, &error),
    };
    match run_command_with_feedback(command.clone(), compact) {
        Ok(outcome) => {
            if let Err(error) = litex::run::output::write_command_outcome(&outcome) {
                report_run_error(&command, &error, compact);
            }
            if outcome.process_failed() {
                process::exit(1);
            }
        }
        Err(error) => report_run_error(&command, &error, compact),
    }
}

fn report_error(command: Option<&LaunchCommand>, error: &RuntimeError) -> ! {
    if let Err(output_error) = litex::run::output::write_command_error(command, error) {
        let _ = writeln!(std::io::stderr().lock(), "{}; {}", output_error, error);
    }
    let code = match error {
        RuntimeError::InvalidArguments(_) => 2,
        _ => 1,
    };
    process::exit(code);
}

fn report_run_error(command: &LaunchCommand, error: &RuntimeError, compact: bool) -> ! {
    if compact {
        let json = litex::json_output::emit_compact_command_error(command, error);
        if let Err(output_error) = litex::run::output::write_stdout(format_args!("{json}\n")) {
            let _ = writeln!(std::io::stderr().lock(), "{output_error}");
        }
        let code = if matches!(error, RuntimeError::InvalidArguments(_)) {
            2
        } else {
            1
        };
        process::exit(code);
    }
    report_error(Some(command), error)
}
