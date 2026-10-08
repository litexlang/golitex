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

use litex::launch_command::LaunchCommand;
use litex::run::{parse_launch_command, run_command};
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
    let command = match parse_launch_command(&args) {
        Ok(command) => command,
        Err(error) => report_error(None, &error),
    };
    match run_command(command.clone()) {
        Ok(outcome) => {
            if let Err(error) = litex::run::output::write_command_outcome(&outcome) {
                report_error(Some(&command), &error);
            }
            if outcome.process_failed() {
                process::exit(1);
            }
        }
        Err(error) => report_error(Some(&command), &error),
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
