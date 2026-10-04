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

use litex::run::{parse_launch_command, run_command};
use litex::runtime::RuntimeError;
use litex::LITEX;
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
    // Binary entry: argv -> LaunchCommand -> run_command.
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match parse_launch_command(&args).and_then(run_command) {
        Ok(outcome) => {
            if let Some(json) = outcome.normal_json() {
                println!("{}", json);
            }
            if outcome.process_failed() {
                process::exit(1);
            }
        }
        Err(error) => {
            eprintln!("{}", error);
            let code = match error {
                RuntimeError::InvalidArguments(_) => 2,
                _ => 1,
            };
            process::exit(code);
        }
    }
}
