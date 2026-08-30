use super::arguments::read_non_flag_value_after_flag;
use super::messages::print_help_message;
use crate::output::style::OutputStyle;
use crate::pipeline::RunOptions;
use crate::stmt_result_to_lean_compiler::{
    compile_litex_file_to_lean_file, compile_litex_markdown_code_blocks_to_lean_file,
};
use std::path::Path;
use std::process;

pub(super) fn run_lean_file_command(
    args: &[String],
    index: &mut usize,
    file_path: &str,
    options: RunOptions,
    isolated: bool,
) {
    *index += 1;
    let output_path = match read_non_flag_value_after_flag(args, index, "-lean") {
        Ok(value) => value,
        Err(message) => {
            eprintln!("-lean requires an output .lean path: {}", message);
            print_help_message();
            process::exit(2);
        }
    };
    if !isolated {
        eprintln!(
            "single-file Litex-to-Lean requires `-isolated`: litex -f <input.lit> -isolated -lean <output.lean>"
        );
        print_help_message();
        process::exit(2);
    }
    if options.strict_mode || options.summarize || options.output_style != OutputStyle::Normal {
        eprintln!(
            "single-file Litex-to-Lean accepts only `-f <input.lit> -isolated -lean <output.lean>`"
        );
        print_help_message();
        process::exit(2);
    }
    if let Some(unexpected) = args.get(*index) {
        eprintln!("unexpected argument after -lean output: {}", unexpected);
        print_help_message();
        process::exit(2);
    }

    match compile_litex_file_to_lean_file(Path::new(file_path), Path::new(&output_path)) {
        Ok(()) => println!("wrote freshly generated Lean to {}", output_path),
        Err(message) => {
            eprintln!("{}", message);
            process::exit(1);
        }
    }
}

pub(super) fn run_lean_ledger_command(args: &[String], index: &mut usize) {
    *index += 1;
    let markdown_path = match read_non_flag_value_after_flag(args, index, "-lean-ledger") {
        Ok(value) => value,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    let output_path = match read_non_flag_value_after_flag(args, index, "-lean-ledger") {
        Ok(value) => value,
        Err(message) => {
            eprintln!("-lean-ledger requires an output .lean path: {}", message);
            print_help_message();
            process::exit(2);
        }
    };
    if let Some(unexpected) = args.get(*index) {
        eprintln!(
            "unexpected argument after -lean-ledger output: {}",
            unexpected
        );
        print_help_message();
        process::exit(2);
    }

    match compile_litex_markdown_code_blocks_to_lean_file(
        Path::new(&markdown_path),
        Path::new(&output_path),
    ) {
        Ok(count) => {
            println!(
                "wrote {} freshly generated Lean entries to {}",
                count, output_path
            );
        }
        Err(message) => {
            eprintln!("{}", message);
            process::exit(1);
        }
    }
}
