use litex::pipeline::{
    run_repl_loop, run_repl_loop_json, run_source_code_from_string, run_source_code_in_file,
    run_source_code_in_file_json,
};
use std::env;
use std::path::{Path, PathBuf};
use std::process;

pub const MAIN_DOT_LIT: &str = "main.lit";

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_cli() {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut index: usize = 0;

    while index < args.len() {
        let head = match args.get(index) {
            Some(value) => value.as_str(),
            None => break,
        };

        match head {
            "-json" | "--json" => {
                if args.len() == 1 {
                    run_repl(VERSION, true);
                    return;
                }
                eprintln!(
                    "{} is only valid in two forms: `litex -json` (JSON REPL), `litex -f/-r ... -json` (JSON output)",
                    head
                );
                print_usage();
                process::exit(2);
            }
            "-help" | "--help" => {
                print_usage();
                println!();
                println!("If no options are provided, starts interactive REPL mode.");
                return;
            }
            "-version" | "--version" => {
                println!("Litex Kernel: litex {}", VERSION);
                return;
            }
            "-elatex" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-elatex") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                match compile_code_to_latex_elatex(code.as_str()) {
                    Ok(output) => println!("{}", output),
                    Err(message) => {
                        eprintln!("Error: {}", message);
                        process::exit(1);
                    }
                }
                return;
            }
            "-e" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                let output = run_source_code_from_string(code.as_str(), "-e");
                println!("{}", output.trim());
                println!("{}", repl_footer_placeholder());
                return;
            }
            "-f" => {
                index += 1;
                let file_path = match read_non_flag_value_after_flag(&args, &mut index, "-f") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                let mut should_output_json = false;
                if let Some(next_token) = args.get(index) {
                    if next_token == "-json" || next_token == "--json" {
                        should_output_json = true;
                    }
                }
                main_flag_file(file_path.as_str(), should_output_json);
                return;
            }
            "-r" => {
                index += 1;
                let repo_path = match read_non_flag_value_after_flag(&args, &mut index, "-r") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                let joined = Path::new(repo_path.as_str()).join(MAIN_DOT_LIT);
                let joined_string = match joined.to_str() {
                    Some(path_string) => path_string.to_string(),
                    None => {
                        eprintln!("Error: repo path is not valid UTF-8");
                        process::exit(1);
                    }
                };
                let mut should_output_json = false;
                if let Some(next_token) = args.get(index) {
                    if next_token == "-json" || next_token == "--json" {
                        should_output_json = true;
                    }
                }
                main_flag_file(joined_string.as_str(), should_output_json);
                return;
            }
            "-latex" => {
                index += 1;
                let file_path = match read_non_flag_value_after_flag(&args, &mut index, "-latex") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                match compile_file_to_latex(file_path.as_str()) {
                    Ok(output) => println!("{}", output),
                    Err(message) => {
                        eprintln!("Error: {}", message);
                        process::exit(1);
                    }
                }
                return;
            }
            "-fmt" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-fmt") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                match format_code(code.as_str()) {
                    Ok(output) => println!("{}", output),
                    Err(message) => {
                        eprintln!("Error: {}", message);
                        process::exit(1);
                    }
                }
                return;
            }
            "-install" => {
                index += 1;
                let module_name =
                    match read_non_flag_value_after_flag(&args, &mut index, "-install") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_usage();
                            process::exit(2);
                        }
                    };
                install_module(module_name.as_str());
                return;
            }
            "-uninstall" => {
                index += 1;
                let module_name =
                    match read_non_flag_value_after_flag(&args, &mut index, "-uninstall") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_usage();
                            process::exit(2);
                        }
                    };
                uninstall_module(module_name.as_str());
                return;
            }
            "-list" => {
                list_installed_modules();
                return;
            }
            "-update" => {
                index += 1;
                let module_name = match read_non_flag_value_after_flag(&args, &mut index, "-update")
                {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_usage();
                        process::exit(2);
                    }
                };
                update_module(module_name.as_str());
                return;
            }
            "-tutorial" => {
                run_tutorial();
                return;
            }
            other => {
                eprintln!("unknown argument: {}", other);
                print_usage();
                process::exit(2);
            }
        }
    }

    run_repl(VERSION, false);
}

/// `index` must point at the first token after the flag; reads one value and advances past it.
fn read_non_flag_value_after_flag(
    args: &[String],
    index: &mut usize,
    flag_name: &str,
) -> Result<String, String> {
    let value = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => candidate.clone(),
        _ => {
            return Err(format!("{} requires a value", flag_name));
        }
    };
    *index += 1;
    Ok(value)
}

fn print_usage() {
    println!("Usage: litex [options]");
    println!("Options:");
    println!("  -help              Show help message");
    println!("  -version           Show version information");
    println!("  -e <CODE>          Execute the given code");
    println!("  -f <PATH>          Execute the given file");
    println!("  -r <REPO>          Execute the given repo (runs REPO/main.lit)");
    println!("  -f <PATH> -json    Execute file and output JSON");
    println!("  -r <REPO> -json    Execute repo main.lit and output JSON");
    println!("  -json              Start REPL with JSON output");
    println!("  -latex <PATH>      Compile the given file to LaTeX (not implemented)");
    println!("  -elatex <CODE>     Compile the given code to LaTeX (not implemented)");
    println!("  -fmt <CODE>        Format the given code (not implemented)");
    println!("  -install <PKG>     Install module (not implemented)");
    println!("  -uninstall <PKG>   Uninstall module (not implemented)");
    println!("  -list              List installed modules (not implemented)");
    println!("  -update <PKG>      Update module (not implemented)");
    println!("  -tutorial          Interactive tutorial (not implemented)");
}

fn remove_windows_carriage_return(path_or_code: &str) -> String {
    path_or_code.replace('\r', "")
}

fn main_flag_file(file_flag: &str, should_output_json: bool) {
    let path = remove_windows_carriage_return(file_flag);

    let abs_file_path: PathBuf = if Path::new(path.as_str()).is_absolute() {
        PathBuf::from(path.as_str())
    } else {
        let working_directory_result = env::current_dir();
        let working_directory = match working_directory_result {
            Ok(path) => path,
            Err(error) => {
                eprintln!("Error: failed to get current working directory: {}", error);
                return;
            }
        };
        working_directory.join(path.as_str())
    };

    if abs_file_path.parent().is_none() {
        eprintln!("Error: could not get parent directory of file path");
        return;
    }

    let path_string = match abs_file_path.to_str() {
        Some(path_string) => path_string.to_string(),
        None => {
            eprintln!("Error: file path is not valid UTF-8");
            return;
        }
    };

    let output = if should_output_json {
        run_source_code_in_file_json(path_string.as_str())
    } else {
        run_source_code_in_file(path_string.as_str())
    };
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
    println!("{}", repl_footer_placeholder());
}

fn string_with_trimmed_outer_newlines(text: &str) -> String {
    text.trim().to_string()
}

fn repl_footer_placeholder() -> String {
    "(REPL / ret-type footer: not implemented in Rust kernel yet)".to_string()
}

fn compile_code_to_latex_elatex(_code: &str) -> Result<String, String> {
    panic!("-elatex: compile code to LaTeX is not implemented in the Rust kernel yet");
}

fn compile_file_to_latex(_file_path: &str) -> Result<String, String> {
    panic!("-latex: compile file to LaTeX is not implemented in the Rust kernel yet");
}

fn format_code(_code: &str) -> Result<String, String> {
    panic!("-fmt: format code is not implemented in the Rust kernel yet");
}

fn install_module(module_name: &str) {
    panic!(
        "-install: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn uninstall_module(module_name: &str) {
    panic!(
        "-uninstall: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn list_installed_modules() {
    panic!("-list: module manager is not implemented in the Rust kernel yet");
}

fn update_module(module_name: &str) {
    panic!(
        "-update: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn run_tutorial() {
    panic!("-tutorial: not implemented in the Rust kernel yet");
}

fn run_repl(version: &str, should_output_json: bool) {
    if should_output_json {
        run_repl_loop_json(version);
    } else {
        run_repl_loop(version);
    }
}
