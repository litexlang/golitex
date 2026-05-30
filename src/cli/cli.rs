use crate::prelude::*;
use crate::to_latex::to_latex_from_source_after_builtins;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

pub const MAIN_DOT_LIT: &str = "main.lit";

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
const DETAIL_FLAG: &str = "-detail";

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let detail_output = remove_flag(&mut args, DETAIL_FLAG);
    let mut index: usize = 0;

    if !args.is_empty() {
        let head = args[index].as_str();

        match head {
            "-help" => {
                print_help_message();
                println!();
                println!("If no options are provided, starts interactive REPL mode.");
                return;
            }
            "-version" => {
                println!("Litex Kernel: litex {}", VERSION);
                return;
            }
            "-e" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let mut runtime = Runtime::new_with_builtin_code();
                runtime.new_file_path_new_env_new_name_scope("-e");
                runtime.detail_output = detail_output;

                let (stmt_results, runtime_error) = run_source_code(code.as_str(), &mut runtime);
                let output =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
                println!("{}", output.1.trim());
                return;
            }
            "-f" => {
                index += 1;
                let file_path = match read_non_flag_value_after_flag(&args, &mut index, "-f") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                main_flag_file(file_path.as_str(), detail_output);
                return;
            }
            "-r" => {
                index += 1;
                let repo_path = match read_non_flag_value_after_flag(&args, &mut index, "-r") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
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
                main_flag_file(joined_string.as_str(), detail_output);
                return;
            }
            "-runner" => {
                index += 1;
                let (ok, output) = match main_flag_runner(&args, &mut index, detail_output) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
                if !ok {
                    process::exit(1);
                }
                return;
            }
            "-latex" => {
                index += 1;
                if index >= args.len() {
                    println!("{}", run_latex_interactive());
                    return;
                }
                let latex_target_flag = match read_any_value_after_flag(&args, &mut index, "-latex")
                {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let latex_output_result = match latex_target_flag.as_str() {
                    "-f" => {
                        let file_path =
                            match read_non_flag_value_after_flag(&args, &mut index, "-f") {
                                Ok(value) => value,
                                Err(message) => {
                                    eprintln!("{}", message);
                                    print_help_message();
                                    process::exit(2);
                                }
                            };
                        compile_file_to_latex(file_path.as_str())
                    }
                    "-e" => {
                        let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
                            Ok(value) => value,
                            Err(message) => {
                                eprintln!("{}", message);
                                print_help_message();
                                process::exit(2);
                            }
                        };
                        compile_code_to_latex(code.as_str())
                    }
                    "-r" => {
                        let repo_path =
                            match read_non_flag_value_after_flag(&args, &mut index, "-r") {
                                Ok(value) => value,
                                Err(message) => {
                                    eprintln!("{}", message);
                                    print_help_message();
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
                        compile_file_to_latex(joined_string.as_str())
                    }
                    _ => {
                        eprintln!(
                            "-latex must be followed by one of: -f <file>, -e <code>, -r <repo>"
                        );
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", latex_output_result);
                return;
            }
            "-fmt" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-fmt") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", format_code(code.as_str()));
                return;
            }
            "-install" => {
                index += 1;
                let module_name =
                    match read_non_flag_value_after_flag(&args, &mut index, "-install") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_help_message();
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
                            print_help_message();
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
                        print_help_message();
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
                print_help_message();
                process::exit(2);
            }
        }
    }

    run_repl_with_detail_output(VERSION, detail_output);
}

fn remove_flag(args: &mut Vec<String>, flag_name: &str) -> bool {
    let before_len = args.len();
    args.retain(|arg| arg != flag_name);
    args.len() != before_len
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

/// `index` must point at the first token after the flag; reads one token (can be another flag) and advances past it.
fn read_any_value_after_flag(
    args: &[String],
    index: &mut usize,
    flag_name: &str,
) -> Result<String, String> {
    let value = match args.get(*index) {
        Some(candidate) => candidate.clone(),
        None => return Err(format!("{} requires a value", flag_name)),
    };
    *index += 1;
    Ok(value)
}

fn print_help_message() {
    println!("{}", help_message());
}

fn remove_windows_carriage_return(path_or_code: &str) -> String {
    path_or_code.replace('\r', "")
}

fn main_flag_file(file_flag: &str, detail_output: bool) {
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

    let output = run_source_code_in_file_for_cli(path_string.as_str(), detail_output);
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
}

fn main_flag_runner(
    args: &[String],
    index: &mut usize,
    detail_output: bool,
) -> Result<(bool, String), String> {
    let target_flag = read_any_value_after_flag(args, index, "-runner")?;
    let hide_file_paths = !detail_output;
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            Ok(run_runner_for_code(
                code.as_str(),
                "-runner -e",
                hide_file_paths,
            ))
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            Ok(run_runner_for_file(file_path.as_str(), hide_file_paths))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            Ok(run_runner_for_repo(repo_path.as_str(), hide_file_paths))
        }
        _ => Err("-runner must be followed by one of: -f <file>, -e <code>, -r <repo>".to_string()),
    }
}

fn string_with_trimmed_outer_newlines(text: &str) -> String {
    text.trim().to_string()
}

fn compile_code_to_latex(code: &str) -> String {
    let code = remove_windows_carriage_return(code);
    match to_latex_from_source_after_builtins(code.as_str(), "-latex -e") {
        Ok(s) => s,
        Err(e) => {
            let runtime = Runtime::new();
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

fn compile_file_to_latex(file_path: &str) -> String {
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_return(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_latex_from_source_after_builtins(source.as_str(), file_path) {
        Ok(s) => s,
        Err(e) => {
            let runtime = Runtime::new();
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

fn format_code(_code: &str) -> String {
    return "-fmt: format code is not implemented in the Rust kernel yet".to_string();
}

fn install_module(module_name: &str) -> String {
    return format!(
        "-install: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn uninstall_module(module_name: &str) -> String {
    return format!(
        "-uninstall: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn list_installed_modules() -> String {
    return "-list: module manager is not implemented in the Rust kernel yet".to_string();
}

fn update_module(module_name: &str) -> String {
    return format!(
        "-update: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn run_tutorial() -> String {
    return "-tutorial: not implemented in the Rust kernel yet".to_string();
}

fn run_latex_interactive() -> String {
    return "-latex: interactive LaTeX mode is not implemented in the Rust kernel yet".to_string();
}

fn help_message() -> String {
    let result = r#"litex : run Litex interactively in your terminal
litex -f <file> : run the given file
litex -r <repo> : run the given repository
litex -e <code> : execute the given code
litex -runner -f <file> : run a file and return one wrapper JSON object
litex -runner -e <code> : run source code and return one wrapper JSON object
litex -runner -r <repo> : run a repository and return one wrapper JSON object
litex -latex : compile the given file or code to LaTeX interactively in your terminal
litex -latex -f <file> : compile the given file to LaTeX
litex -latex -e <code> : compile the given code to LaTeX
litex -latex -r <repo> : compile the given repository to LaTeX
litex -help : show the help message
litex -version : show the version
litex -detail : include full trace details and raw source paths in JSON output
litex -fmt : format the given code
litex -install <module> : install the given module
litex -uninstall <module> : uninstall the given module
litex -list : list all installed modules
litex -update <module> : update the given module
litex -tutorial : run the tutorial
"#;
    result.to_string()
}
