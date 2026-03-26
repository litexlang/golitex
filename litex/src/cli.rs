use litex::common::keywords::BUILTIN_CODE;
use litex::module_manager::ModuleManager;
use litex::pipeline::run_repl_loop_and_return_json_string;
use litex::pipeline::run_repl_loop_and_return_string;
use litex::pipeline::run_source_code;
use litex::pipeline::run_source_code_in_file_and_return_json_string;
use litex::pipeline::run_source_code_in_file_and_return_string;
use litex::runtime::Runtime;
use litex::runtime::RuntimeContext;
use litex::runtime::BUILTIN_ENV_CODE;
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
            "-json" => {
                index += 1;
                if index == 1 {
                    run_repl(VERSION, true);
                    return;
                }
                // In case someone passes "-json" after other flags, we try to reject
                // ambiguous ordering. Documented usage is "-f -json <file>" etc.
                eprintln!(
                    "{} should be used alone (litex -json) or as '-f/-e/-r -json <value>'",
                    head
                );
                print_help_message();
                process::exit(2);
            }
            "-e" => {
                index += 1;
                let should_output_json = if args.get(index).map(|v| v.as_str()) == Some("-json") {
                    index += 1;
                    true
                } else {
                    false
                };

                let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let mut module_manager = ModuleManager::new_empty_module_manager(BUILTIN_CODE);
                let mut runtime_context =
                    RuntimeContext::new_empty_runtime_context_with_one_env(&mut module_manager);
                let mut runtime = Runtime::new(&mut runtime_context);

                let (ok, msg) = run_source_code(BUILTIN_ENV_CODE, &mut runtime, true);
                if !ok {
                    eprintln!("builtin code execution failed: {}", msg);
                    process::exit(1);
                }
                runtime.new_file_path_new_env_new_name_scope("-e");

                let output = run_source_code(code.as_str(), &mut runtime, should_output_json);
                println!("{}", output.1.trim());
                println!("{}", repl_footer_placeholder());
                return;
            }
            "-f" => {
                index += 1;
                let should_output_json = if args.get(index).map(|v| v.as_str()) == Some("-json") {
                    index += 1;
                    true
                } else {
                    false
                };

                let file_path = match read_non_flag_value_after_flag(&args, &mut index, "-f") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                main_flag_file(file_path.as_str(), should_output_json);
                return;
            }
            "-r" => {
                index += 1;
                let should_output_json = if args.get(index).map(|v| v.as_str()) == Some("-json") {
                    index += 1;
                    true
                } else {
                    false
                };

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
                main_flag_file(joined_string.as_str(), should_output_json);
                return;
            }
            "-latex" => {
                index += 1;
                if index >= args.len() {
                    run_latex_interactive();
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
                match latex_output_result {
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
                        print_help_message();
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
        run_source_code_in_file_and_return_json_string(path_string.as_str())
    } else {
        run_source_code_in_file_and_return_string(path_string.as_str())
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

fn compile_code_to_latex(_code: &str) -> Result<String, String> {
    panic!("-latex -e: compile code to LaTeX is not implemented in the Rust kernel yet");
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

fn run_latex_interactive() {
    panic!("-latex: interactive LaTeX mode is not implemented in the Rust kernel yet");
}

fn run_repl(version: &str, should_output_json: bool) {
    if should_output_json {
        run_repl_loop_and_return_json_string(version);
    } else {
        run_repl_loop_and_return_string(version);
    }
}

fn help_message() -> String {
    let result = r#"litex : run Litex interactively in your terminal
litex -f <file> : run the given file
litex -r <repo> : run the given repository
litex -e <code> : execute the given code
litex -json : run Litex interactively in your terminal and return the result in JSON format
litex -f -json <file> : execute the given file and return the result in JSON format
litex -e -json <code> : execute the given code and return the result in JSON format
litex -r -json <repo> : execute the given repository and return the result in JSON format
litex -latex : compile the given file or code to LaTeX interactively in your terminal
litex -latex -f <file> : compile the given file to LaTeX
litex -latex -e <code> : compile the given code to LaTeX
litex -latex -r <repo> : compile the given repository to LaTeX
litex -help : show the help message
litex -version : show the version
litex -fmt : format the given code
litex -install <module> : install the given module
litex -uninstall <module> : uninstall the given module
litex -list : list all installed modules
litex -update <module> : update the given module
litex -tutorial : run the tutorial
"#;
    result.to_string()
}
