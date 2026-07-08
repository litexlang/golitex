use crate::prelude::*;
use crate::to_latex::to_latex_from_source_after_builtins;
use crate::to_python::to_python_from_source_after_builtins;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

pub const MAIN_DOT_LIT: &str = "main.lit";

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
const DETAIL_FLAG: &str = "-detail";
const STRICT_FLAG: &str = "-strict";
const LANGUAGE_FLAG: &str = "-lang";

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let detail_output = remove_flag(&mut args, DETAIL_FLAG);
    let strict_mode = remove_flag(&mut args, STRICT_FLAG);
    let output_language = match remove_language_flag(&mut args) {
        Ok(language) => language,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
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
            "-upgrade" => {
                println!("{}", upgrade_message(VERSION));
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
                runtime.strict_mode = strict_mode;
                runtime.output_language = output_language;

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
                main_flag_file(
                    file_path.as_str(),
                    detail_output,
                    strict_mode,
                    output_language,
                );
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
                main_flag_file(
                    joined_string.as_str(),
                    detail_output,
                    strict_mode,
                    output_language,
                );
                return;
            }
            "-runner" => {
                index += 1;
                let (ok, output) = match main_flag_runner(
                    &args,
                    &mut index,
                    detail_output,
                    strict_mode,
                    output_language,
                ) {
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
            "-graph" => {
                index += 1;
                let (ok, output, save_path) = match main_flag_graph(
                    &args,
                    &mut index,
                    detail_output,
                    strict_mode,
                    output_language,
                ) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let trimmed_output = string_with_trimmed_outer_newlines(output.as_str());
                if let Some(save_path) = save_path {
                    let path = Path::new(save_path.as_str());
                    if let Some(parent) = path.parent() {
                        if !parent.as_os_str().is_empty() {
                            if let Err(error) = fs::create_dir_all(parent) {
                                eprintln!(
                                    "failed to create graph output directory for {}: {}",
                                    save_path, error
                                );
                                process::exit(1);
                            }
                        }
                    }
                    if let Err(error) = fs::write(path, format!("{}\n", trimmed_output)) {
                        eprintln!("failed to write graph JSON to {}: {}", save_path, error);
                        process::exit(1);
                    }
                    println!("saved graph JSON to {}", save_path);
                } else {
                    println!("{}", trimmed_output);
                }
                if !ok {
                    process::exit(1);
                }
                return;
            }
            "-latex" => {
                index += 1;
                if index >= args.len() {
                    run_latex_repl(VERSION);
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
                        compile_file_to_latex(file_path.as_str(), output_language)
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
                        compile_code_to_latex(code.as_str(), output_language)
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
                        compile_file_to_latex(joined_string.as_str(), output_language)
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
            "-python" => {
                index += 1;
                let python_target_flag =
                    match read_any_value_after_flag(&args, &mut index, "-python") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_help_message();
                            process::exit(2);
                        }
                    };
                let python_output_result = match python_target_flag.as_str() {
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
                        compile_file_to_python(file_path.as_str(), output_language)
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
                        compile_code_to_python(code.as_str(), output_language)
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
                        compile_file_to_python(joined_string.as_str(), output_language)
                    }
                    _ => {
                        eprintln!(
                            "-python must be followed by one of: -f <file>, -e <code>, -r <repo>"
                        );
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", python_output_result);
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

    run_repl_with_detail_output_and_strict_and_language(
        VERSION,
        detail_output,
        strict_mode,
        output_language,
    );
}

fn remove_flag(args: &mut Vec<String>, flag_name: &str) -> bool {
    let before_len = args.len();
    args.retain(|arg| arg != flag_name);
    args.len() != before_len
}

fn remove_language_flag(args: &mut Vec<String>) -> Result<OutputLanguage, String> {
    let Some(flag_index) = args.iter().position(|arg| arg == LANGUAGE_FLAG) else {
        return Ok(OutputLanguage::English);
    };

    if flag_index + 1 >= args.len() {
        return Err(format!(
            "{} requires a value: {}",
            LANGUAGE_FLAG,
            OutputLanguage::supported_codes_text()
        ));
    }

    let value = args.remove(flag_index + 1);
    args.remove(flag_index);
    OutputLanguage::from_cli_lang(value.as_str())
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

fn main_flag_file(
    file_flag: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) {
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

    let output = run_source_code_in_file_for_cli_with_strict_and_language(
        path_string.as_str(),
        detail_output,
        strict_mode,
        output_language,
    );
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
}

fn main_flag_runner(
    args: &[String],
    index: &mut usize,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> Result<(bool, String), String> {
    let target_flag = read_any_value_after_flag(args, index, "-runner")?;
    let hide_file_paths = !detail_output;
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let output = if strict_mode {
                run_runner_for_code_strict_with_language(
                    code.as_str(),
                    "-runner -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_runner_for_code_with_language(
                    code.as_str(),
                    "-runner -e",
                    hide_file_paths,
                    output_language,
                )
            };
            Ok(output)
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            Ok(run_runner_for_file_with_strict_and_language(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            ))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            Ok(run_runner_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            ))
        }
        _ => Err("-runner must be followed by one of: -f <file>, -e <code>, -r <repo>".to_string()),
    }
}

fn main_flag_graph(
    args: &[String],
    index: &mut usize,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> Result<(bool, String, Option<String>), String> {
    let target_flag = read_any_value_after_flag(args, index, "-graph")?;
    let hide_file_paths = !detail_output;
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let save_path = read_optional_graph_save_path(args, index)?;
            let output = if strict_mode {
                run_graph_for_code_strict_with_language(
                    code.as_str(),
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_graph_for_code_with_language(
                    code.as_str(),
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            };
            Ok((output.0, output.1, save_path))
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            let save_path = read_optional_graph_save_path(args, index)?;
            let output = run_graph_for_file_with_strict_and_language(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            );
            Ok((output.0, output.1, save_path))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            let save_path = read_optional_graph_save_path(args, index)?;
            let output = run_graph_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            );
            Ok((output.0, output.1, save_path))
        }
        _ => Err(
            "-graph must be followed by one of: -f <file> [json], -e <code> [json], -r <repo> [json]"
                .to_string(),
        ),
    }
}

fn read_optional_graph_save_path(
    args: &[String],
    index: &mut usize,
) -> Result<Option<String>, String> {
    let save_path = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => {
            *index += 1;
            Some(candidate.clone())
        }
        _ => None,
    };

    if let Some(unexpected) = args.get(*index) {
        return Err(format!(
            "unexpected argument after -graph target: {}",
            unexpected
        ));
    }

    Ok(save_path)
}

fn string_with_trimmed_outer_newlines(text: &str) -> String {
    text.trim().to_string()
}

fn compile_code_to_latex(code: &str, output_language: OutputLanguage) -> String {
    let code = remove_windows_carriage_return(code);
    match to_latex_from_source_after_builtins(code.as_str(), "-latex -e") {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

fn compile_file_to_latex(file_path: &str, output_language: OutputLanguage) -> String {
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_return(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_latex_from_source_after_builtins(source.as_str(), file_path) {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

fn compile_code_to_python(code: &str, output_language: OutputLanguage) -> String {
    let code = remove_windows_carriage_return(code);
    match to_python_from_source_after_builtins(code.as_str(), "-python -e") {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

fn compile_file_to_python(file_path: &str, output_language: OutputLanguage) -> String {
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_return(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_python_from_source_after_builtins(source.as_str(), file_path) {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
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

/// Print instructions instead of running a package manager.
/// Litex can be installed by Homebrew, release packages, or source builds, so
/// startup should not perform network or system changes on the user's machine.
fn upgrade_message(version: &str) -> String {
    let mut result = format!("Litex version {}\n\nUpgrade Litex:\n", version);

    if cfg!(target_os = "macos") {
        result.push_str("macOS with Homebrew:\n");
        result.push_str("  brew update\n");
        result.push_str("  brew upgrade litexlang/tap/litex\n\n");
    } else if cfg!(target_os = "linux") {
        result.push_str("Linux with the .deb release package:\n");
        result.push_str(
            "  Download the latest litex_<tag>_amd64.deb from GitHub Releases and run:\n",
        );
        result.push_str("  sudo dpkg -i litex_<tag>_amd64.deb\n\n");
    } else if cfg!(target_os = "windows") {
        result.push_str("Windows release zip install:\n");
        result.push_str("  Rerun the PowerShell install command from docs/Setup.md.\n\n");
    } else {
        result.push_str("Open the latest GitHub Release and install the package for your OS.\n\n");
    }

    result.push_str("Release page: https://github.com/litexlang/golitex/releases/latest\n");
    result.push_str("Full setup notes: https://litexlang.com/doc/Setup");
    result
}

fn help_message() -> String {
    let result = r#"litex : run Litex interactively in your terminal
litex -f <file> : run the given file
litex -r <repo> : run the given repository
litex -e <code> : execute the given code
litex -runner -f <file> : run a file and return one wrapper JSON object
litex -runner -e <code> : run source code and return one wrapper JSON object
litex -runner -r <repo> : run a repository and return one wrapper JSON object
litex -graph -f <file> <json> : run a file and save a prop/function/fact relation graph JSON object
litex -graph -e <code> <json> : run source code and save a prop/function/fact relation graph JSON object
litex -graph -r <repo> <json> : run a repository and save a prop/function/fact relation graph JSON object
litex -latex : run Litex interactively and print LaTeX output in your terminal
litex -latex -f <file> : compile the given file to LaTeX
litex -latex -e <code> : compile the given code to LaTeX
litex -latex -r <repo> : compile the given repository to LaTeX
litex -python -f <file> : compile supported verified Litex definitions to Python
litex -python -e <code> : compile supported verified Litex code to Python
litex -python -r <repo> : compile supported definitions in the repository main.lit to Python
litex -help : show the help message
litex -version : show the version
litex -upgrade : show upgrade instructions for this platform
litex -detail : include full trace details and raw source paths in JSON output
litex -strict : reject user proof_debt, suppose, and axiom statements after builtin initialization
litex -lang <en|zh|zh-Hans|ja|ko|es|fr|de|pt|ru|ar|hi|vi|id> : choose output language
litex -fmt : format the given code
litex -install <module> : install the given module
litex -uninstall <module> : uninstall the given module
litex -list : list all installed modules
litex -update <module> : update the given module
litex -tutorial : run the tutorial
"#;
    result.to_string()
}

#[cfg(test)]
mod tests {
    use super::{help_message, upgrade_message};

    #[test]
    fn help_lists_upgrade_command() {
        let message = help_message();
        assert!(message.contains("litex -upgrade"));
    }

    #[test]
    fn help_lists_strict_command() {
        let message = help_message();
        assert!(message.contains("litex -strict"));
    }

    #[test]
    fn help_lists_python_command() {
        let message = help_message();
        assert!(message.contains("litex -python -f <file>"));
    }

    #[test]
    fn help_lists_graph_command() {
        let message = help_message();
        assert!(message.contains("litex -graph -f <file> <json>"));
    }

    #[test]
    fn upgrade_message_mentions_version_and_release_page() {
        let message = upgrade_message("test-version");
        assert!(message.contains("Litex version test-version"));
        assert!(message.contains("https://github.com/litexlang/golitex/releases/latest"));
    }
}
