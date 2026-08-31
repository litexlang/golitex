use crate::output::{language::OutputLanguage, style::OutputStyle};
use crate::pipeline::{FileRunMode, SessionTarget};
use crate::runtime::RunOptions;

const DETAIL_FLAG: &str = "-detail";
const COMPACT_FLAG: &str = "-compact";
const STRICT_FLAG: &str = "-strict";
const LANGUAGE_FLAG: &str = "-lang";
const SUMMARIZE_FLAG: &str = "-summarize";
const ISOLATED_FLAG: &str = "-isolated";

pub fn parse_global_options(args: &mut Vec<String>) -> Result<RunOptions, String> {
    let detail_output = remove_flag(args, DETAIL_FLAG);
    let compact_output = remove_flag(args, COMPACT_FLAG);
    if detail_output && compact_output {
        return Err("-compact and -detail cannot be used together".to_string());
    }

    let output_style = if compact_output {
        OutputStyle::Compact
    } else if detail_output {
        OutputStyle::Detailed
    } else {
        OutputStyle::Normal
    };
    let strict_mode = remove_flag(args, STRICT_FLAG);
    let summarize = remove_flag(args, SUMMARIZE_FLAG);
    let is_isolated = remove_flag(args, ISOLATED_FLAG);
    let output_language = remove_language_flag(args)?;

    Ok(RunOptions {
        output_style,
        strict_mode,
        summarize,
        output_language,
        is_isolated,
    })
}

pub fn validate_cli_combination(args: &[String], isolated: bool) -> Result<(), String> {
    let is_value = |index: usize| args.get(index).is_some_and(|value| !value.starts_with('-'));

    let valid = if args.is_empty() {
        true
    } else if args.len() == 1 {
        if args[0] == "-session" {
            true
        } else if isolated {
            false
        } else {
            matches!(args[0].as_str(), "-help" | "-version" | "-latex")
        }
    } else if args.len() == 2 {
        is_value(1)
            && if args[0] == "-f" {
                true
            } else if isolated {
                false
            } else {
                matches!(
                    args[0].as_str(),
                    "-e" | "-r" | "-extractpython" | "-extractc"
                )
            }
    } else if args.len() == 3 {
        let target_flag = args[1].as_str();
        is_value(2)
            && if args[0] == "-session" {
                target_flag == "-f"
            } else if matches!(args[0].as_str(), "-graph" | "-factgraph" | "-defgraph") {
                matches!(target_flag, "-e" | "-f" | "-r") && (!isolated || target_flag == "-f")
            } else if args[0] == "-latex" {
                matches!(target_flag, "-e" | "-f" | "-r") && (!isolated || target_flag == "-f")
            } else if matches!(args[0].as_str(), "-extractpython" | "-extractc") {
                matches!(target_flag, "-f" | "-r") && (!isolated || target_flag == "-f")
            } else {
                false
            }
    } else if args.len() == 4 {
        if args[0] == "-f" {
            isolated && is_value(1) && args[2] == "-lean" && is_value(3)
        } else {
            matches!(args[0].as_str(), "-graph" | "-factgraph" | "-defgraph")
                && matches!(args[1].as_str(), "-e" | "-f" | "-r")
                && (!isolated || args[1] == "-f")
                && is_value(2)
                && is_value(3)
        }
    } else {
        false
    };

    if valid {
        Ok(())
    } else {
        Err("unsupported CLI command combination".to_string())
    }
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
pub fn read_non_flag_value_after_flag(
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
pub fn read_any_value_after_flag(
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

pub fn read_session_target(
    args: &[String],
    index: &mut usize,
    isolated: bool,
) -> Result<SessionTarget, String> {
    if *index == args.len() {
        return Ok(if isolated {
            SessionTarget::Isolated
        } else {
            SessionTarget::CurrentDirectory
        });
    }
    let flag = args.get(*index).map(String::as_str).unwrap_or_default();
    *index += 1;
    let file = match flag {
        "-f" => read_non_flag_value_after_flag(args, index, "-f")?,
        _ => {
            return Err("-session accepts only an optional -f <file> target".to_string());
        }
    };
    if *index != args.len() {
        return Err(format!(
            "-session {} <file> does not accept additional arguments",
            flag
        ));
    }
    Ok(SessionTarget::File {
        path: file,
        mode: FileRunMode::from_isolated(isolated),
    })
}
