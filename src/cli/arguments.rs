use crate::output::{language::OutputLanguage, style::OutputStyle};
use crate::pipeline::{FileRunMode, SessionTarget};
use crate::runtime::RunOptions;

const DETAIL_FLAG: &str = "-detail";
const COMPACT_FLAG: &str = "-compact";
const STRICT_FLAG: &str = "-strict";
const LANGUAGE_FLAG: &str = "-lang";
const SUMMARIZE_FLAG: &str = "-summarize";
const ISOLATED_FLAG: &str = "-isolated";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GlobalOptions {
    pub run: RunOptions,
    pub isolated: bool,
}

pub fn parse_global_options(args: &mut Vec<String>) -> Result<GlobalOptions, String> {
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
    let isolated = remove_flag(args, ISOLATED_FLAG);
    let output_language = remove_language_flag(args)?;

    Ok(GlobalOptions {
        run: RunOptions {
            output_style,
            strict_mode,
            summarize,
            output_language,
        },
        isolated,
    })
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

pub fn reject_meaningless_isolated(isolated: bool, target: &str) -> Result<(), String> {
    if isolated {
        return Err(format!(
            "-isolated has no meaning with {}; use it with -f, -session, or the REPL",
            target
        ));
    }
    Ok(())
}
