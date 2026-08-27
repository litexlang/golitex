use crate::common::output_language::OutputLanguage;
use crate::pipeline::{RunOptions, SessionPreload};
use crate::runtime::OutputStyle;

const DETAIL_FLAG: &str = "-detail";
const COMPACT_FLAG: &str = "-compact";
const STRICT_FLAG: &str = "-strict";
const LANGUAGE_FLAG: &str = "-lang";
const SUMMARIZE_FLAG: &str = "-summarize";
const ISOLATED_FLAG: &str = "-isolated";

pub struct CliOptions {
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub summarize_output: bool,
    pub force_isolated: bool,
    pub output_language: OutputLanguage,
}

impl CliOptions {
    pub fn run_options(&self) -> RunOptions {
        RunOptions {
            output_style: self.output_style,
            strict_mode: self.strict_mode,
            output_language: self.output_language,
            summarize: self.summarize_output,
            force_isolated: self.force_isolated,
        }
    }
}

pub fn parse_global_options(args: &mut Vec<String>) -> Result<CliOptions, String> {
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
    let summarize_output = remove_flag(args, SUMMARIZE_FLAG);
    let force_isolated = remove_flag(args, ISOLATED_FLAG);
    let output_language = remove_language_flag(args)?;

    Ok(CliOptions {
        output_style,
        strict_mode,
        summarize_output,
        force_isolated,
        output_language,
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

pub fn read_session_preload(args: &[String], index: &mut usize) -> Result<SessionPreload, String> {
    if *index == args.len() {
        return Ok(SessionPreload::None);
    }
    let flag = args.get(*index).map(String::as_str).unwrap_or_default();
    *index += 1;
    let file = match flag {
        "-f" => read_non_flag_value_after_flag(args, index, "-f")?,
        "-before" => read_non_flag_value_after_flag(args, index, "-before")?,
        _ => {
            return Err(
                "-session accepts only an optional -f <file> or -before <file> target".to_string(),
            );
        }
    };
    if *index != args.len() {
        return Err(format!(
            "-session {} <file> does not accept additional arguments",
            flag
        ));
    }
    match flag {
        "-f" => Ok(SessionPreload::ThroughFile(file)),
        "-before" => Ok(SessionPreload::BeforeFile(file)),
        _ => unreachable!("session preload flag was already validated"),
    }
}

pub fn validate_session_preload(
    force_isolated: bool,
    preload: &SessionPreload,
) -> Result<(), String> {
    if force_isolated && matches!(preload, SessionPreload::BeforeFile(_)) {
        return Err(
            "-isolated cannot be used with -session -before; the target must be a registered project file"
                .to_string(),
        );
    }
    Ok(())
}
