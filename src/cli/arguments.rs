use crate::common::output_language::OutputLanguage;
use crate::pipeline::SessionPreload;
use crate::runtime::OutputStyle;

const DETAIL_FLAG: &str = "-detail";
const COMPACT_FLAG: &str = "-compact";
const STRICT_FLAG: &str = "-strict";
const LANGUAGE_FLAG: &str = "-lang";
const SUMMARIZE_FLAG: &str = "-summarize";
const ISOLATED_FLAG: &str = "-isolated";
const TRUST_BEFORE_LINE_FLAG: &str = "-trust-before-line";
const TRACE_PIPELINE_FLAG: &str = "-trace-pipeline";

pub struct CliOptions {
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub summarize_output: bool,
    pub force_isolated: bool,
    pub output_language: OutputLanguage,
    pub trust_before_line: Option<usize>,
    pub trace_pipeline: bool,
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
    let trace_pipeline = remove_flag(args, TRACE_PIPELINE_FLAG);
    let trust_before_line = remove_trust_before_line_flag(args)?;
    validate_trust_before_line_invocation(args, strict_mode, trust_before_line)?;
    validate_trace_pipeline_invocation(args, trace_pipeline)?;

    Ok(CliOptions {
        output_style,
        strict_mode,
        summarize_output,
        force_isolated,
        output_language,
        trust_before_line,
        trace_pipeline,
    })
}

pub fn validate_trace_pipeline_invocation(
    args: &[String],
    trace_pipeline: bool,
) -> Result<(), String> {
    if !trace_pipeline {
        return Ok(());
    }
    match args.first().map(String::as_str) {
        Some("-e" | "-f" | "-r" | "-runner") => Ok(()),
        _ => Err(
            "-trace-pipeline is supported only with -e, -f, -r, or -runner batch execution"
                .to_string(),
        ),
    }
}

fn remove_flag(args: &mut Vec<String>, flag_name: &str) -> bool {
    let before_len = args.len();
    args.retain(|arg| arg != flag_name);
    args.len() != before_len
}

pub fn remove_trust_before_line_flag(args: &mut Vec<String>) -> Result<Option<usize>, String> {
    let flag_count = args
        .iter()
        .filter(|arg| arg.as_str() == TRUST_BEFORE_LINE_FLAG)
        .count();
    if flag_count == 0 {
        return Ok(None);
    }
    if flag_count > 1 {
        return Err(format!(
            "{} may be provided only once",
            TRUST_BEFORE_LINE_FLAG
        ));
    }

    let flag_index = args
        .iter()
        .position(|arg| arg == TRUST_BEFORE_LINE_FLAG)
        .expect("the trust-before-line flag count was already checked");
    let Some(value) = args.get(flag_index + 1) else {
        return Err(format!(
            "{} requires a positive ASCII decimal line number",
            TRUST_BEFORE_LINE_FLAG
        ));
    };
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!(
            "{} requires a positive ASCII decimal line number, got {}",
            TRUST_BEFORE_LINE_FLAG, value
        ));
    }
    let line = value.parse::<usize>().map_err(|_| {
        format!(
            "{} line number exceeds the supported range: {}",
            TRUST_BEFORE_LINE_FLAG, value
        )
    })?;
    if line == 0 {
        return Err(format!(
            "{} requires a line number greater than 0",
            TRUST_BEFORE_LINE_FLAG
        ));
    }

    args.remove(flag_index + 1);
    args.remove(flag_index);
    Ok(Some(line))
}

pub fn validate_trust_before_line_invocation(
    args: &[String],
    strict_mode: bool,
    trust_before_line: Option<usize>,
) -> Result<(), String> {
    if trust_before_line.is_none() {
        return Ok(());
    }
    if strict_mode {
        return Err(format!(
            "{} cannot be used with {}",
            TRUST_BEFORE_LINE_FLAG, STRICT_FLAG
        ));
    }
    if args.len() != 2 || args.first().map(String::as_str) != Some("-f") {
        return Err(format!(
            "{} is supported only with a direct -f <file> or -isolated -f <file> command and does not accept additional arguments",
            TRUST_BEFORE_LINE_FLAG
        ));
    }
    if args
        .get(1)
        .map(|file| file.is_empty() || file.starts_with('-'))
        .unwrap_or(true)
    {
        return Err(format!(
            "{} requires a direct -f <file> target",
            TRUST_BEFORE_LINE_FLAG
        ));
    }
    Ok(())
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
