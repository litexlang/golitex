use crate::prelude::*;
use std::path::PathBuf;

use super::{ReadingAction, ReadingCommand, ReadingInput};

/// Reading has its own service lifecycle; it is dispatched before kernel commands.
pub fn parse_reading_command(args: &[String]) -> RuntimeResult<Option<ReadingCommand>> {
    let mut cursor = 0;
    let mut selected = false;
    while cursor < args.len() {
        let arg = args[cursor].as_str();
        if matches!(arg, "-reading" | "--reading") {
            selected = true;
        }
        cursor += if matches!(
            arg,
            "-e" | "-f" | "-r" | "-lang" | "--lang" | "-export" | "-port"
        ) {
            2
        } else {
            1
        };
    }
    if !selected {
        return Ok(None);
    }

    let mut input = ReadingInput::Empty;
    let mut action = None;
    let mut strict = false;
    let mut language = OutputLanguage::English;
    let mut open_browser = true;
    let mut port = 0;
    let mut preview_options = false;
    let mut reading_count = 0;
    let mut cursor = 0;
    while cursor < args.len() {
        let arg = args[cursor].as_str();
        cursor += 1;
        match arg {
            "-reading" | "--reading" => {
                reading_count += 1;
            }
            "-e" | "-f" | "-r" => {
                if input != ReadingInput::Empty {
                    return Err(arguments("select one reading source: -e, -f or -r"));
                }
                let value = operand(args, &mut cursor, arg)?;
                input = match arg {
                    "-e" => ReadingInput::Source(value),
                    "-f" => ReadingInput::File(PathBuf::from(value)),
                    _ => ReadingInput::Project(PathBuf::from(value)),
                };
            }
            "-json" => {
                if action.is_some() {
                    return Err(arguments(
                        "select one reading action: preview, -json or -export",
                    ));
                }
                action = Some(ReadingAction::Json);
            }
            "-export" => {
                if action.is_some() {
                    return Err(arguments(
                        "select one reading action: preview, -json or -export",
                    ));
                }
                action = Some(ReadingAction::Export(PathBuf::from(operand(
                    args,
                    &mut cursor,
                    arg,
                )?)));
            }
            "-strict" | "--strict" => strict = true,
            "-lang" | "--lang" => {
                language = OutputLanguage::parse_token(&operand(args, &mut cursor, arg)?)?
            }
            "-no-browser" => {
                open_browser = false;
                preview_options = true;
            }
            "-port" => {
                port = operand(args, &mut cursor, arg)?
                    .parse()
                    .map_err(|_| arguments("-port expects an integer from 0 to 65535"))?;
                preview_options = true;
            }
            _ => return Err(arguments(&format!("unsupported reading argument `{arg}`"))),
        }
    }
    if reading_count != 1 {
        return Err(arguments("-reading may appear only once"));
    }
    if action.is_some() && preview_options {
        return Err(arguments(
            "-port and -no-browser apply only to reading preview",
        ));
    }
    let action = action.unwrap_or(ReadingAction::Preview { port, open_browser });
    if input == ReadingInput::Empty && !matches!(action, ReadingAction::Preview { .. }) {
        return Err(arguments(
            "reading JSON/export requires -e <code>, -f <file> or -r <project>",
        ));
    }
    Ok(Some(ReadingCommand::new(input, action, strict, language)))
}

fn operand(args: &[String], cursor: &mut usize, flag: &str) -> RuntimeResult<String> {
    let value = args
        .get(*cursor)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| arguments(&format!("{flag} requires a nonempty operand")))?;
    *cursor += 1;
    Ok(value.clone())
}

fn arguments(message: &str) -> RuntimeError {
    RuntimeError::InvalidArguments(message.into())
}
