use crate::prelude::*;
use crate::reading::{build_reading, export_reading, serve_reading, ReadingAction, ReadingCommand};

pub fn run_reading(command: ReadingCommand) -> RuntimeResult<bool> {
    let result = build_reading(&command.input, command.strict, command.language);
    match command.action {
        ReadingAction::Json => {
            super::output::write_stdout(format_args!("{}\n", result.document.stringify_pretty()))?
        }
        ReadingAction::Export(path) => {
            export_reading(&path, &result.document)?;
            let summary = JsonValue::object_from(vec![
                ("kind".into(), JsonValue::String("reading_export".into())),
                ("path".into(), JsonValue::String(path.display().to_string())),
                (
                    "run_result".into(),
                    JsonValue::String(if result.success { "success" } else { "failure" }.into()),
                ),
            ]);
            super::output::write_stdout(format_args!("{}\n", summary.stringify_pretty()))?;
        }
        ReadingAction::Preview { port, open_browser } => {
            serve_reading(result.document, port, open_browser, command.strict)?
        }
    }
    Ok(result.success)
}
