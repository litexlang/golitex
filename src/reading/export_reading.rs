use crate::prelude::*;
use std::fs;
use std::path::Path;

pub const READER_JS: &str = include_str!("web/reader.js");
pub const READER_CSS: &str = include_str!("web/reader.css");
pub const APP_JS: &str = include_str!("web/app.js");

pub fn reading_html(document: &JsonValue, live: bool) -> String {
    let data = document
        .stringify()
        .replace('<', "\\u003c")
        .replace('\u{2028}', "\\u2028")
        .replace('\u{2029}', "\\u2029");
    include_str!("web/index.html")
        .replace(
            "__LITEX_READING_LIVE__",
            if live { "true" } else { "false" },
        )
        .replace("__LITEX_READING_DATA__", &data)
}

pub fn export_reading(path: &Path, document: &JsonValue) -> RuntimeResult<()> {
    fs::create_dir_all(path).map_err(|error| RuntimeError::Io {
        path: path.into(),
        message: error.to_string(),
    })?;
    for (name, content) in [
        ("index.html", reading_html(document, false)),
        ("reader.js", READER_JS.into()),
        ("reader.css", READER_CSS.into()),
        ("app.js", APP_JS.into()),
        ("reading.json", document.stringify_pretty()),
    ] {
        let file = path.join(name);
        fs::write(&file, content).map_err(|error| RuntimeError::Io {
            path: file,
            message: error.to_string(),
        })?;
    }
    Ok(())
}
