use crate::prelude::*;

pub(super) fn print_help_message() {
    println!("{}", help_message());
}

pub(super) fn help_message() -> String {
    let entries = [
        ("litex", "Start the interactive Litex REPL."),
        ("litex -help", "Show this help."),
        ("litex -version", "Show the Litex version."),
        ("litex -e <code>", "Run inline Litex source."),
        (
            "litex -f <file>",
            "Run a file using project context when directly configured, otherwise in isolation.",
        ),
        (
            "litex -isolated -f <file>",
            "Run a file in forced isolation.",
        ),
        ("litex -r <directory>", "Run a Litex module."),
        ("litex -session", "Start a framed machine session."),
        (
            "litex -session -f <file>",
            "Load a file with automatic context and continue in a framed session.",
        ),
        (
            "litex -isolated -session -f <file>",
            "Load a standalone file and continue in a framed session.",
        ),
        (
            "litex -graph <-e|-f|-r> <target> [output.json]",
            "Produce a recursive result graph.",
        ),
        (
            "litex -factgraph <-e|-f|-r> <target> [output.json]",
            "Produce a fact dependency graph.",
        ),
        (
            "litex -defgraph <-e|-f|-r> <target> [output.json]",
            "Produce a definition dependency graph.",
        ),
        ("litex -latex", "Start the interactive LaTeX REPL."),
        (
            "litex -latex <-e|-f|-r> <target>",
            "Render Litex source as LaTeX.",
        ),
        (
            "litex -extractpython <code>",
            "Extract supported executable definitions as Python.",
        ),
        (
            "litex -extractpython <-f|-r> <target>",
            "Extract a file or module as Python.",
        ),
        (
            "litex -extractc <code>",
            "Extract supported executable definitions as C99.",
        ),
        (
            "litex -extractc <-f|-r> <target>",
            "Extract a file or module as C99.",
        ),
        (
            "litex -isolated -f <input.lit> -lean <output.lean>",
            "Verify one standalone file and compile it to Lean.",
        ),
        ("-strict", "Verify dependencies and reject unchecked trust."),
        ("-lang <language>", "Select human-readable output language."),
        (
            "-isolated",
            "Run a supported file target without a project.",
        ),
    ]
    .into_iter()
    .map(|(usage, description)| {
        JsonValue::Object(vec![
            (
                "usage".to_string(),
                JsonValue::JsonString(usage.to_string()),
            ),
            (
                "description".to_string(),
                JsonValue::JsonString(description.to_string()),
            ),
        ])
    })
    .collect::<Vec<_>>();

    render_json_value(
        &JsonValue::Object(vec![
            (
                "kind".to_string(),
                JsonValue::JsonString("help".to_string()),
            ),
            ("ok".to_string(), JsonValue::Bool(true)),
            ("entries".to_string(), JsonValue::Array(entries)),
        ]),
        0,
    )
}
