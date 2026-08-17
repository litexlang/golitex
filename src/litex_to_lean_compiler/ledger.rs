use super::compile_source;
use std::collections::HashSet;
use std::fs;
use std::path::Path;

pub(super) struct LitexLedgerExample {
    pub(super) label: String,
    pub(super) source: String,
}

struct CompiledLedgerExample {
    label: String,
    imports: Vec<String>,
    body: String,
}

pub fn compile_markdown_ledger_file_to_lean(
    ledger_path: &Path,
    output_path: &Path,
) -> Result<usize, String> {
    reject_same_input_and_output(ledger_path, output_path)?;

    let markdown = fs::read_to_string(ledger_path)
        .map_err(|error| format!("failed to read {}: {error}", ledger_path.display()))?;
    let examples = parse_litex_ledger_examples(&markdown)?;
    let mut compiled = Vec::with_capacity(examples.len());

    for example in examples {
        let source_label = format!("{}#{}", ledger_path.display(), example.label);
        let generated = compile_source(&example.source, &source_label).map_err(|error| {
            format!(
                "ledger entry {} failed to compile from {}: {error}",
                example.label,
                ledger_path.display()
            )
        })?;
        let (imports, body) = split_generated_lean(&generated).map_err(|message| {
            format!(
                "ledger entry {} produced an invalid complete Lean file: {message}",
                example.label
            )
        })?;
        compiled.push(CompiledLedgerExample {
            label: example.label,
            imports,
            body,
        });
    }

    let count = compiled.len();
    let output = render_compiled_ledger(ledger_path, &compiled);
    if let Some(parent) = output_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|error| {
                format!(
                    "failed to create output directory {}: {error}",
                    parent.display()
                )
            })?;
        }
    }
    fs::write(output_path, output)
        .map_err(|error| format!("failed to write {}: {error}", output_path.display()))?;
    Ok(count)
}

pub(super) fn parse_litex_ledger_examples(
    markdown: &str,
) -> Result<Vec<LitexLedgerExample>, String> {
    let mut heading: Option<String> = None;
    let mut active_label: Option<String> = None;
    let mut litex_fence_line = None;
    let mut in_other_fence = false;
    let mut source = String::new();
    let mut labels = HashSet::new();
    let mut examples = Vec::new();

    for (line_index, line) in markdown.lines().enumerate() {
        let line_number = line_index + 1;
        let trimmed = line.trim();

        if active_label.is_some() {
            if trimmed == "```" {
                let label = active_label
                    .take()
                    .expect("an active Litex fence must retain its heading");
                if source.trim().is_empty() {
                    return Err(format!(
                        "Litex fence for {label} at line {} is empty",
                        litex_fence_line.unwrap_or(line_number)
                    ));
                }
                if !labels.insert(label.clone()) {
                    return Err(format!("duplicate Litex ledger heading: {label}"));
                }
                examples.push(LitexLedgerExample {
                    label,
                    source: source.clone(),
                });
                source.clear();
                litex_fence_line = None;
            } else {
                source.push_str(line);
                source.push('\n');
            }
            continue;
        }

        if in_other_fence {
            if trimmed == "```" {
                in_other_fence = false;
            }
            continue;
        }

        if trimmed == "```litex" {
            let label = heading.clone().ok_or_else(|| {
                format!(
                    "Litex fence at line {line_number} must follow a level-two Markdown heading"
                )
            })?;
            active_label = Some(label);
            litex_fence_line = Some(line_number);
            source.clear();
            continue;
        }
        if trimmed.starts_with("```") {
            in_other_fence = true;
            continue;
        }
        if let Some(value) = line.strip_prefix("## ") {
            let value = value.trim();
            if value.is_empty() {
                return Err(format!("empty level-two heading at line {line_number}"));
            }
            heading = Some(value.to_string());
        }
    }

    if let Some(label) = active_label {
        return Err(format!(
            "unterminated Litex fence for {label} opened at line {}",
            litex_fence_line.unwrap_or(markdown.lines().count())
        ));
    }
    if examples.is_empty() {
        return Err(
            "Markdown ledger contains no Litex fences under level-two headings".to_string(),
        );
    }
    Ok(examples)
}

fn split_generated_lean(generated: &str) -> Result<(Vec<String>, String), String> {
    let mut imports = Vec::new();
    let mut body = String::new();
    let mut body_started = false;

    for line in generated.lines() {
        if !body_started {
            if line.trim().is_empty() {
                continue;
            }
            if line.starts_with("-- Generated by compiler from ") {
                continue;
            }
            if line.starts_with("import ") {
                imports.push(line.to_string());
                continue;
            }
            body_started = true;
        }
        body.push_str(line);
        body.push('\n');
    }

    if body.trim().is_empty() {
        return Err("generated source has no declarations after its imports".to_string());
    }
    Ok((imports, body))
}

fn render_compiled_ledger(ledger_path: &Path, examples: &[CompiledLedgerExample]) -> String {
    let mut imports = Vec::new();
    for example in examples {
        for import in &example.imports {
            if !imports.contains(import) {
                imports.push(import.clone());
            }
        }
    }

    let source_label = ledger_path
        .display()
        .to_string()
        .replace('\r', " ")
        .replace('\n', " ");
    let entry_width = examples.len().to_string().len().max(2);
    let mut output = String::new();
    for import in imports {
        output.push_str(&import);
        output.push('\n');
    }
    if !output.is_empty() {
        output.push('\n');
    }
    output.push_str("-- Generated by litex -lean-ledger from fresh Litex compilation.\n");
    output.push_str(&format!("-- Source ledger: {source_label}\n"));
    output.push_str(&format!("-- Entries: {}\n\n", examples.len()));
    output.push_str("namespace LitexLedger\n\n");

    for (index, example) in examples.iter().enumerate() {
        let entry_number = index + 1;
        let namespace = format!("Entry{:0entry_width$}", entry_number);
        output.push_str(&format!(
            "-- BEGIN ENTRY {entry_number:0entry_width$}: {}\n",
            example.label
        ));
        output.push_str(&format!("namespace {namespace}\n\n"));
        output.push_str(example.body.trim_end());
        output.push_str("\n\n");
        output.push_str(&format!("end {namespace}\n"));
        output.push_str(&format!(
            "-- END ENTRY {entry_number:0entry_width$}: {}\n\n",
            example.label
        ));
    }

    output.push_str("end LitexLedger\n");
    output
}

fn reject_same_input_and_output(ledger_path: &Path, output_path: &Path) -> Result<(), String> {
    if ledger_path == output_path {
        return Err("the Markdown ledger and Lean output paths must be different".to_string());
    }

    let canonical_ledger = fs::canonicalize(ledger_path)
        .map_err(|error| format!("failed to resolve {}: {error}", ledger_path.display()))?;
    if output_path.exists() {
        let canonical_output = fs::canonicalize(output_path)
            .map_err(|error| format!("failed to resolve {}: {error}", output_path.display()))?;
        if canonical_ledger == canonical_output {
            return Err("the Markdown ledger and Lean output paths must be different".to_string());
        }
    }
    Ok(())
}
