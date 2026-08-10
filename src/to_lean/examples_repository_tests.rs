use std::collections::HashSet;
use std::fs;
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use super::{
    to_lean_from_source, to_lean_from_source_with_report, ToLeanCompilationStatus,
    ToLeanUnsupportedPhase,
};

const TO_LEAN_EXAMPLES_MARKDOWN: &str = "examples/09_to_lean/litex_to_lean_examples.md";
const PARTIAL_EXAMPLE_MARKER: &str = "<!-- to-lean: partial -->";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ToLeanExampleMode {
    Strict,
    Partial,
}

struct ToLeanMarkdownExample {
    name: String,
    mode: ToLeanExampleMode,
    litex_source: String,
    lean_snapshot: String,
    lean_body_range: Range<usize>,
}

#[test]
fn to_lean_examples_markdown_emits_checked_source() {
    run_with_large_stack("to_lean_examples_markdown_emits_checked_source", || {
        let markdown = fs::read_to_string(example_markdown_path()).unwrap();
        let examples = parse_to_lean_markdown_examples(&markdown);
        let mut strict_failures = Vec::new();
        let mut saw_native_carriers = false;
        let mut saw_propositions_and_trust = false;
        let mut saw_carrier_boundaries = false;
        let mut saw_partial_boundary = false;

        for example in examples.iter() {
            match example.mode {
                ToLeanExampleMode::Strict => {
                    let generated = match to_lean_from_source(
                        &example.litex_source,
                        &example_entry_label(&example.name),
                    ) {
                        Ok(generated) => generated,
                        Err(error) => {
                            let report = to_lean_from_source_with_report(
                                &example.litex_source,
                                &example_entry_label(&example.name),
                            )
                            .unwrap();
                            strict_failures.push(format!(
                                "strict To-Lean failed for {}: {}\nunsupported: {:#?}",
                                example.name,
                                error.trace_message(),
                                report.unsupported
                            ));
                            continue;
                        }
                    };

                    assert_common_generated_contract(example, &generated);
                    if example.name == "propositions_and_trust" {
                        saw_propositions_and_trust = true;
                        assert_eq!(generated.matches("\naxiom fact").count(), 4);
                        assert!(
                            generated.contains("∀ x ∈ (Set.univ : Set ℝ), x ∈ (Set.univ : Set ℝ)"),
                            "{}",
                            generated
                        );
                        assert!(
                            generated.contains(
                                "∀ z ∈ (Set.univ : Set ℤ), (z / 2 : ℚ) ∈ (Set.univ : Set ℚ)"
                            ),
                            "{}",
                            generated
                        );
                    } else {
                        assert!(!generated.contains("\naxiom fact"), "{}", example.name);
                    }

                    if example.name == "native_carriers" {
                        saw_native_carriers = true;
                        assert!(generated.contains("2 = 2"), "{}", generated);
                        assert!(
                            generated.contains("2 ∈ (Set.univ : Set ℝ)"),
                            "{}",
                            generated
                        );
                    }

                    assert_generated_snapshot_matches(example, &generated);
                    println!(
                        "To-Lean strict Markdown example OK: {} ({} Lean bytes)",
                        example.name,
                        generated.len()
                    );
                }
                ToLeanExampleMode::Partial => {
                    let report = to_lean_from_source_with_report(
                        &example.litex_source,
                        &example_entry_label(&example.name),
                    )
                    .unwrap();

                    assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                    assert!(!report.unsupported.is_empty(), "{}", example.name);
                    assert!(!report.lean_code.contains("sorry"), "{}", example.name);
                    assert!(
                        !report.lean_code.contains("\naxiom fact"),
                        "{}",
                        example.name
                    );

                    if example.name == "carrier_boundaries" {
                        saw_carrier_boundaries = true;
                        assert_eq!(report.unsupported.len(), 11);
                        assert!(report.unsupported[0].statement.contains("n + 1"));
                        assert!(report.unsupported[10]
                            .statement
                            .contains("boundary_complex_one"));
                    } else if example.name == "partial_boundary" {
                        saw_partial_boundary = true;
                        assert_eq!(report.unsupported.len(), 1);
                        assert_eq!(report.unsupported[0].statement_index, 2);
                        assert_eq!(
                            report.unsupported[0].phase,
                            ToLeanUnsupportedPhase::LeanEmission
                        );
                        assert!(report.unsupported[0].statement.contains("sin"));
                        assert_eq!(report.lean_code.matches("theorem fact").count(), 2);
                    }

                    assert_generated_snapshot_matches(example, &report.lean_code);
                    println!(
                        "To-Lean partial Markdown example OK: {} ({} explicit omissions, {} Lean bytes)",
                        example.name,
                        report.unsupported.len(),
                        report.lean_code.len()
                    );
                }
            }
        }

        assert!(
            strict_failures.is_empty(),
            "{}",
            strict_failures.join("\n\n")
        );
        assert!(saw_native_carriers, "native_carriers example is missing");
        assert!(
            saw_propositions_and_trust,
            "propositions_and_trust example is missing"
        );
        assert!(
            saw_carrier_boundaries,
            "carrier_boundaries partial example is missing"
        );
        assert!(
            saw_partial_boundary,
            "partial_boundary partial example is missing"
        );
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing at a Mathlib Lake project"]
fn generated_to_lean_examples_markdown_compiles_with_mathlib() {
    run_with_large_stack(
        "generated_to_lean_examples_markdown_compiles_with_mathlib",
        || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("LITEX_LEAN_PROJECT must point at a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let markdown = fs::read_to_string(example_markdown_path()).unwrap();
            let examples = parse_to_lean_markdown_examples(&markdown);
            let mut failures = Vec::new();

            for example in examples.iter() {
                let generated = match example.mode {
                    ToLeanExampleMode::Strict => to_lean_from_source(
                        &example.litex_source,
                        &example_entry_label(&example.name),
                    )
                    .unwrap(),
                    ToLeanExampleMode::Partial => {
                        let report = to_lean_from_source_with_report(
                            &example.litex_source,
                            &example_entry_label(&example.name),
                        )
                        .unwrap();
                        assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                        report.lean_code
                    }
                };
                if let Err(failure) =
                    compile_generated_with_mathlib(&example.name, &generated, &project, &lake)
                {
                    failures.push(failure);
                }
            }

            assert!(failures.is_empty(), "{}", failures.join("\n\n"));
        },
    );
}

#[test]
#[ignore = "rewrites generated Lean fences in the consolidated example Markdown"]
fn refresh_to_lean_examples_markdown_snapshots() {
    run_with_large_stack("refresh_to_lean_examples_markdown_snapshots", || {
        let path = example_markdown_path();
        let markdown = fs::read_to_string(&path).unwrap();
        let examples = parse_to_lean_markdown_examples(&markdown);
        let mut generated_snapshots = Vec::new();

        for example in examples.iter() {
            let generated = match example.mode {
                ToLeanExampleMode::Strict => {
                    to_lean_from_source(&example.litex_source, &example_entry_label(&example.name))
                        .unwrap()
                }
                ToLeanExampleMode::Partial => {
                    let report = to_lean_from_source_with_report(
                        &example.litex_source,
                        &example_entry_label(&example.name),
                    )
                    .unwrap();
                    assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                    report.lean_code
                }
            };
            println!("Refreshed Markdown Lean snapshot: {}", example.name);
            generated_snapshots.push(generated);
        }

        let refreshed =
            markdown_with_refreshed_lean_snapshots(&markdown, &examples, &generated_snapshots);
        fs::write(path, refreshed).unwrap();
    });
}

#[test]
fn parses_strict_and_partial_markdown_example_pairs() {
    let markdown = r#"# Examples

## strict_example

```litex
2 = 2
```

```lean
theorem strictExample : 2 = 2 := by norm_num
```

## partial_example

<!-- to-lean: partial -->

```litex
sin(0) = 0
```

```lean
-- incomplete
```
"#;
    let examples = parse_to_lean_markdown_examples(markdown);

    assert_eq!(examples.len(), 2);
    assert_eq!(examples[0].name, "strict_example");
    assert_eq!(examples[0].mode, ToLeanExampleMode::Strict);
    assert_eq!(examples[1].name, "partial_example");
    assert_eq!(examples[1].mode, ToLeanExampleMode::Partial);
}

#[test]
#[should_panic(expected = "must contain exactly one lean fenced block")]
fn rejects_markdown_example_without_lean_pair() {
    let markdown = r#"# Examples

## unpaired

```litex
2 = 2
```
"#;
    let _ = parse_to_lean_markdown_examples(markdown);
}

fn example_markdown_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(TO_LEAN_EXAMPLES_MARKDOWN)
}

fn example_entry_label(name: &str) -> String {
    format!("{}#{}", TO_LEAN_EXAMPLES_MARKDOWN, name)
}

fn assert_common_generated_contract(example: &ToLeanMarkdownExample, generated: &str) {
    assert!(
        generated.starts_with("import Mathlib\n"),
        "{}",
        example.name
    );
    assert!(!generated.contains("sorry"), "{}", example.name);
    assert!(!generated.contains("LitexSet"), "{}", example.name);
    assert!(!generated.contains("LitexAddEq"), "{}", example.name);
}

fn assert_generated_snapshot_matches(example: &ToLeanMarkdownExample, generated: &str) {
    assert_eq!(
        example.lean_snapshot.trim_end(),
        generated.trim_end(),
        "generated Lean snapshot is stale for {}; run the Markdown refresh test",
        example.name
    );
}

fn parse_to_lean_markdown_examples(markdown: &str) -> Vec<ToLeanMarkdownExample> {
    let mut headings: Vec<(usize, usize, String)> = Vec::new();
    let mut in_fence = false;
    let mut offset = 0;

    for line in markdown.split_inclusive('\n') {
        let line_without_ending = line.trim_end_matches('\n').trim_end_matches('\r');
        let trimmed_start = line_without_ending.trim_start();
        if trimmed_start.starts_with("```") {
            in_fence = !in_fence;
        } else if !in_fence {
            if let Some(name) = line_without_ending.strip_prefix("## ") {
                headings.push((offset, offset + line.len(), name.trim().to_string()));
            }
        }
        offset += line.len();
    }

    assert!(
        !headings.is_empty(),
        "{} must contain at least one H2 example section",
        TO_LEAN_EXAMPLES_MARKDOWN
    );

    let mut examples = Vec::new();
    let mut names = HashSet::new();
    for (index, (_heading_start, body_start, name)) in headings.iter().enumerate() {
        assert!(
            !name.is_empty()
                && name.chars().all(|character| character.is_ascii_lowercase()
                    || character.is_ascii_digit()
                    || character == '_'),
            "invalid To-Lean Markdown example name: {}",
            name
        );
        assert!(
            names.insert(name.clone()),
            "duplicate To-Lean Markdown example name: {}",
            name
        );

        let section_end = headings
            .get(index + 1)
            .map(|(next_heading_start, _, _)| *next_heading_start)
            .unwrap_or(markdown.len());
        let litex_ranges = fenced_body_ranges(markdown, *body_start, section_end, "litex");
        let lean_ranges = fenced_body_ranges(markdown, *body_start, section_end, "lean");
        assert_eq!(
            litex_ranges.len(),
            1,
            "{} must contain exactly one litex fenced block",
            name
        );
        assert_eq!(
            lean_ranges.len(),
            1,
            "{} must contain exactly one lean fenced block",
            name
        );
        let litex_range = litex_ranges[0].clone();
        let lean_range = lean_ranges[0].clone();
        assert!(
            litex_range.start < lean_range.start,
            "{} must put its litex fence before its lean fence",
            name
        );

        let marker_count = markdown[*body_start..litex_range.start]
            .lines()
            .filter(|line| line.trim() == PARTIAL_EXAMPLE_MARKER)
            .count();
        assert!(
            marker_count <= 1,
            "{} contains duplicate partial markers",
            name
        );
        let mode = if marker_count == 1 {
            ToLeanExampleMode::Partial
        } else {
            ToLeanExampleMode::Strict
        };

        let litex_source = markdown[litex_range].trim_end().to_string();
        let lean_snapshot = markdown[lean_range.clone()].trim_end().to_string();
        examples.push(ToLeanMarkdownExample {
            name: name.clone(),
            mode,
            litex_source,
            lean_snapshot,
            lean_body_range: lean_range,
        });
    }

    examples
}

fn fenced_body_ranges(
    markdown: &str,
    section_start: usize,
    section_end: usize,
    target_language: &str,
) -> Vec<Range<usize>> {
    let mut ranges = Vec::new();
    let mut open_fence: Option<(String, usize)> = None;
    let mut offset = section_start;

    for line in markdown[section_start..section_end].split_inclusive('\n') {
        let line_start = offset;
        offset += line.len();
        let trimmed = line.trim_end_matches('\n').trim_end_matches('\r').trim();

        match open_fence.as_ref() {
            Some((language, body_start)) => {
                if trimmed == "```" {
                    if language == target_language {
                        ranges.push(*body_start..line_start);
                    }
                    open_fence = None;
                }
            }
            None => {
                if let Some(language) = trimmed.strip_prefix("```") {
                    open_fence = Some((language.trim().to_string(), offset));
                }
            }
        }
    }

    ranges
}

fn markdown_with_refreshed_lean_snapshots(
    markdown: &str,
    examples: &[ToLeanMarkdownExample],
    generated_snapshots: &[String],
) -> String {
    assert_eq!(examples.len(), generated_snapshots.len());
    let mut refreshed = String::with_capacity(markdown.len());
    let mut cursor = 0;

    for (example, generated) in examples.iter().zip(generated_snapshots.iter()) {
        assert!(cursor <= example.lean_body_range.start);
        refreshed.push_str(&markdown[cursor..example.lean_body_range.start]);
        refreshed.push_str(generated.trim_end());
        refreshed.push('\n');
        cursor = example.lean_body_range.end;
    }
    refreshed.push_str(&markdown[cursor..]);
    refreshed
}

fn compile_generated_with_mathlib(
    name: &str,
    generated: &str,
    project: &str,
    lake: &str,
) -> Result<(), String> {
    let lean_file = generated_lean_path(name);
    fs::write(&lean_file, generated).unwrap();
    let output = Command::new(lake)
        .args(["env", "lean"])
        .arg(&lean_file)
        .current_dir(project)
        .output();
    let _ = fs::remove_file(&lean_file);
    let output = output.unwrap();
    if !output.status.success() {
        return Err(format!(
            "generated Lean failed for {}\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
            name,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
            generated
        ));
    }
    println!("Mathlib kernel Markdown example OK: {}", name);
    Ok(())
}

fn generated_lean_path(name: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let stem = name.replace('_', "-");
    let private = Path::new(env!("CARGO_MANIFEST_DIR")).join("private");
    fs::create_dir_all(&private).unwrap();
    private.join(format!(
        "litex-to-lean-example-{}-{}-{}.lean",
        stem,
        std::process::id(),
        nonce
    ))
}

fn run_with_large_stack(test_name: &str, action: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(action)
        .unwrap()
        .join()
        .unwrap();
}
