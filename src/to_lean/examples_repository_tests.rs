use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use super::{
    to_lean_from_source, to_lean_from_source_with_report, ToLeanCompilationStatus,
    ToLeanUnsupportedPhase,
};

const TO_LEAN_EXAMPLE_REPOSITORY: &str = "examples/09_to_lean";
const STRICT_EXAMPLE_FILES: &[&str] = &[
    "native_carriers.lit",
    "bounded_facts.lit",
    "propositions_and_trust.lit",
    "object_definitions.lit",
    "equality_transport.lit",
    "builtin_arithmetic.lit",
    "recursive_arithmetic.lit",
    "native_sets.lit",
    "choice.lit",
    "existentials.lit",
    "proof_scopes.lit",
];
const PARTIAL_EXAMPLE_FILES: &[&str] = &["carrier_boundaries.lit", "partial_boundary.lit"];

#[test]
fn to_lean_examples_repository_emits_checked_source() {
    run_with_large_stack("to_lean_examples_repository_emits_checked_source", || {
        let repository = example_repository_path();
        let config = fs::read_to_string(repository.join("litex.config")).unwrap();
        let mut strict_failures = Vec::new();

        for file in STRICT_EXAMPLE_FILES {
            assert!(
                config.contains(&format!("\"./{}\"", file)),
                "{} is missing from litex.config",
                file
            );
            let path = repository.join(file);
            let source = fs::read_to_string(&path).unwrap();
            let entry_label = example_entry_label(file);
            let generated = match to_lean_from_source(&source, &entry_label) {
                Ok(generated) => generated,
                Err(error) => {
                    let report = to_lean_from_source_with_report(&source, &entry_label).unwrap();
                    strict_failures.push(format!(
                        "strict To-Lean failed for {}: {}\nunsupported: {:#?}",
                        file,
                        error.trace_message(),
                        report.unsupported
                    ));
                    continue;
                }
            };

            assert!(generated.starts_with("import Mathlib\n"), "{}", file);
            assert!(!generated.contains("sorry"), "{}", file);
            assert!(!generated.contains("LitexSet"), "{}", file);
            assert!(!generated.contains("LitexAddEq"), "{}", file);
            if *file == "propositions_and_trust.lit" {
                assert_eq!(generated.matches("\naxiom global_fact_").count(), 4);
                assert!(
                    generated.contains("∀ x ∈ (Set.univ : Set ℝ), x ∈ (Set.univ : Set ℝ)"),
                    "{}",
                    generated
                );
                assert!(
                    generated
                        .contains("∀ z ∈ (Set.univ : Set ℤ), (z / 2 : ℚ) ∈ (Set.univ : Set ℚ)"),
                    "{}",
                    generated
                );
            } else {
                assert!(!generated.contains("\naxiom global_fact_"), "{}", file);
            }

            if *file == "native_carriers.lit" {
                assert!(generated.contains("2 = 2"), "{}", generated);
                assert!(
                    generated.contains("2 ∈ (Set.univ : Set ℝ)"),
                    "{}",
                    generated
                );
            }

            assert_generated_snapshot_matches(file, &source, &generated);

            println!(
                "To-Lean strict example OK: {} ({} Lean bytes)",
                file,
                generated.len()
            );
        }

        assert!(
            strict_failures.is_empty(),
            "{}",
            strict_failures.join("\n\n")
        );

        for file in PARTIAL_EXAMPLE_FILES {
            assert!(
                config.contains(&format!("\"./{}\"", file)),
                "{} is missing from litex.config",
                file
            );
            let partial_path = repository.join(file);
            let partial_source = fs::read_to_string(&partial_path).unwrap();
            let report =
                to_lean_from_source_with_report(&partial_source, &example_entry_label(file))
                    .unwrap();

            assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
            assert!(!report.unsupported.is_empty(), "{}", file);
            assert!(!report.lean_code.contains("sorry"), "{}", file);
            assert!(
                !report.lean_code.contains("\naxiom global_fact_"),
                "{}",
                file
            );

            if *file == "carrier_boundaries.lit" {
                assert_eq!(report.unsupported.len(), 11);
                assert!(report.unsupported[0].statement.contains("n + 1"));
                assert!(report.unsupported[10]
                    .statement
                    .contains("boundary_complex_one"));
            } else if *file == "partial_boundary.lit" {
                assert_eq!(report.unsupported.len(), 1);
                assert_eq!(report.unsupported[0].statement_index, 2);
                assert_eq!(
                    report.unsupported[0].phase,
                    ToLeanUnsupportedPhase::LeanEmission
                );
                assert!(report.unsupported[0].statement.contains("sin"));
                assert_eq!(report.lean_code.matches("theorem global_fact_").count(), 2);
            }

            assert_generated_snapshot_matches(file, &partial_source, &report.lean_code);

            println!(
                "To-Lean partial example OK: {} ({} explicit omissions, {} Lean bytes)",
                file,
                report.unsupported.len(),
                report.lean_code.len()
            );
        }
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing at a Mathlib Lake project"]
fn generated_to_lean_examples_repository_compiles_with_mathlib() {
    run_with_large_stack(
        "generated_to_lean_examples_repository_compiles_with_mathlib",
        || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("LITEX_LEAN_PROJECT must point at a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let repository = example_repository_path();
            let mut failures = Vec::new();

            for file in STRICT_EXAMPLE_FILES {
                let path = repository.join(file);
                let source = fs::read_to_string(&path).unwrap();
                let generated = to_lean_from_source(&source, &example_entry_label(file)).unwrap();
                if let Err(failure) =
                    compile_generated_with_mathlib(file, &generated, &project, &lake)
                {
                    failures.push(failure);
                }
            }

            for file in PARTIAL_EXAMPLE_FILES {
                let partial_path = repository.join(file);
                let partial_source = fs::read_to_string(&partial_path).unwrap();
                let report =
                    to_lean_from_source_with_report(&partial_source, &example_entry_label(file))
                        .unwrap();
                assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                if let Err(failure) =
                    compile_generated_with_mathlib(file, &report.lean_code, &project, &lake)
                {
                    failures.push(failure);
                }
            }

            assert!(failures.is_empty(), "{}", failures.join("\n\n"));
        },
    );
}

#[test]
#[ignore = "rewrites every trailing generated-Lean snapshot under examples/09_to_lean"]
fn refresh_to_lean_examples_repository_snapshots() {
    run_with_large_stack("refresh_to_lean_examples_repository_snapshots", || {
        let repository = example_repository_path();

        for file in STRICT_EXAMPLE_FILES {
            let path = repository.join(file);
            let source = fs::read_to_string(&path).unwrap();
            let litex_source = source_without_trailing_triple_quoted_block(&source);
            let generated = to_lean_from_source(litex_source, &example_entry_label(file)).unwrap();
            fs::write(&path, source_with_generated_lean(litex_source, &generated)).unwrap();
            println!("Refreshed strict Lean snapshot: {}", file);
        }

        for file in PARTIAL_EXAMPLE_FILES {
            let path = repository.join(file);
            let source = fs::read_to_string(&path).unwrap();
            let litex_source = source_without_trailing_triple_quoted_block(&source);
            let report =
                to_lean_from_source_with_report(litex_source, &example_entry_label(file)).unwrap();
            assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
            fs::write(
                &path,
                source_with_generated_lean(litex_source, &report.lean_code),
            )
            .unwrap();
            println!("Refreshed partial Lean snapshot: {}", file);
        }
    });
}

fn example_repository_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(TO_LEAN_EXAMPLE_REPOSITORY)
}

fn example_entry_label(file: &str) -> String {
    format!("{}/{}", TO_LEAN_EXAMPLE_REPOSITORY, file)
}

fn assert_generated_snapshot_matches(file: &str, source: &str, generated: &str) {
    let snapshot = trailing_triple_quoted_block(source)
        .unwrap_or_else(|| panic!("{} must end with a triple-quoted Lean snapshot", file));
    assert_eq!(
        snapshot.trim_end(),
        generated.trim_end(),
        "generated Lean snapshot is stale for {}; run the refresh test",
        file
    );
}

fn source_with_generated_lean(source: &str, generated_lean: &str) -> String {
    format!(
        "{}\n\n\n\"\"\"\n{}\n\"\"\"\n",
        source.trim_end(),
        generated_lean.trim_end()
    )
}

fn trailing_triple_quoted_block(source: &str) -> Option<&str> {
    let trimmed_source = source.trim_end();
    let before_closing_delimiter = trimmed_source.strip_suffix("\"\"\"")?;
    let opening_marker = "\n\"\"\"\n";
    let opening_delimiter_start = before_closing_delimiter.rfind(opening_marker)?;
    Some(&before_closing_delimiter[opening_delimiter_start + opening_marker.len()..])
}

fn source_without_trailing_triple_quoted_block(source: &str) -> &str {
    let trimmed_source = source.trim_end();
    let Some(before_closing_delimiter) = trimmed_source.strip_suffix("\"\"\"") else {
        return source;
    };
    let opening_marker = "\n\"\"\"\n";
    let Some(opening_delimiter_start) = before_closing_delimiter.rfind(opening_marker) else {
        return source;
    };
    &source[..opening_delimiter_start]
}

fn compile_generated_with_mathlib(
    file: &str,
    generated: &str,
    project: &str,
    lake: &str,
) -> Result<(), String> {
    let lean_file = generated_lean_path(file);
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
            file,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
            generated
        ));
    }
    println!("Mathlib kernel example OK: {}", file);
    Ok(())
}

fn generated_lean_path(file: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let stem = file.trim_end_matches(".lit").replace('_', "-");
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
