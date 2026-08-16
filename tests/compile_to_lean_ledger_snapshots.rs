use litex::compile_to_lean::compile_to_lean_from_source;
use std::fs;
use std::path::Path;

const LEDGER: &str = "lean/examples/compile_to_lean_examples.md";

#[test]
fn actual_generated_lean_snapshots_match_current_compiler() {
    run_with_large_stack(|| {
        let (examples, snapshots) = ledger_examples_and_snapshots();
        assert_eq!(examples.len(), 25, "the feature ledger changed shape");
        assert_eq!(
            snapshots.len(),
            examples.len(),
            "every Litex program must have one actual generated Lean snapshot"
        );
        for ((label, source), (snapshot_label, snapshot)) in examples.into_iter().zip(snapshots) {
            assert_eq!(snapshot_label, label, "ledger snapshot order drifted");
            let case_path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("lean/examples/cases")
                .join(format!("compile_to_lean_{label}.lit"));
            let case_source = fs::read_to_string(&case_path)
                .unwrap_or_else(|error| panic!("read {}: {error}", case_path.display()));
            let active_source = case_source
                .lines()
                .filter(|line| !line.trim_start().starts_with('#'))
                .collect::<Vec<_>>()
                .join("\n");
            let active_source = format!("{}\n", active_source.trim());
            assert_eq!(
                source,
                active_source,
                "ledger Litex source drifted from {}",
                case_path.display()
            );
            let generated = compile_to_lean_from_source(&source, &format!("{label}.lit"))
                .unwrap_or_else(|error| panic!("ledger example {label} failed: {error:?}"));
            assert_eq!(
                snapshot, generated,
                "ledger example {label} has a stale or hand-written generated Lean snapshot"
            );
        }
    });
}

#[test]
#[ignore = "rewrites the ledger from canonical case files and fresh compiler output"]
fn update_actual_generated_lean_snapshots() {
    run_with_large_stack(|| {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let ledger_path = root.join(LEDGER);
        let original = fs::read_to_string(&ledger_path).expect("read compiler ledger");
        let (examples, _) = ledger_examples_and_snapshots();
        let mut updated = original;

        for (label, _) in examples {
            let case_path = root
                .join("lean/examples/cases")
                .join(format!("compile_to_lean_{label}.lit"));
            let case_source = fs::read_to_string(&case_path)
                .unwrap_or_else(|error| panic!("read {}: {error}", case_path.display()));
            let source = case_source
                .lines()
                .filter(|line| !line.trim_start().starts_with('#'))
                .collect::<Vec<_>>()
                .join("\n");
            let source = format!("{}\n", source.trim());
            let generated = compile_to_lean_from_source(&source, &format!("{label}.lit"))
                .unwrap_or_else(|error| panic!("ledger example {label} failed: {error:?}"));

            let heading = format!("## {label}\n");
            let section_start = updated
                .find(&heading)
                .unwrap_or_else(|| panic!("missing ledger heading {label}"));
            let section_end = updated[section_start + heading.len()..]
                .find("\n## ")
                .map(|offset| section_start + heading.len() + offset)
                .unwrap_or(updated.len());
            let section = &updated[section_start..section_end];
            let litex_open = section
                .find("```litex\n")
                .map(|offset| section_start + offset + "```litex\n".len())
                .unwrap_or_else(|| panic!("missing Litex fence for {label}"));
            let litex_close = updated[litex_open..]
                .find("\n```")
                .map(|offset| litex_open + offset)
                .unwrap_or_else(|| panic!("unterminated Litex fence for {label}"));
            updated.replace_range(litex_open..litex_close, source.trim_end());

            let begin = format!("<!-- BEGIN ACTUAL GENERATED LEAN: {label} -->\n```lean\n");
            let end = format!("```\n<!-- END ACTUAL GENERATED LEAN: {label} -->");
            let generated_start = updated
                .find(&begin)
                .map(|offset| offset + begin.len())
                .unwrap_or_else(|| panic!("missing generated Lean begin marker for {label}"));
            let generated_end = updated[generated_start..]
                .find(&end)
                .map(|offset| generated_start + offset)
                .unwrap_or_else(|| panic!("missing generated Lean end marker for {label}"));
            updated.replace_range(generated_start..generated_end, generated.trim_end());
            updated.insert(generated_start + generated.trim_end().len(), '\n');
        }

        fs::write(&ledger_path, updated).expect("rewrite compiler ledger snapshots");
    });
}

fn ledger_examples_and_snapshots() -> (Vec<(String, String)>, Vec<(String, String)>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(LEDGER);
    let markdown = fs::read_to_string(path).expect("read compiler ledger");
    let mut heading = None;
    let mut in_litex = false;
    let mut litex_source = String::new();
    let mut active_snapshot = None;
    let mut in_generated_lean = false;
    let mut generated_lean = String::new();
    let mut examples = Vec::new();
    let mut snapshots = Vec::new();

    for line in markdown.lines() {
        if let Some(value) = line.strip_prefix("## ") {
            heading = Some(value.trim().to_string());
            continue;
        }
        if line.trim() == "```litex" {
            assert!(!in_litex, "nested Litex fence");
            in_litex = true;
            litex_source.clear();
            continue;
        }
        if in_litex && line.trim() == "```" {
            let label = heading.clone().expect("Litex fence heading");
            examples.push((label, litex_source.clone()));
            in_litex = false;
            continue;
        }
        if in_litex {
            litex_source.push_str(line);
            litex_source.push('\n');
            continue;
        }
        if let Some(value) = line
            .strip_prefix("<!-- BEGIN ACTUAL GENERATED LEAN: ")
            .and_then(|value| value.strip_suffix(" -->"))
        {
            assert!(active_snapshot.is_none(), "nested generated Lean snapshot");
            assert_eq!(heading.as_deref(), Some(value));
            active_snapshot = Some(value.to_string());
            generated_lean.clear();
            continue;
        }
        if active_snapshot.is_some() && line.trim() == "```lean" {
            assert!(!in_generated_lean, "nested generated Lean fence");
            in_generated_lean = true;
            continue;
        }
        if in_generated_lean && line.trim() == "```" {
            in_generated_lean = false;
            continue;
        }
        if let Some(value) = line
            .strip_prefix("<!-- END ACTUAL GENERATED LEAN: ")
            .and_then(|value| value.strip_suffix(" -->"))
        {
            assert!(!in_generated_lean, "unterminated generated Lean fence");
            let label = active_snapshot.take().expect("generated Lean end marker");
            assert_eq!(value, label);
            snapshots.push((label, generated_lean.clone()));
            continue;
        }
        if in_generated_lean {
            generated_lean.push_str(line);
            generated_lean.push('\n');
        }
    }

    assert!(!in_litex, "unterminated Litex fence");
    assert!(
        active_snapshot.is_none(),
        "unterminated generated Lean snapshot"
    );
    assert!(!in_generated_lean, "unterminated generated Lean fence");
    (examples, snapshots)
}

fn run_with_large_stack(action: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("compile_to_lean_ledger_snapshots".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(action)
        .expect("spawn compiler ledger snapshot test")
        .join()
        .expect("compiler ledger snapshot test panicked");
}
