use super::compile_to_lean_from_source;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const LEDGER: &str = "examples/09_compile_to_lean/compile_to_lean_examples.md";
const SHOWCASE: &str = "examples/_internal/compile_to_lean/showcase.lit";

#[test]
fn universal_examples_compile_to_the_new_abi() {
    run_with_large_stack(|| {
        let examples = ledger_examples();
        assert_eq!(
            examples.len(),
            7,
            "the universal-object ledger changed shape"
        );
        for (label, source) in examples {
            let generated = compile_to_lean_from_source(&source, &format!("{label}.lit"))
                .unwrap_or_else(|error| panic!("ledger example {label} failed: {error:?}"));
            assert_new_abi(&label, &generated);
        }
    });
}

#[test]
fn universal_showcase_compiles_to_the_new_abi() {
    run_with_large_stack(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(SHOWCASE);
        let source = fs::read_to_string(path).expect("read universal-object showcase");
        let generated = compile_to_lean_from_source(&source, SHOWCASE)
            .expect("the combined universal-object showcase should compile");
        for label in [
            "set_parameter",
            "derived_set_predicates",
            "membership_wd",
            "known_forall",
            "builtin_theorem",
            "exact_application_layers",
            "arithmetic_forall_wd",
        ] {
            assert_new_abi(label, &generated);
        }
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
fn universal_showcase_compiles_with_mathlib() {
    run_with_large_stack(|| {
        let project = std::env::var("LITEX_LEAN_PROJECT")
            .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
        let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(SHOWCASE);
        let source = fs::read_to_string(path).expect("read universal-object showcase");
        let generated = compile_to_lean_from_source(&source, SHOWCASE)
            .expect("the combined universal-object showcase should compile");
        compile_generated("showcase", &generated, &project, &lake);
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
fn universal_examples_compile_with_mathlib() {
    run_with_large_stack(|| {
        let project = std::env::var("LITEX_LEAN_PROJECT")
            .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
        let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
        for (label, source) in ledger_examples() {
            let generated = compile_to_lean_from_source(&source, &format!("{label}.lit"))
                .unwrap_or_else(|error| panic!("ledger example {label} failed: {error:?}"));
            assert_new_abi(&label, &generated);
            compile_generated(&label, &generated, &project, &lake);
        }
    });
}

fn assert_new_abi(label: &str, generated: &str) {
    assert!(
        generated.contains("axiom LitexObject : Type"),
        "{label}\n{generated}"
    );
    assert!(
        generated.contains("axiom In : LitexObject → LitexObject → Prop"),
        "{label}\n{generated}"
    );
    assert!(
        generated.contains("def IsNonemptySet (s : LitexObject) : Prop :=")
            && generated.contains("IsSet s ∧ ∃ x : LitexObject, In x s"),
        "{label}\n{generated}"
    );
    assert!(
        generated.contains("def IsFiniteSet (s : LitexObject) : Prop :=")
            && generated.contains("IsSet s ∧ Set.Finite {x : LitexObject | In x s}"),
        "{label}\n{generated}"
    );
    assert!(!generated.contains("axiom IsNonemptySet"), "{generated}");
    assert!(!generated.contains("axiom IsFiniteSet"), "{generated}");
    for forbidden in [
        "class LitexObject",
        "Set ℝ",
        "Set ℂ",
        "downcast",
        "widening",
        "LeanCarrier",
    ] {
        assert!(
            !generated.contains(forbidden),
            "ledger example {label} retained forbidden old ABI fragment `{forbidden}`\n{generated}"
        );
    }
    let source_declarations = generated
        .rsplit_once("end Litex\n")
        .expect("generated prelude should close the Litex namespace")
        .1;
    for forbidden in ["(a : ℝ)", "(a : ℂ)", "(b : ℝ)", "(b : ℂ)"] {
        assert!(
            !source_declarations.contains(forbidden),
            "ledger example {label} retyped a source binder as `{forbidden}`\n{generated}"
        );
    }
    match label {
        "membership_wd" => {
            assert!(
                generated.contains("theorem well_defined_fact_3"),
                "{generated}"
            );
            assert!(
                generated.contains("f [a] (Litex.fnSetApplicable"),
                "{generated}"
            );
        }
        "set_parameter" => {
            assert!(generated.contains("(a : LitexObject)"), "{generated}");
            assert!(generated.contains("Litex.In a Litex.R"), "{generated}");
            assert!(generated.contains("(b : LitexObject)"), "{generated}");
            assert!(generated.contains("Litex.IsSet b"), "{generated}");
        }
        "derived_set_predicates" => {
            assert!(generated.contains("(s : LitexObject)"), "{generated}");
            assert!(generated.contains("Litex.IsNonemptySet s"), "{generated}");
            assert!(generated.contains("(t : LitexObject)"), "{generated}");
            assert!(generated.contains("Litex.IsFiniteSet t"), "{generated}");
        }
        "known_forall" => {
            assert!(
                generated.contains("axiom marked : LitexObject → Prop"),
                "{generated}"
            );
            assert!(!generated.contains("assumption"), "{generated}");
        }
        "builtin_theorem" => {
            assert!(
                generated.contains("theorem notEqualSymmetry"),
                "{generated}"
            );
            assert!(
                generated.contains("Litex.BuiltinRules.notEqualSymmetry"),
                "{generated}"
            );
            assert!(!generated.contains("axiom notEqualSymmetry"), "{generated}");
        }
        "exact_application_layers" => {
            assert!(generated.contains("f [1, 2, 3]"), "{generated}");
            assert!(generated.contains("g [1]"), "{generated}");
            assert!(generated.contains(") [2]"), "{generated}");
            assert!(generated.contains("Litex.fnSetResult"), "{generated}");
        }
        "arithmetic_forall_wd" => {
            assert!(generated.contains("Litex.sub"), "{generated}");
            assert!(
                generated.contains("Litex.BuiltinRules.realSubClosure"),
                "{generated}"
            );
            assert!(
                generated.contains("litex_nested_param_fact_"),
                "{generated}"
            );
            let helper_names = generated
                .lines()
                .filter_map(|line| {
                    line.strip_prefix("theorem well_defined_fact_")
                        .and_then(|rest| rest.split_whitespace().next())
                })
                .collect::<Vec<_>>();
            let unique_helper_names = helper_names
                .iter()
                .copied()
                .collect::<std::collections::HashSet<_>>();
            assert!(!helper_names.is_empty(), "{generated}");
            assert_eq!(
                helper_names.len(),
                unique_helper_names.len(),
                "one WellDefinedFactId must emit one helper declaration\n{generated}"
            );
        }
        other => panic!("unregistered universal-object ledger example `{other}`"),
    }
}

fn ledger_examples() -> Vec<(String, String)> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(LEDGER);
    let markdown = fs::read_to_string(&path).expect("read universal-object compiler ledger");
    let mut heading = None;
    let mut in_litex = false;
    let mut current = String::new();
    let mut examples = Vec::new();
    for line in markdown.lines() {
        if let Some(value) = line.strip_prefix("## ") {
            heading = Some(value.trim().to_string());
            continue;
        }
        if line.trim() == "```litex" {
            assert!(!in_litex, "nested Litex fence in compiler ledger");
            in_litex = true;
            current.clear();
            continue;
        }
        if in_litex && line.trim() == "```" {
            let label = heading
                .clone()
                .expect("every Litex ledger fence must follow a level-two heading");
            examples.push((label, current.clone()));
            in_litex = false;
            continue;
        }
        if in_litex {
            current.push_str(line);
            current.push('\n');
        }
    }
    assert!(!in_litex, "unterminated Litex fence in compiler ledger");
    examples
}

fn compile_generated(label: &str, generated: &str, project: &str, lake: &str) {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after Unix epoch")
        .as_nanos();
    let path: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("private")
        .join(format!(
            "litex-universal-ledger-{label}-{}-{nonce}.lean",
            std::process::id()
        ));
    fs::create_dir_all(path.parent().expect("generated file should have a parent"))
        .expect("create workspace-local private directory");
    fs::write(&path, generated).expect("write generated Lean ledger entry");
    let result = Command::new(lake)
        .args(["env", "lean"])
        .arg(&path)
        .current_dir(project)
        .output();
    fs::remove_file(&path).expect("remove workspace-local generated Lean file");
    let result = result.expect("run Lean through configured Lake project");
    assert!(
        result.status.success(),
        "universal ledger example {label} failed Lean\nstdout:\n{}\nstderr:\n{}\nsource:\n{generated}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}

fn run_with_large_stack(action: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("universal_examples_test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(action)
        .expect("spawn universal examples test thread")
        .join()
        .expect("universal examples test thread panicked");
}
