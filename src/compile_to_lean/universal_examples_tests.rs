use super::compile_to_lean_from_source;
use super::lean_test_support::SharedLeanTestLibrary;
use std::fs;
use std::path::Path;

const LEDGER: &str = "examples/09_compile_to_lean/compile_to_lean_examples.md";
const SHOWCASE: &str = "examples/_internal/compile_to_lean/showcase.lit";
const SHARED_BUILTIN_TRACER: &str =
    "examples/05_compiler_interop/compile_to_lean_shared_builtin_rules.lit";

#[test]
fn universal_examples_compile_to_the_new_abi() {
    run_with_large_stack(|| {
        let examples = ledger_examples();
        let snapshots = ledger_generated_snapshots();
        assert_eq!(
            examples.len(),
            15,
            "the append-only feature ledger changed shape"
        );
        assert_eq!(
            snapshots.len(),
            examples.len(),
            "every Litex ledger program must have one actual generated Lean snapshot"
        );
        for ((label, source), (snapshot_label, snapshot)) in
            examples.into_iter().zip(snapshots)
        {
            assert_eq!(snapshot_label, label, "ledger snapshot order drifted");
            let generated = compile_to_lean_from_source(&source, &format!("{label}.lit"))
                .unwrap_or_else(|error| panic!("ledger example {label} failed: {error:?}"));
            assert_eq!(
                snapshot, generated,
                "ledger example {label} has a stale or hand-written generated Lean snapshot"
            );
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
            "statement_definitions_and_trust",
            "builtin_theorem",
            "known_equality_path",
            "exact_application_layers",
            "arithmetic_forall_wd",
            "proof_carrying_arithmetic",
            "proof_carrying_list_set",
        ] {
            assert_new_abi(label, &generated);
        }
    });
}

#[test]
fn shared_builtin_rule_tracer_imports_theorems() {
    run_with_large_stack(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(SHARED_BUILTIN_TRACER);
        let source = fs::read_to_string(path).expect("read shared builtin-rule tracer");
        let generated = compile_to_lean_from_source(&source, SHARED_BUILTIN_TRACER)
            .expect("the shared builtin-rule tracer should compile");
        assert_new_shared_library_header("shared_builtin_rules", &generated);
        for theorem in ["notEqualSymmetry", "numeralInN", "numeralInC"] {
            assert!(
                generated.contains(&format!("Litex.BuiltinRules.{theorem}")),
                "{generated}"
            );
            assert!(
                !generated.contains(&format!("theorem {theorem}")),
                "{generated}"
            );
        }
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
fn universal_showcase_compiles_with_mathlib() {
    run_with_large_stack(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(SHOWCASE);
        let source = fs::read_to_string(path).expect("read universal-object showcase");
        let generated = compile_to_lean_from_source(&source, SHOWCASE)
            .expect("the combined universal-object showcase should compile");
        let mut library = SharedLeanTestLibrary::new("showcase");
        library.compile_generated("showcase", &generated);
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
fn universal_examples_compile_with_mathlib() {
    run_with_large_stack(|| {
        let mut library = SharedLeanTestLibrary::new("ledger");
        for (label, source) in ledger_examples() {
            let generated = compile_to_lean_from_source(&source, &format!("{label}.lit"))
                .unwrap_or_else(|error| panic!("ledger example {label} failed: {error:?}"));
            assert_new_abi(&label, &generated);
            library.compile_generated(&label, &generated);
        }
    });
}

#[test]
#[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
fn shared_builtin_rule_tracer_compiles_with_mathlib() {
    run_with_large_stack(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(SHARED_BUILTIN_TRACER);
        let source = fs::read_to_string(path).expect("read shared builtin-rule tracer");
        let generated = compile_to_lean_from_source(&source, SHARED_BUILTIN_TRACER)
            .expect("the shared builtin-rule tracer should compile");
        let mut library = SharedLeanTestLibrary::new("shared-builtin-tracer");
        library.compile_generated("shared-builtin-tracer", &generated);
        library.reject_generated(
            "wrong-abi-version",
            "import Litex.BuiltinRules\n\nexample : Litex.abiVersion = 1 := rfl\n",
        );
    });
}

fn assert_new_abi(label: &str, generated: &str) {
    assert_new_shared_library_header(label, generated);
    for forbidden in [
        "LitexObject",
        "import Mathlib",
        "axiom Object : Type",
        "axiom In : Object",
        "theorem notEqualSymmetry",
        "theorem numeralInN",
        "theorem numeralInC",
        "theorem realSubClosure",
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
        .strip_prefix("import Litex.BuiltinRules\n\nexample : Litex.abiVersion = 7 := rfl\n")
        .expect("generated source should begin after the shared-library header");
    for forbidden in ["(a : ℝ)", "(a : ℂ)", "(b : ℝ)", "(b : ℂ)"] {
        assert!(
            !source_declarations.contains(forbidden),
            "ledger example {label} retyped a source binder as `{forbidden}`\n{generated}"
        );
    }
    match label {
        "well_defined_object_dag" => {
            assert!(
                generated.matches("noncomputable def obj_").count() >= 3,
                "{generated}"
            );
            assert!(
                generated.contains("_applicable : ∀") && generated.contains("Litex.Applicable"),
                "{generated}"
            );
            assert!(!generated.contains("well_defined_object_"), "{generated}");
        }
        "trusted_forall_atomic_fact" => {
            assert!(
                generated.contains("axiom p : Litex.Object → Prop"),
                "{generated}"
            );
            assert_eq!(generated.matches("axiom fact").count(), 1, "{generated}");
            assert!(generated.contains(": p 1 := by"), "{generated}");
            assert!(
                generated.contains(" 1 (Litex.BuiltinRules.numeralInR 1)"),
                "{generated}"
            );
            assert!(!generated.contains("assumption"), "{generated}");
        }
        "membership_wd" => {
            assert!(
                generated.contains("theorem well_defined_fact_3"),
                "{generated}"
            );
            assert!(
                generated.contains("noncomputable def obj_") && generated.contains("_applicable"),
                "{generated}"
            );
        }
        "set_parameter" => {
            assert!(generated.contains("(a : Litex.Object)"), "{generated}");
            assert!(generated.contains("Litex.In a Litex.R"), "{generated}");
            assert!(generated.contains("(b : Litex.Object)"), "{generated}");
            assert!(generated.contains("Litex.IsSet b"), "{generated}");
        }
        "derived_set_predicates" => {
            assert!(generated.contains("(s : Litex.Object)"), "{generated}");
            assert!(generated.contains("Litex.IsNonemptySet s"), "{generated}");
            assert!(generated.contains("(t : Litex.Object)"), "{generated}");
            assert!(generated.contains("Litex.IsFiniteSet t"), "{generated}");
        }
        "known_forall" => {
            assert!(
                generated.contains("axiom marked : Litex.Object → Prop"),
                "{generated}"
            );
            assert!(!generated.contains("assumption"), "{generated}");
        }
        "statement_definitions_and_trust" => {
            assert!(
                generated.contains("axiom highlighted : Litex.Object → Prop"),
                "{generated}"
            );
            assert!(
                generated.contains("def is_zero (x : Litex.Object) : Prop :=")
                    && generated.contains("Litex.In x Litex.R ∧ (x = 0)"),
                "{generated}"
            );
            assert!(
                generated.contains("noncomputable def named_zero : Litex.Object := 0"),
                "{generated}"
            );
            assert!(
                generated.contains("change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0)"),
                "{generated}"
            );
            assert!(
                generated.contains("change Litex.In named_zero Litex.R ∧ (named_zero = 0)"),
                "{generated}"
            );
        }
        "builtin_theorem" => {
            assert!(
                generated.contains("Litex.BuiltinRules.notEqualSymmetry"),
                "{generated}"
            );
            assert!(!generated.contains("axiom notEqualSymmetry"), "{generated}");
        }
        "known_equality_path" => {
            assert!(generated.contains("Eq.symm"), "{generated}");
            assert!(generated.contains("Eq.trans"), "{generated}");
            assert!(
                !generated.contains("same known equality class"),
                "{generated}"
            );
        }
        "exact_application_layers" => {
            assert!(generated.contains("f [obj_"), "{generated}");
            assert!(generated.contains("g [obj_"), "{generated}");
            assert!(generated.contains(") [obj_"), "{generated}");
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
        "proof_carrying_arithmetic" => {
            for theorem in [
                "complexAddClosure",
                "complexSubClosure",
                "complexMulClosure",
                "complexDivClosure",
            ] {
                assert!(
                    generated.contains(&format!("Litex.BuiltinRules.{theorem}")),
                    "{generated}"
                );
            }
            assert!(
                generated.contains("theorem well_defined_fact_"),
                "{generated}"
            );
            assert!(generated.contains("Litex.add (obj_"), "{generated}");
            assert!(generated.contains("Litex.div (obj_"), "{generated}");
        }
        "inferred_forall_premise" => {
            assert!(
                generated.contains("have litex_inferred_fact_1 : Litex.Lt 0 x :="),
                "{generated}"
            );
            assert!(
                generated.contains("Litex.BuiltinRules.positiveRealMembership litex_param_fact_1"),
                "{generated}"
            );
            assert!(
                generated.contains("exact litex_inferred_fact_1"),
                "{generated}"
            );
            assert!(!generated.contains("assumption"), "{generated}");
        }
        "proof_carrying_list_set" => {
            assert!(generated.contains("Litex.listSet [(obj_"), "{generated}");
            assert!(generated.contains("List.Pairwise.cons"), "{generated}");
            assert!(
                generated.contains("exact (well_defined_fact_"),
                "{generated}"
            );
            assert!(!generated.contains("sorry"), "{generated}");
        }
        "object_choice" => {
            assert!(generated.contains("Classical.choose"), "{generated}");
            assert!(generated.contains("Classical.choose_spec"), "{generated}");
        }
        "existential_intro_elim" => {
            assert!(generated.contains("∃ (x : Litex.Object)"), "{generated}");
            assert!(generated.contains("Classical.choose_spec"), "{generated}");
        }
        "case_and_contradiction_scopes" => {
            assert!(generated.contains("have litex_case_1"), "{generated}");
            assert!(
                generated.contains("by_contra litex_reverse_assumption"),
                "{generated}"
            );
        }
        "named_theorem" => {
            assert!(generated.contains("theorem one_eq_one :"), "{generated}");
            assert!(!generated.contains("axiom one_eq_one"), "{generated}");
        }
        "total_object_constructors" => {
            assert!(generated.contains("Litex.pi"), "{generated}");
            assert!(generated.contains("Litex.union"), "{generated}");
        }
        "proof_carrying_division" => {
            assert!(generated.contains("Litex.div (obj_"), "{generated}");
            assert!(
                generated.contains("Litex.BuiltinRules.realDivClosure"),
                "{generated}"
            );
        }
        "set_builder_scope" => {
            assert!(generated.contains("Litex.setBuilder"), "{generated}");
            assert!(generated.contains("fun litex_set_builder_"), "{generated}");
        }
        "named_function" => {
            assert!(generated.contains("Litex.functionObject"), "{generated}");
            assert!(
                generated.contains("Litex.functionObject_apply"),
                "{generated}"
            );
        }
        "indexed_aggregate" => {
            assert!(generated.contains("Litex.tupleObject"), "{generated}");
            assert!(generated.contains("Litex.tupleObject_at"), "{generated}");
        }
        "statement_object_interactions" => {
            assert!(generated.contains("noncomputable def y"), "{generated}");
            assert!(
                generated.contains("theorem one_eq_one_by_cases"),
                "{generated}"
            );
            assert!(
                generated.contains("Litex.inSetBuilder_iff.mpr"),
                "{generated}"
            );
        }
        other => panic!("unregistered universal-object ledger example `{other}`"),
    }
}

fn assert_new_shared_library_header(label: &str, generated: &str) {
    assert!(
        generated
            .starts_with("import Litex.BuiltinRules\n\nexample : Litex.abiVersion = 7 := rfl\n"),
        "{label}\n{generated}"
    );
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

fn ledger_generated_snapshots() -> Vec<(String, String)> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(LEDGER);
    let markdown = fs::read_to_string(&path).expect("read universal-object compiler ledger");
    let mut heading = None;
    let mut active_label = None;
    let mut in_lean = false;
    let mut current = String::new();
    let mut snapshots = Vec::new();
    for line in markdown.lines() {
        if let Some(value) = line.strip_prefix("## ") {
            heading = Some(value.trim().to_string());
            continue;
        }
        if let Some(value) = line
            .strip_prefix("<!-- BEGIN ACTUAL GENERATED LEAN: ")
            .and_then(|value| value.strip_suffix(" -->"))
        {
            assert!(active_label.is_none(), "nested generated Lean snapshot");
            let label = value.to_string();
            assert_eq!(heading.as_deref(), Some(label.as_str()));
            active_label = Some(label);
            current.clear();
            continue;
        }
        if active_label.is_some() && line.trim() == "```lean" {
            assert!(!in_lean, "nested generated Lean fence");
            in_lean = true;
            continue;
        }
        if in_lean && line.trim() == "```" {
            in_lean = false;
            continue;
        }
        if let Some(value) = line
            .strip_prefix("<!-- END ACTUAL GENERATED LEAN: ")
            .and_then(|value| value.strip_suffix(" -->"))
        {
            assert!(!in_lean, "unterminated generated Lean fence");
            let label = active_label.take().expect("generated Lean end marker");
            assert_eq!(value, label);
            snapshots.push((label, current.clone()));
            continue;
        }
        if in_lean {
            current.push_str(line);
            current.push('\n');
        }
    }
    assert!(active_label.is_none(), "unterminated generated Lean snapshot");
    assert!(!in_lean, "unterminated generated Lean fence");
    snapshots
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
