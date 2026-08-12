use super::*;

fn run_setting_source(source_code: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (results, error) = run_source_code(source_code, &mut runtime);
    render_run_source_code_output(&runtime, &results, &error, false)
}

#[test]
fn setting_expands_parameters_conditions_and_extra_parameters() {
    let source = r#"
setting EqualPair:
    X nonempty_set
    x, y X
    x = y

forall [EqualPair]:
    x = y

forall [EqualPair], z X:
    z = z
"#;
    let (succeeded, output) = run_setting_source(source, "setting_expansion");
    assert!(succeeded, "setting fixture failed:\n{}", output);
    assert!(output.contains("\"type\": \"setting definition\""));
    assert!(output.contains("forall X nonempty_set, x, y X:\\n    x = y\\n    =>:"));
    assert!(output.contains("forall X nonempty_set, x, y X, z X:"));
}

#[test]
fn setting_expands_in_inline_forall_positions() {
    let source = r#"
setting EqualPair:
    X nonempty_set
    x, y X
    x = y

forall [EqualPair] => {x = y}

trust not forall [EqualPair] => {x != y}
"#;
    let (succeeded, output) = run_setting_source(source, "setting_inline_expansion");
    assert!(succeeded, "inline setting fixture failed:\n{}", output);
    assert!(output.contains("forall X nonempty_set, x, y X:"));
    assert!(output.contains("not forall X nonempty_set, x, y X:"));
}

#[test]
fn existential_and_set_builder_bodies_reject_forall() {
    let cases = [
        (
            "exist_inline_forall",
            "trust exist x R st {forall y R => {y = y}}",
        ),
        (
            "set_builder_inline_forall",
            "trust {x R: forall y R => {y = y}} = {x R: x = x}",
        ),
        (
            "exist_block_forall",
            "have x R:\n    forall y R:\n        y = y",
        ),
    ];

    for (label, source) in cases {
        let (succeeded, output) = run_setting_source(source, label);
        assert!(!succeeded, "{label} unexpectedly succeeded:\n{output}");
        assert!(
            output.contains("inline `forall` is not allowed in existential or set-builder bodies"),
            "{label} produced the wrong diagnostic:\n{output}"
        );
    }
}

#[test]
fn repeated_setting_uses_allocate_distinct_forall_bindings() {
    let source = r#"
setting OneElement:
    X nonempty_set
    x X

forall [OneElement]:
    x = x

forall [OneElement]:
    x = x
"#;
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, std::rc::Rc::from("setting_freshness"))
        .expect("tokenize setting fixture");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("setting_freshness");

    let setting_stmt = runtime.parse_stmt(&mut blocks[0]).expect("parse setting");
    runtime.exec_stmt(&setting_stmt).expect("store setting");
    let first = runtime.parse_stmt(&mut blocks[1]).expect("parse first use");
    runtime.exec_stmt(&first).expect("execute first use");
    let second = runtime
        .parse_stmt(&mut blocks[2])
        .expect("parse second use");

    let Stmt::Fact(Fact::ForallFact(first)) = first else {
        panic!("expected first forall");
    };
    let Stmt::Fact(Fact::ForallFact(second)) = second else {
        panic!("expected second forall");
    };
    let first_bindings = first.params_def_with_type.collect_param_bindings();
    let second_bindings = second.params_def_with_type.collect_param_bindings();
    assert_eq!(first_bindings.len(), second_bindings.len());
    for (left, right) in first_bindings.iter().zip(second_bindings.iter()) {
        assert_eq!(left.name(), right.name());
        assert_ne!(left.id(), right.id(), "setting use reused binder identity");
    }
}

#[test]
fn setting_expansion_replays_parameterized_default_struct_views() {
    let source = r#"
struct Box<s set>:
    value s
    tag N

setting BoxSetting:
    s nonempty_set
    box &Box<s>

forall [BoxSetting]:
    box.value = &Box<s>{box}.value

forall [BoxSetting]:
    box.value = &Box<s>{box}.value
"#;
    let (succeeded, output) = run_setting_source(source, "setting_default_struct_view");
    assert!(
        succeeded,
        "setting expansion should replay each fresh binder's instantiated default struct view:\n{}",
        output
    );
}

#[test]
fn setting_expansion_does_not_invent_default_struct_views() {
    let source = r#"
struct Point:
    x R
    y R

setting UntypedPoint:
    point set

forall [UntypedPoint]:
    point.x = point.x
"#;
    let (succeeded, output) = run_setting_source(source, "setting_without_default_struct_view");
    assert!(
        !succeeded,
        "an untyped setting parameter must not acquire a default struct view:\n{}",
        output
    );
    assert!(output.contains("default struct view"));
}

#[test]
fn setting_reports_unknown_collision_order_and_duplicate_errors() {
    let cases = [
        ("forall [Missing]:\n    1 = 1", "unknown setting `Missing`"),
        ("forall [Missing] => {1 = 1}", "unknown setting `Missing`"),
        (
            "setting S:\n    X nonempty_set\nforall [S], x X => {x = x}",
            "must be followed by `=>`",
        ),
        (
            "setting S:\n    X nonempty_set\nforall [S], X nonempty_set:\n    1 = 1",
            "already active",
        ),
        (
            "setting S:\n    X nonempty_set\n    X = X\n    x X",
            "parameter lines must come before",
        ),
        (
            "setting S:\n    X nonempty_set\nsetting S:\n    Y nonempty_set",
            "already used",
        ),
        ("setting Empty:", "missing body"),
    ];

    for (index, (source, expected)) in cases.iter().enumerate() {
        let (succeeded, output) =
            run_setting_source(source, &format!("setting_negative_{}", index));
        assert!(!succeeded, "negative fixture unexpectedly passed: {source}");
        assert!(
            output.contains(expected),
            "expected {expected:?} for {source:?}, got:\n{output}"
        );
    }
}
