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
setting EqualPair(X nonempty_set, x, y X):
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
setting EqualPair(X nonempty_set, x, y X):
    x = y

forall [EqualPair] => x = y

trust not forall [EqualPair] => x != y
"#;
    let (succeeded, output) = run_setting_source(source, "setting_inline_expansion");
    assert!(succeeded, "inline setting fixture failed:\n{}", output);
    assert!(output.contains("forall X nonempty_set, x, y X:"));
    assert!(output.contains("not forall X nonempty_set, x, y X:"));
}

#[test]
fn setting_explicit_names_declare_fresh_binders_and_instantiate_dependencies() {
    let source = r#"
setting GroupSetting(A nonempty_set, mul fn(x, y A) A, one A, inv fn(x A) A):
    forall u A:
        mul(one, u) = u
        mul(inv(u), u) = one

forall [GroupSetting(existing_set, some_function_expression, identity_element, inverse_function)]:
    some_function_expression(identity_element, identity_element) = identity_element

forall [GroupSetting(B, mul_B, one_B, inv_B)] => mul_B(inv_B(one_B), one_B) = one_B
"#;
    let (succeeded, output) = run_setting_source(source, "setting_explicit_names");
    assert!(succeeded, "explicit setting binders failed:\n{}", output);
    assert!(output.contains(
        "forall existing_set nonempty_set, some_function_expression fn (x, y existing_set) existing_set, identity_element existing_set, inverse_function fn (x existing_set) existing_set:"
    ));
    assert!(
        output.contains("forall B nonempty_set, mul_B fn (x, y B) B, one_B B, inv_B fn (x B) B:")
    );
}

#[test]
fn prop_header_setting_bundles_expand_parameters_and_conditions_in_order() {
    let source = r#"
setting GroupSetting(A nonempty_set, mul fn(x, y A) A, one A, inv fn(x A) A):
    forall u, v, w A:
        mul(mul(u, v), w) = mul(u, mul(v, w))
    forall u A:
        mul(one, u) = u
        mul(inv(u), u) = one

prop is_group_homomorphism([GroupSetting(A, mul_A, one_A, inv_A)], [GroupSetting(B, mul_B, one_B, inv_B)], f fn(x A) B):
    forall x, y A:
        f(mul_A(x, y)) = mul_B(f(x), f(y))
"#;
    let (succeeded, output) = run_setting_source(source, "setting_prop_header");
    assert!(succeeded, "prop setting bundles failed:\n{}", output);
    assert!(output.contains(
        "prop is_group_homomorphism(A nonempty_set, mul_A fn (x, y A) A, one_A A, inv_A fn (x A) A, B nonempty_set, mul_B fn (x, y B) B, one_B B, inv_B fn (x B) B, f fn (x A) B):"
    ));
    let a_condition = output
        .find("mul_A(mul_A(u, v), w)")
        .expect("first setting conditions should be expanded");
    let b_condition = output
        .find("mul_B(mul_B(u, v), w)")
        .expect("second setting conditions should be expanded");
    let explicit_body = output
        .find("f(mul_A(x, y)) = mul_B(f(x), f(y))")
        .expect("explicit prop body should remain present");
    assert!(a_condition < b_condition && b_condition < explicit_body);
}

#[test]
fn bare_setting_bundle_is_supported_in_prop_headers() {
    let source = r#"
setting Pointed(X nonempty_set, point X):
    point = point

prop is_pointed([Pointed])
"#;
    let (succeeded, output) = run_setting_source(source, "setting_prop_bare");
    assert!(succeeded, "bare prop setting bundle failed:\n{}", output);
    assert!(output.contains("prop is_pointed(X nonempty_set, point X):"));
    assert!(output.contains("point = point"));
}

#[test]
fn setting_headers_compose_setting_bundles() {
    let source = r#"
setting EqualPair(X nonempty_set, x, y X):
    x = y

setting EqualPairWithWitness([EqualPair(S, left, right)], witness S):
    witness = left

forall [EqualPairWithWitness]:
    left = right
    witness = left
"#;
    let (succeeded, output) = run_setting_source(source, "setting_header_bundle");
    assert!(succeeded, "nested setting bundle failed:\n{}", output);
    assert!(
        output.contains("setting EqualPairWithWitness(S nonempty_set, left, right S, witness S):")
    );
    let nested_setting = output
        .find("setting EqualPairWithWitness(")
        .expect("nested setting should be displayed");
    let nested_output = &output[nested_setting..];
    let inherited = nested_output
        .find("left = right")
        .expect("inherited setting condition should be expanded");
    let explicit = nested_output
        .find("witness = left")
        .expect("explicit setting condition should remain present");
    assert!(inherited < explicit);
}

#[test]
fn struct_headers_turn_setting_conditions_into_membership_conditions() {
    let source = r#"
setting EqualPair(X nonempty_set, x, y X):
    x = y

struct EqualPairWitness<[EqualPair(S, left, right)]>:
    witness S
    <=>:
        witness = left

forall S nonempty_set, left, right S, item &EqualPairWitness<S, left, right>:
    left = right
"#;
    let (succeeded, output) = run_setting_source(source, "struct_header_bundle");
    assert!(
        succeeded,
        "struct setting bundle membership inference failed:\n{}",
        output
    );

    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, std::rc::Rc::from("struct_header_bundle_shape"))
        .expect("tokenize struct setting bundle fixture");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("struct_header_bundle_shape");
    let setting_stmt = runtime.parse_stmt(&mut blocks[0]).expect("parse setting");
    runtime.exec_stmt(&setting_stmt).expect("store setting");
    let struct_stmt = runtime.parse_stmt(&mut blocks[1]).expect("parse struct");
    let Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(struct_def)) = struct_stmt else {
        panic!("expected struct definition");
    };
    let (params, header_dom) = struct_def
        .param_def_with_dom
        .as_ref()
        .expect("setting bundle should produce struct header parameters");
    assert_eq!(params.collect_param_names(), ["S", "left", "right"]);
    assert!(
        header_dom.is_empty(),
        "setting laws are not header-domain facts"
    );
    assert_eq!(
        struct_def.fields.len(),
        1,
        "bundle parameters are not fields"
    );
    assert_eq!(struct_def.fields[0].name(), "witness");
    assert_eq!(struct_def.equivalent_facts.len(), 2);
    assert_eq!(struct_def.equivalent_facts[0].to_string(), "left = right");
    assert_eq!(struct_def.equivalent_facts[1].to_string(), "witness = left");
}

#[test]
fn renamed_setting_parameters_do_not_capture_nested_forall_binders() {
    let source = r#"
setting ReflexiveCarrier(X set):
    forall u X:
        u = u

forall [ReflexiveCarrier(u)]:
    u = u
"#;
    let (succeeded, output) = run_setting_source(source, "setting_capture_avoidance");
    assert!(
        succeeded,
        "setting substitution captured a nested binder:\n{}",
        output
    );
}

#[test]
fn existential_and_set_builder_bodies_reject_forall() {
    let cases = [
        (
            "exist_inline_forall",
            "trust exist x R st {forall y R => y = y}",
        ),
        (
            "set_builder_inline_forall",
            "trust {x R: forall y R => y = y} = {x R: x = x}",
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
setting OneElement(X nonempty_set, x X)

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
fn repeated_explicit_setting_uses_allocate_distinct_forall_bindings() {
    let source = r#"
setting OneElement(X nonempty_set, x X)

forall [OneElement(Y, y)]:
    y = y

forall [OneElement(Y, y)]:
    y = y
"#;
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, std::rc::Rc::from("setting_explicit_freshness"))
        .expect("tokenize setting fixture");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("setting_explicit_freshness");

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
    for (left, right) in first
        .params_def_with_type
        .collect_param_bindings()
        .iter()
        .zip(second.params_def_with_type.collect_param_bindings().iter())
    {
        assert_eq!(left.name(), right.name());
        assert_ne!(
            left.id(),
            right.id(),
            "explicit setting use reused identity"
        );
    }
}

#[test]
fn setting_expansion_replays_parameterized_default_struct_views() {
    let source = r#"
struct Box<s set>:
    value s
    tag N

setting BoxSetting(s nonempty_set, box &Box<s>)

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

setting UntypedPoint(point set)

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
        ("forall [Missing] => 1 = 1", "unknown setting `Missing`"),
        (
            "setting S(X nonempty_set)\nforall [S], x X => x = x",
            "must be followed by `=>`",
        ),
        (
            "setting S(X nonempty_set)\nforall [S], X nonempty_set:\n    1 = 1",
            "already active",
        ),
        (
            "setting S(X nonempty_set, x X)\nforall [S(Y)]:\n    1 = 1",
            "setting `S` expects 2 binder name(s), got 1",
        ),
        (
            "setting S(X nonempty_set, x X)\nforall [S()]:\n    1 = 1",
            "setting `S` expects 2 binder name(s), got 0",
        ),
        (
            "setting S(X nonempty_set, f fn(x X) X)\nforall [S(Y, compose(g, h))]:\n    1 = 1",
            "arguments must be bare binder names",
        ),
        (
            "setting S(X nonempty_set, x X)\nforall Outer nonempty_set:\n    forall [S(Outer, inner)]:\n        inner = inner",
            "already active",
        ),
        (
            "setting S(X nonempty_set, x X)\nprop duplicate([S(A, x)], [S(A, y)])",
            "already active",
        ),
        (
            "setting S(X nonempty_set, x X)\nsetting Nested([S(A, x)], [S(A, y)])",
            "already active",
        ),
        (
            "setting S(X nonempty_set, x X)\nstruct Wrapped<[S(A, compose(g, h))]>:\n    value A",
            "arguments must be bare binder names",
        ),
        (
            "setting S(X nonempty_set, x X)\nhave existing_set nonempty_set\nforall [S(existing_set, fresh_x)]:\n    fresh_x = fresh_x",
            "already active",
        ),
        ("forall []:\n    1 = 1", "bundle cannot be empty"),
        (
            "setting S(X nonempty_set):\n    X = X\n    x X",
            "Expected operator or $prop in fact",
        ),
        (
            "setting S(X nonempty_set)\nsetting S(Y nonempty_set)",
            "already used",
        ),
        ("setting Empty()", "at least one parameter"),
        (
            "setting Legacy:\n    X nonempty_set",
            "setting header expects `setting Name(...)`",
        ),
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
