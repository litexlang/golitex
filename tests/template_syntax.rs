use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn run_examples_template_syntax() {
    let run = runtime()
        .run_litex_code(include_str!(
            "../examples/stmt_nodes/definition/template_syntax.lit"
        ))
        .unwrap();
    assert!(run.success, "{:?}", run.normal_json);
    assert!(run.input_error.is_none());
    assert!(run.session_error.is_none());
}

#[test]
fn bracketed_forms_fail_at_parse_and_leave_the_runtime_usable() {
    let mut rt = runtime();
    let setup = rt
        .run_litex_code(
            "template<a R>:\n    have A set = R\n\
             template<S set>:\n    have fn identity(x S) S = x\n\
             have p cart(R, R) = (1, 2)",
        )
        .unwrap();
    assert!(setup.success, "{:?}", setup.normal_json);

    for (source, diagnostic) in [
        (
            "template[S set]:\n    have broken set = S",
            "expected `<`, got `[`",
        ),
        ("have x A[0] = 2", "object indexing with [] is removed"),
        ("identity[R](2) = 2", "object indexing with [] is removed"),
        ("p[1] = 1", "object indexing with [] is removed"),
        ("p[1][2] = 1", "object indexing with [] is removed"),
    ] {
        let fact_count = rt.top_exec_env().facts.facts_by_id.len();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(
            format!("{:?}", run.input_error).contains(diagnostic),
            "{source}: {:?}",
            run.normal_json
        );
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), fact_count);
        for name in ["S", "broken", "x"] {
            assert!(!rt.plain_atom_is_visible(name), "{source} leaked {name}");
        }
    }
    let run = rt
        .run_litex_code("have x \\A<0> = 2\nx = 2\n\\identity<R>(2) = 2\np(1) = 1")
        .unwrap();
    assert!(run.success, "{:?}", run.normal_json);
}

#[test]
fn angle_bracket_templates_keep_argument_and_guard_checks() {
    let mut rt = runtime();
    let setup = rt
        .run_litex_code(
            "template<S set>:\n    have fn identity(x S) S = x\n\
             template<a R: a != 0,>:\n    have inverse R = 1 / a",
        )
        .unwrap();
    assert!(setup.success, "{:?}", setup.normal_json);

    for source in [
        r"\identity<N>(-1) = -1",
        r"\identity<R, N>(2) = 2",
        r"\identity<>(2) = 2",
        r"\inverse<0> = 0",
        r"\ghost<R> = R",
        r"\identity<R>(2) = 3",
    ] {
        let fact_count = rt.top_exec_env().facts.facts_by_id.len();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.input_error.is_none(), "{source}");
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), fact_count);
        assert!(rt.run_litex_code(r"\identity<R>(2) = 2").unwrap().success);
    }
}

#[test]
fn malformed_angle_brackets_do_not_leak_bindings() {
    let mut rt = runtime();
    for source in [
        "template<S set]:\n    have broken set = S",
        "template<>:\n    have broken set = R",
        "template<S set>:",
        r"let broken = \f<R",
        r"let broken = \f<R](2)",
    ] {
        let run = rt.run_litex_code(source).unwrap();
        assert!(
            !run.success && run.input_error.is_some(),
            "{source}: {:?}",
            run.normal_json
        );
        for name in ["S", "broken"] {
            assert!(!rt.plain_atom_is_visible(name), "{source} leaked {name}");
        }
    }
    assert!(rt.run_litex_code("have broken R = 2").unwrap().success);
    assert!(rt.run_litex_code("broken + 1 = 3").unwrap().success);
}
