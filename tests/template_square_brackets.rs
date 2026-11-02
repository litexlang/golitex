use litex::ast::obj::Obj;
use litex::ast::stmt::{CommandStmt, Stmt};
use litex::launch_command::{LaunchCommand, OutputLanguage};
use litex::runtime::Runtime;
use litex::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parsed_object(source: &str) -> Obj {
    let mut rt = runtime();
    let blocks = Tokenizer::new()
        .tokenize(&format!("eval {source}"), rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&blocks).unwrap();
    let Stmt::Command(CommandStmt::EvalStmt(statement)) = statements.remove(0) else {
        panic!("expected eval object: {source}");
    };
    statement.obj_to_eval
}

#[test]
fn template_square_brackets_reuse_the_existing_instance_and_application_ast() {
    for (square, angle) in [
        ("f[R]", r"\f<R>"),
        ("f[R](2)", r"\f<R>(2)"),
        ("f[copy[R]](2)", r"\f<\copy<R>>(2)"),
        ("f['[0, 1)](0)", r"\f<'[0, 1)>(0)"),
        ("f[R](2)(3)", r"\f<R>(2)(3)"),
        ("f[R](2).field", r"\f<R>(2).field"),
    ] {
        assert_eq!(
            parsed_object(square),
            parsed_object(angle),
            "{square} must retain the same semantic identity as {angle}"
        );
    }
}

#[test]
fn run_examples_template_square_brackets() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../examples/stmt_nodes/definition/template_square_brackets.lit"
        ))
        .unwrap();
    assert!(run.success, "{:?}", run.normal_json);
    assert!(run.input_error.is_none());
    assert!(run.session_error.is_none());
}

#[test]
fn template_square_brackets_keep_argument_guard_and_indexing_boundaries() {
    let mut rt = runtime();
    let setup = rt
        .run_litex_code(
            "template[S set]:\n    have fn identity(x S) S = x\n\
             template[a R: a != 0]:\n    have inverse R = 1 / a\n\
             have p cart(R, R) = (1, 2)",
        )
        .unwrap();
    assert!(setup.success, "{:?}", setup.normal_json);

    for source in [
        "identity[N](-1) = -1",
        "identity[R, N](2) = 2",
        "identity[](2) = 2",
        "inverse[0] = 0",
        "ghost[R] = R",
        "p[1] = 1",
        "p[1][2] = 1",
        "identity[R](2) = 3",
    ] {
        let fact_count = rt.top_exec_env().facts.facts_by_id.len();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), fact_count);
        assert!(rt.run_litex_code("identity[R](2) = 2").unwrap().success);
        assert!(rt.run_litex_code("p(1) = 1").unwrap().success);
    }
}

#[test]
fn template_square_brackets_reject_malformed_delimiters_without_leaking_names() {
    let mut rt = runtime();
    for source in [
        "template[S set>:\n    have broken set = S",
        "template<S set]:\n    have broken set = S",
        "template[]:\n    have broken set = R",
        "template[S set]:",
        "let broken = f[R",
        "let broken = f[R>](2)",
        "let broken = f[R,](2)",
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
