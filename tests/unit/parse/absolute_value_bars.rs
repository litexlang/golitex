use crate::prelude::*;

#[test]
fn absolute_value_bars_lower_to_the_existing_abs_object() {
    for (bars, canonical) in [
        ("|-3|", "abs(-3)"),
        ("|1 - 4|", "abs(1 - 4)"),
        ("|-3| + |2|", "abs(-3) + abs(2)"),
        ("2 * |-3|", "2 * abs(-3)"),
        ("|1 + |-3||", "abs(1 + abs(-3))"),
        ("||-3||", "abs(abs(-3))"),
        ("-|-3|^2", "-abs(-3)^2"),
        ("|2|^|-3|", "abs(2)^abs(-3)"),
        ("|2|!", "abs(2)!"),
        ("min(|-3|, |4|)", "min(abs(-3), abs(4))"),
        ("{|1|, |2|}", "{abs(1), abs(2)}"),
        ("|-3|...|2|", "abs(-3)...abs(2)"),
        ("fn(x R) R {|x|}", "fn(x R) R {abs(x)}"),
        ("{|1|, |2|} ∪ {|3|}", "{abs(1), abs(2)} ∪ {abs(3)}"),
    ] {
        let actual = parsed_expression(bars).unwrap();
        let expected = parsed_expression(canonical).unwrap();
        assert_eq!(actual, expected, "different objects for {bars}");
        assert_eq!(actual.readable_string(), expected.readable_string());
    }
}

#[test]
fn absolute_value_bars_reject_malformed_delimiters_and_implicit_multiplication() {
    for source in [
        "|",
        "||",
        "|1",
        "1|",
        "|1||",
        "|1 + |",
        "|1, 2|",
        "|1 = 1|",
        "|(|1|)",
        "|1|2",
        "2|1|",
        "|1| |2|",
        "|1| garbage",
    ] {
        assert!(parsed_expression(source).is_err(), "accepted {source}");
    }
    let error = parsed_expression("|1").unwrap_err().to_string();
    assert!(error.contains("closing `|`"), "{error}");
}

#[test]
fn absolute_value_bars_reuse_abs_verification_and_keep_the_real_domain() {
    let mut rt = runtime();
    let tracer = include_str!("../../../examples/test_objs/absolute_value_bars.lit");
    let run = rt.run_litex_code(tracer).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success);

    for source in [
        "|-3| = -3",
        "|i| = 1",
        "|{1, 2}| = 2",
        "|1 / 0| = 0",
        "abs(i) = 1",
    ] {
        let rejected = rt.run_litex_code(source).unwrap();
        assert!(
            rejected.session_error.is_none(),
            "{source}: {:?}",
            rejected.session_error
        );
        assert!(!rejected.success, "accepted {source}");
        assert!(rt.run_litex_code("|-3| = 3").unwrap().success);
    }
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parsed_expression(expression: &str) -> RuntimeResult<Obj> {
    let mut rt = runtime();
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize(&format!("eval {expression}"), rt.current_file.clone())?;
    let mut stmts = rt.parse(&blocks)?;
    let Stmt::Command(crate::ast::stmt::CommandStmt::EvalStmt(eval)) = stmts.remove(0) else {
        panic!("expected eval statement");
    };
    Ok(eval.obj_to_eval)
}
