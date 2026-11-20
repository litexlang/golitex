use crate::prelude::*;

#[test]
fn backtick_infix_calls_lower_to_ordinary_function_applications() {
    for (infix, prefix) in [
        ("1 `f` 2", "f(1, 2)"),
        ("1 `G.mul` 2", "G.mul(1, 2)"),
        ("1 + 2 `f` 3 * 4", "f(1 + 2, 3 * 4)"),
        ("{1} ∪ {2} `f` {3} ∩ {4}", "f({1} ∪ {2}, {3} ∩ {4})"),
        ("(1 `f` 2) + 3", "f(1, 2) + 3"),
        ("(1 `f` 2) `f` 3", "f(f(1, 2), 3)"),
        ("1 `f` (2 `f` 3)", "f(1, f(2, 3))"),
        ("(1 `f` g) `t` 3", "t(f(1, g), 3)"),
        ("1 `f` (g `t` 3)", "f(1, t(g, 3))"),
    ] {
        let actual = parsed_expression(infix).expect(infix);
        let expected = parsed_expression(prefix).expect(prefix);
        assert_eq!(actual, expected, "different objects for {infix}");
    }
}

#[test]
fn backtick_infix_calls_reject_unparenthesized_chains() {
    for source in [
        "1 `f` 2 `f` 3",
        "1 `f` 2 `f` 3 `f`",
        "1 `f` g `t` 3",
        "(1 `f` 2) `f` 3 `f` 4",
        "1 `f` (2 `f` 3 `f` 4)",
    ] {
        let error = parsed_expression(source).expect_err(source).to_string();
        assert!(
            error.contains("use parentheses to group"),
            "{source}: {error}"
        );
    }
}

#[test]
fn backtick_infix_calls_reject_malformed_applications() {
    for source in [
        "1 `f 2",
        "1 `f`",
        "`f` 2",
        "1 `` 2",
        "1 `2` 3",
        "1 `f(2, 3)` 4",
    ] {
        assert!(parsed_expression(source).is_err(), "accepted {source}");
    }
}

fn parsed_expression(expression: &str) -> RuntimeResult<Obj> {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let source = format!("have f, g, t fn(x, y R) R\nhave G R\neval {expression}");
    let blocks = crate::tokenize::Tokenizer::new().tokenize(&source, rt.current_file.clone())?;
    let mut stmts = rt.parse(&blocks)?;
    let Some(Stmt::Command(crate::ast::stmt::CommandStmt::EvalStmt(eval))) = stmts.pop() else {
        panic!("expected eval statement");
    };
    Ok(eval.obj_to_eval)
}
