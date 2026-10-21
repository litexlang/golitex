use crate::prelude::*;

#[test]
fn retired_function_arrow_rejects_in_each_object_context() {
    for source in [
        "let Retired = R -> R",
        "let Retired=N->N->Z",
        "let Retired = R × R -> R",
        "let Retired = (R -> R)",
        "let Retired = fn(f R -> R) R",
        "let Retired = fn(x R) (R -> R)",
        "let Retired = {f R -> R: f = f}",
        "have retired R -> R",
        "forall f R -> R:\n    f $in R -> R",
        "fn(x R) R $in R -> R",
        "R -> R = R -> R",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(!run.success && run.input_error.is_some(), "{source}");
        assert!(run.statement_results.is_empty(), "{source}");
        assert!(
            format!("{:?}", run.input_error)
                .contains("function-set arrow `->` is removed; use `fn(x A) B`"),
            "{source}: {:?}",
            run.input_error
        );
    }
    // Compact R- set aliases absorb the hyphen; this spelling must still reject.
    let run = runtime().run_litex_code("let Retired=R->R->Z").unwrap();
    assert!(!run.success && run.input_error.is_some());
}

#[test]
fn explicit_function_sets_functions_and_logical_implication_remain_available() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(
            "# R -> R is only a comment.\n\
         let Unary = fn(x R) R\n\
         let Curried = fn(x R) fn(y R) R\n\
         Curried = fn(a R) fn(b R) R\n\
         let PairMap = fn(p R × R) R\n\
         PairMap = fn(q cart(R, R)) R\n\
         have fn id(x R) R = x\n\
         let shifted = fn(x R) R {x + 1}\n\
         id(2) = 2\n\
         shifted(2) = 3\n\
         -1 < 0\n\
         forall f fn(x R) R:\n    f $in fn(y R) R\n\
         forall x R:\n    x = 0\n    =>:\n        x + 1 = 1",
        )
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let run = rt.run_litex_code("fn(x R) N = fn(y R) R").unwrap();
    assert!(!run.success && run.session_error.is_none());
}

#[test]
fn retired_function_arrow_does_not_leave_an_attempted_binding() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have fn id(x R) R = x").unwrap().success);
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let run = rt.run_litex_code("let Retired = R -> R").unwrap();
    assert!(!run.success && run.input_error.is_some());
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    let run = rt
        .run_litex_code("let Retired = fn(x R) R\nid(2) = 2")
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
