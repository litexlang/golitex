use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn known_exist_reuses_nested_binders_after_wd_without_changing_the_function_body() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/proof_nodes/exist/by_known/nested_binder_alpha.lit"
        ))
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let run = rt
        .run_litex_code("exist z R st {$fixed(fn(b R) R {b + 1}, z)}")
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    let detailed =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(
        detailed.contains("search_proof"),
        "changed body is well-defined but cannot reuse the known fact: {detailed}"
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn known_exist_structural_match_keeps_carriers_kinds_and_free_owners_exact() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("prop fixed(g fn(a R) R, x R):\n    g(x) = x\nhave left, right R\n")
            .unwrap()
            .success
    );
    for (left, right) in [
        (
            "exist x R st {$fixed(fn(a R) R {a}, x)}",
            "exist y N st {$fixed(fn(b R) R {b}, y)}",
        ),
        (
            "exist x R st {$fixed(fn(a R) R {a + left}, x)}",
            "exist y R st {$fixed(fn(b R) R {b + right}, y)}",
        ),
        (
            "exist S set st {$is_set(S)}",
            "exist T nonempty_set st {$is_set(T)}",
        ),
    ] {
        let code = format!("{left}\n{right}\n");
        let tokens = Tokenizer::new()
            .tokenize(&code, rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::ExistFact(left)) = &statements[0] else {
            panic!("left existential")
        };
        let Stmt::Fact(Fact::ExistFact(right)) = &statements[1] else {
            panic!("right existential")
        };
        assert!(!plain_exist_facts_alpha_equal(left, right), "{code}");
    }
}
