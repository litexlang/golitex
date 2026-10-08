//! Retired syntax and payloads cannot bypass current exact-function contracts.
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

#[test]
fn retired_product_surface_rejects_before_execution_and_keeps_existing_binding_scope() {
    for (source, diagnostic) in [
        ("tuple_dim(p)=2", "tuple_dim is removed"),
        ("proj(cart(R,Z),1)=R", "proj is removed"),
        ("p[1]=1", "object indexing with [] is removed"),
        ("p[1][2]=1", "object indexing with [] is removed"),
        ("$is_tuple(p)", "is_tuple` is removed"),
        ("not $is_tuple(p)", "is_tuple` is removed"),
        ("not not $is_tuple(p)", "is_tuple` is removed"),
        ("$is_cart(cart(R,Z))", "is_cart` is removed"),
        ("not $is_cart(cart(R,Z))", "is_cart` is removed"),
        ("cart_dim(cart(R,Z))=2", "cart_dim is removed"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(rt.run_litex_code("have p cart(R,Z)=(1,2)").unwrap().success);
        let before = rt.top_exec_env().facts.facts_by_id.len();
        let run = rt.run_litex_code(source).unwrap();
        assert!(
            !run.success && run.session_error.is_some(),
            "old surface accepted: {source}"
        );
        assert!(
            format!("{:?}", run.session_error).contains(diagnostic),
            "wrong diagnostic: {source}"
        );
        assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
        assert!(rt.run_litex_code("p(1)=1\np(2) $in Z").unwrap().success);
        assert!(!rt.run_litex_code("2=3").unwrap().success);
    }
    let mut rt = runtime(OutputLanguage::English);
    assert!(
        !rt.run_litex_code("let picked=tuple_dim((1,2))")
            .unwrap()
            .success
    );
    assert!(
        rt.run_litex_code("have picked R=1\npicked=1")
            .unwrap()
            .success,
        "retired RHS left its attempted binding in parse scope"
    );
}

#[test]
fn new_coordinate_calls_reconstruction_intervals_and_generic_indexed_families_remain_available() {
    let mut rt = runtime(OutputLanguage::English);
    let run=rt.run_litex_code("have p cart(R,Z)\np=(p(1),p(2))\np(1) $in R\np(2) $in Z\n2 $in closed_range(1,2)\n0 $in '[0,1]\ncart()={()}\nlet family=fn(k {1}) power_set(R) {{0}}\nindex_cart({1},power_set(R),family)=index_cart({1},power_set(R),family)\n").unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    for false_goal in ["p(3)=0", "p=(p(2),p(1))", "p=(p(1),p(1),p(2))"] {
        assert!(
            !rt.run_litex_code(false_goal).unwrap().success,
            "{false_goal}"
        );
    }
}

// Retired payloads can no longer be constructed: the approved AST deletion
// is enforced by exhaustive Rust matches. Test old source re-entry against a
// populated current environment rather than manufacturing removed variants.
#[test]
fn retired_spellings_cannot_reenter_a_populated_current_environment() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        assert!(
            rt.run_litex_code("have p cart(R,Z)=(1,2)\np(1)=1")
                .unwrap()
                .success
        );
        for source in [
            "tuple_dim(p)=2",
            "cart_dim(cart(R,Z))=2",
            "proj(cart(R,Z),1)=R",
            "p[1]=1",
            "$is_tuple(p)",
            "$is_cart(cart(R,Z))",
        ] {
            let before = rt.top_exec_env().facts.facts_by_id.len();
            let result = rt.run_litex_code(source).unwrap();
            assert!(
                !result.success && result.session_error.is_some(),
                "{source}"
            );
            assert!(result.statement_results.is_empty());
            assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
            assert!(rt.run_litex_code("p(2)=2").unwrap().success);
        }
    }
}
