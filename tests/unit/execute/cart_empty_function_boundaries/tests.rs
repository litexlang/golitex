//! Cartesian members and empty graphs use complete function domains.
use crate::execute::ExecStmtResult;
use crate::json_output::{emit_run_detailed, project_stmt_detailed};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn execute(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1, "{code}");
    rt.exec_stmt(&statements.remove(0)).unwrap()
}

fn facts(rt: &Runtime) -> usize {
    rt.execution_environments_stack
        .iter()
        .map(|env| env.facts.facts_by_id.len())
        .sum()
}

#[test]
fn cart_empty_function_boundaries_preserve_zero_one_and_many_members() {
    for code in [
        "cart()={()}\ncart()={{}}\n()={}",
        "finite_seq({},0)={()}\nfinite_seq(R,0)={{}}\nfn(k {}) R={()}",
        "have fn empty_fn(k {}) R=0\nempty_fn={}\nlet alias=empty_fn\nalias={}",
        "fn(x R,y {}) R {0}={}\nfn(k {}) R {0}={}",
        "tuple(7) $in cart(Z)\nhave p cart(Z)=tuple(7)\np(1)=7\np(1) $in Z\np $in finite_seq(R,1)",
        "() $in cart()\nrelease thm cart_member_from_coordinates((),cart())",
        "release thm cart_member_from_coordinates(tuple(7),cart(Z))",
        "have empty_member cart()\nfn_range(empty_member)={}\nempty_member={}",
        "cart({})={}\n$is_finite_set(cart())\n$is_nonempty_set(cart())\nfinite_set_size(cart())=1",
        "finite_set_size(cart({1,2}))=finite_set_size({1,2})",
        "have fn f(k closed_range(1,2)) Z=0\nf $in cart(R,Z)\nf(2) $in Z",
        "have Carrier set=cart(Z)\nhave p Carrier=tuple(7)\nlet alias=p\nalias=tuple(7)\nalias(1)=7",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}\n{}", emit_run_detailed(&run, &rt, "cart-empty-boundaries", None));
        assert!(!run.statement_results.is_empty());
        assert!(run.statement_results.iter().all(|statement| !statement.is_failed()));
    }
}

#[test]
fn cart_empty_function_boundaries_reject_wrong_domains_and_false_empty_graphs() {
    for (setup, target) in [
        ("1=1", "cart()={}"),
        ("1=1", "tuple(7) $in cart()"),
        ("1=1", "() $in cart(Z)"),
        ("1=1", "(7,8) $in cart(Z)"),
        ("1=1", "tuple(1/2) $in cart(Z)"),
        ("have p cart(Z)=tuple(7)", "p(2)=7"),
        ("have empty_member cart()", "empty_member(1)=0"),
        ("1=1", "fn(k N+) R {0}={}"),
        ("1=1", "fn(k R) R {0}={}"),
        ("have outer fn(x R) fn(k {}) R", "outer={}"),
        ("1=1", "fn(k R) R={()}"),
        ("1=1", "cart(Z)={()}"),
        (
            "1=1",
            "release thm cart_member_from_coordinates(tuple(7),cart())",
        ),
        ("cart({},R)={}\ncart({},R,Z)={}", "2=3"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(setup).unwrap().success, "{setup}");
        let before = facts(&rt);
        assert!(
            execute(&mut rt, target).is_failed(),
            "accepted false target: {setup}\n{target}"
        );
        assert_eq!(facts(&rt), before, "failed target published: {target}");
        assert!(!execute(&mut rt, "1=1").is_failed());
    }
}

#[test]
fn cart_empty_function_boundaries_project_real_domain_sources_in_all_languages() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        for (code, label, source) in [
            ("()={}", "EmptyFunctionGraph", "empty_integer_range_carrier"),
            (
                "cart()={()}",
                "EmptyDomainFunctionSpaceSingleton",
                "empty_integer_range_carrier",
            ),
            (
                "tuple(7) $in cart(Z)",
                "CartMembership",
                "domain_alpha_equivalent",
            ),
        ] {
            let result = execute(&mut rt, code);
            assert!(!result.is_failed(), "{language:?}: {code}");
            let detailed = project_stmt_detailed(&result, &rt).stringify();
            assert!(detailed.contains(label), "{language:?}: {detailed}");
            assert!(
                detailed.contains(source),
                "missing domain proof: {detailed}"
            );
            assert!(
                !detailed.contains("shape_and_dimension_checked"),
                "old opaque proof: {detailed}"
            );
        }
    }
}
