use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn compact_subcover_reuses_declared_interface_and_requires_both_hypotheses() {
    let mut rt = runtime();
    let original = include_str!("../../../../showcases/math_concepts_in_litex/9_topology/main.lit");
    let prefix = original
        .split("thm continuous_image_of_compact_is_compact:")
        .next()
        .unwrap();
    let setup = rt.run_litex_code(prefix).unwrap();
    assert!(
        setup.success && setup.session_error.is_none(),
        "topology declarations must pass"
    );

    // Reuse the declared restriction interface. Expanding it to an anonymous
    // function is a separate equality proof, not an existential lookup contract.
    let conclusion = r"exist J power_set(Index) st {$is_finite_set(J), K $subset family_union(fn_range(\restricted<Index,open_sets,cover,J>))}";
    for (hypotheses, expected) in [
        ("        $is_compact_subset(X, open_sets, K)\n        K $subset family_union(fn_range(cover))\n", true),
        ("        K $subset family_union(fn_range(cover))\n", false),
        ("        $is_compact_subset(X, open_sets, K)\n", false),
    ] {
        let code = format!(
            "claim:\n    ? forall X set, open_sets power_set(power_set(X)), K power_set(X), Index set, cover fn(index Index) open_sets:\n{hypotheses}        =>:\n            {conclusion}\n    {conclusion}\n"
        );
        let result = rt.run_litex_code(&code).unwrap();
        assert!(result.session_error.is_none(), "{code}");
        assert_eq!(result.success, expected, "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
    assert!(rt.run_litex_code("1=1\n").unwrap().success);
}

#[test]
fn maintained_nested_function_exist_tracer_keeps_cited_forall_and_release_routes() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/proof_nodes/exist/by_known_forall/nested_function_alpha.lit"
        ))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt).stringify();
    assert!(
        detail.contains("by_known_forall"),
        "actual theorem instantiation route: {detail}"
    );
    assert!(detail.contains("cite_fact_id"));
    assert!(detail.contains("proof_of_dom_facts"));
}

#[test]
fn nested_function_exist_reuse_rejects_changed_body_witness_carrier_and_kind() {
    let tracer = include_str!(
        "../../../../examples/proof_nodes/exist/by_known_forall/nested_function_alpha.lit"
    );
    for goal in [
        "exist w R st {fn(t R) R {f(t)+1}(0) = f(0), w=0}",
        "exist w R st {fn(t R) R {f(t)}(0) = f(1), w=0}",
        "exist w N st {fn(t R) R {f(t)}(0) = f(0), w=0}",
        "exist! w R st {fn(t R) R {f(t)}(0) = f(0), w=0}",
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(tracer).unwrap().success, "valid setup");
        let code = format!("claim:\n    ? forall f fn(x R) R:\n        {goal}\n    {goal}\n");
        let rejected = rt.run_litex_code(&code).unwrap();
        assert!(
            !rejected.success && rejected.session_error.is_none(),
            "must not reuse different conclusion: {goal}"
        );
        assert!(
            rt.run_litex_code("1=1\n").unwrap().success,
            "failure must discard locals"
        );
    }
}

#[test]
fn anonymous_function_free_argument_matching_keeps_local_binders_rigid() {
    let mut rt = runtime();
    for (source, goal, expected) in [
        ("forall a R:\n    fn(x R) R {a} = fn(x R) R {a}", "fn(t R) R {0} = fn(t R) R {0}", true),
        ("forall a R:\n    fn(x R) R {a} = fn(x R) R {a}", "fn(t R) R {t} = fn(t R) R {t}", false),
        ("forall a R:\n    fn(x R) (fn(y R) R) {fn(z R) R {a}} = fn(x R) (fn(y R) R) {fn(z R) R {a}}", "fn(t R) (fn(u R) R) {fn(v R) R {0}} = fn(t R) (fn(u R) R) {fn(v R) R {0}}", true),
        ("forall a R:\n    fn(x R) (fn(y R) R) {fn(z R) R {a}} = fn(x R) (fn(y R) R) {fn(z R) R {a}}", "fn(t R) (fn(u R) R) {fn(v R) R {t}} = fn(t R) (fn(u R) R) {fn(v R) R {t}}", false),
        ("forall a R:\n    fn(x R: x>0) R {a} = fn(x R: x>0) R {a}", "fn(t R: t<0) R {0} = fn(t R: t<0) R {0}", false),
        ("forall a R:\n    fn(x R) R {a} = fn(x R) R {a}", "fn(t N) R {0} = fn(t N) R {0}", false),
        ("forall a R:\n    fn(x R) R {a} = fn(x R) R {a}", "fn(t R) N {0} = fn(t R) N {0}", false),
        ("forall a R:\n    fn(x R) R {a} = fn(x R) R {a}", "fn(t, u R) R {0} = fn(t, u R) R {0}", false),
    ] {
        let tokens = crate::tokenize::Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::ForallFact(forall)) = &statements[0] else { panic!("parameter pattern") };
        let Fact::AtomicFact(crate::ast::fact::AtomicFact::EqualFact(pattern)) = Fact::from(forall.then_facts[0].clone()) else { panic!("pattern literal") };
        let tokens = crate::tokenize::Tokenizer::new().tokenize(goal, rt.current_file.clone()).unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::AtomicFact(crate::ast::fact::AtomicFact::EqualFact(goal))) = &statements[0] else { panic!("goal literal") };
        let matched = rt.match_forall_conclusion_args_to_subst(&[&pattern.left], &[&goal.left], &forall.typed_parameters.ordered_param_ids()).unwrap();
        assert_eq!(matched.is_some(), expected, "{source} -> {goal:?}");
    }
}

#[test]
fn nested_function_exist_instantiation_still_requires_the_cited_domain() {
    let setup = "thm positive_constant_witness:\n    ? forall a R:\n        a > 0\n        =>:\n            exist w R st {w=a, fn(t R) R {a}(0)>0}\n    witness exist w R st {w=a, fn(t R) R {a}(0)>0} from a:\n        a=a\n        fn(t R) R {a}(0)=a\n        fn(t R) R {a}(0)>0\n";
    for (premises, expected) in [
        ("        a > 0\n        =>:\n", true),
        ("", false),
        ("        a >= 0\n        =>:\n", false),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(setup).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "real witnessed source must pass"
        );
        let indent = if premises.is_empty() {
            "        "
        } else {
            "            "
        };
        let source = format!("claim:\n    ? forall a R:\n{premises}{indent}exist w R st {{w=a, fn(renamed R) R {{a}}(0)>0}}\n    exist w R st {{w=a, fn(renamed R) R {{a}}(0)>0}}\n");
        let run = rt.run_litex_code(&source).unwrap();
        assert_eq!(run.success, expected, "{source}");
        assert!(run.session_error.is_none());
        assert!(rt.run_litex_code("1=1\n").unwrap().success);
    }
}
