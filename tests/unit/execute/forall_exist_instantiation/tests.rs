use crate::ast::fact::{exist_shaped_fact_free_args_ref, exist_shaped_fact_from_fact, exist_shaped_fact_to_fact, Fact};
use crate::ast::stmt::Stmt;
use crate::exec_env::exist_shaped_fact_index_key::{exist_shaped_fact_alpha_match_key, exist_shaped_fact_can_prove_goal, exist_shaped_fact_known_lookup_keys};
use crate::exec_env::known_forall_conclusion_memory::exist_at_forall_location;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
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
fn compact_subcover_exist_instantiation_keeps_nested_alpha_and_requirements() {
    let mut rt = runtime();
    let original = include_str!("../../../../showcases/math_concepts_in_litex/9_topology/main.lit");
    let prefix = original
        .split("thm continuous_image_of_compact_is_compact:")
        .next()
        .unwrap();
    let setup = rt.run_litex_code(prefix).unwrap();
    assert!(
        setup.success && setup.session_error.is_none(),
        "original 15 roots must pass"
    );
    let source = "forall X set, open_sets power_set(power_set(X)), K power_set(X), Index set, cover fn(index Index) open_sets:\n    $is_compact_subset(X, open_sets, K)\n    K $subset family_union(fn_range(cover))\n    =>:\n        exist J power_set(Index) st {$is_finite_set(J), K $subset family_union(fn_range(fn(index J) open_sets {cover(index)}))}\n";
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let mut statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::ForallFact(context)) = statements.remove(0) else {
        panic!("quantified context")
    };
    rt.run_in_local_env_and_take_env(|rt| {
        assert!(rt.introduce_typed_parameters(&context.typed_parameters, VerifyState::top_level())?.is_ok());
        // These are the actual root goal's hypotheses, never a trusted target.
        for hypothesis in &context.dom_facts {
            rt.store_fact_and_infer(hypothesis, VerifyState::top_level())?;
        }
        let goal_fact: Fact = context.then_facts[0].clone().into();
        let goal = exist_shaped_fact_from_fact(&goal_fact).unwrap();
        assert!(!rt.verify_exist_shaped_fact_well_definedness(&goal, VerifyState::top_level())?.is_failed());
        let mut cites = Vec::new();
        for key in exist_shaped_fact_known_lookup_keys(&goal) {
            for env in rt.execution_environments_stack.iter().rev() {
                if let Some(entries) = env.facts.known_forall_conclusions.by_exist.get(&key) {
                    cites.extend(entries.iter().cloned());
                }
            }
        }
        eprintln!("compact exist lookup: {} candidates", cites.len());
        assert!(!cites.is_empty(), "property must publish an existential forall conclusion");
        let child = VerifyState::new(VerifyStateLevel::BuiltinRule);
        for cite in &cites {
            let Some(Fact::ForallFact(forall)) = rt.fact_by_id_in_stack(cite.fact_id).cloned() else { continue };
            let Some(conclusion) = exist_at_forall_location(&forall, &cite.location) else { continue };
            assert!(exist_shaped_fact_can_prove_goal(&conclusion, &goal));
            let aligned = rt.align_exist_conclusion(&conclusion, &goal).expect("witness alignment");
            let ids = forall.typed_parameters.ordered_param_ids();
            let left = exist_shaped_fact_free_args_ref(&aligned);
            let right = exist_shaped_fact_free_args_ref(&goal);
            eprintln!("compact exist free args: {} vs {}", left.len(), right.len());
            let matched = rt.match_forall_conclusion_args_to_subst(&left, &right, &ids)?;
            if let Some((mut subst, _)) = matched {
                let complete = rt.complete_forall_subst_from_dom_facts(&forall, &mut subst, &ids)?;
                eprintln!("compact exist match=true, complete={complete}");
                if complete {
                    let instantiated = rt.inst_fact(&exist_shaped_fact_to_fact(&aligned), &subst).expect("fully bound existential");
                    let instantiated = exist_shaped_fact_from_fact(&instantiated).unwrap();
                    eprintln!("compact exist whole: text_key_equal={}, structural_alpha_equal={}", exist_shaped_fact_alpha_match_key(&instantiated)==exist_shaped_fact_alpha_match_key(&goal), plain_exist_facts_alpha_equal(instantiated.plain(),goal.plain()));
                    let requirements = rt.prove_forall_instantiation_requirements(&forall, &subst, child)?;
                    eprintln!("compact exist type/dom requirements={}", requirements.is_some());
                }
            } else {
                for i in 1..=left.len() {
                    let ok = rt.match_forall_conclusion_args_to_subst(&left[..i], &right[..i], &ids)?.is_some();
                    eprintln!("compact exist arg prefix {i}: {ok}; pattern={}, goal={}", left[i-1].readable_string(), right[i-1].readable_string());
                    if !ok {
                        // Independently recover the missing free argument from
                        // the already assumed cover premise. This observes the
                        // later comparison, without accepting a proof or
                        // changing the production matching path.
                        if let Some((mut subst, _)) = rt.match_forall_conclusion_args_to_subst(&left[..i-1], &right[..i-1], &ids)? {
                            let complete = rt.complete_forall_subst_from_dom_facts(&forall, &mut subst, &ids)?;
                            eprintln!("compact exist diagnostic dom completion={complete}");
                            if complete {
                                let instantiated = rt.inst_fact(&exist_shaped_fact_to_fact(&aligned), &subst).expect("diagnostic fully bound exist");
                                let instantiated = exist_shaped_fact_from_fact(&instantiated).unwrap();
                                eprintln!("compact exist diagnostic whole: text_key_equal={}, structural_alpha_equal={}", exist_shaped_fact_alpha_match_key(&instantiated)==exist_shaped_fact_alpha_match_key(&goal), plain_exist_facts_alpha_equal(instantiated.plain(),goal.plain()));
                                eprintln!("compact exist diagnostic type/dom requirements={}", rt.prove_forall_instantiation_requirements(&forall, &subst, child)?.is_some());
                            }
                        }
                        break;
                    }
                }
            }
        }
        Ok(())
    }).unwrap();
    // Public production entry: the expected same-goal specialization.
    let run = rt.run_litex_code("claim:\n    ? forall X set, open_sets power_set(power_set(X)), K power_set(X), Index set, cover fn(index Index) open_sets:\n        $is_compact_subset(X, open_sets, K)\n        K $subset family_union(fn_range(cover))\n        =>:\n            exist J power_set(Index) st {$is_finite_set(J), K $subset family_union(fn_range(fn(index J) open_sets {cover(index)}))}\n    cover $in fn(index Index) open_sets\n    exist J power_set(Index) st {$is_finite_set(J), K $subset family_union(fn_range(fn(index J) open_sets {cover(index)}))}\n").unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "compact subcover specialization must verify"
    );
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
        let indent = if premises.is_empty() { "        " } else { "            " };
        let source = format!("claim:\n    ? forall a R:\n{premises}{indent}exist w R st {{w=a, fn(renamed R) R {{a}}(0)>0}}\n    exist w R st {{w=a, fn(renamed R) R {{a}}(0)>0}}\n");
        let run = rt.run_litex_code(&source).unwrap();
        assert_eq!(run.success, expected, "{source}");
        assert!(run.session_error.is_none());
        assert!(rt.run_litex_code("1=1\n").unwrap().success);
    }
}
