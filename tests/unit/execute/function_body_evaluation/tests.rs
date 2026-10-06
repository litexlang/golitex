use crate::knowledge_base::JsonValue;
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
fn function_value_parameter_applications_keep_checked_body_evidence() {
    let source = include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_object_definition/by_fn_application/function_value_parameter_application.lit"));
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none(), "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "test", None));
    assert_eq!(run.statement_results.len(), 8);
    for index in [2, 6] {
        let detailed = crate::json_output::project_stmt_detailed(&run.statement_results[index], &rt);
        assert!(field_rec(&detailed, "expanded_body").is_some());
        assert!(field_rec(&detailed, "function_body").is_some());
    }
}

#[test]
fn function_value_parameter_rejections_preserve_the_prefix_and_publish_nothing() {
    for (source, phase) in [
        (include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
            "/examples/negative/exact_function_domains/function_parameter_missing_inner_guard.lit")), "well_defined"),
        (include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
            "/examples/negative/exact_function_domains/function_parameter_wrong_complete_length.lit")), "well_defined"),
        (include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
            "/examples/negative/exact_function_domains/function_parameter_wrong_call_groups.lit")), "well_defined"),
        (include_str!(concat!(env!("CARGO_MANIFEST_DIR"),
            "/examples/negative/exact_function_domains/function_parameter_wrong_coordinate_value.lit")), "search_proof"),
    ] {
        let (prefix, target) = source.trim_end().rsplit_once('\n').unwrap();
        let mut rt = runtime();
        let setup = rt.run_litex_code(prefix).unwrap();
        assert!(setup.success && setup.session_error.is_none(), "{prefix}");
        let before: usize = rt.execution_environments_stack.iter()
            .map(|env| env.facts.facts_by_id.len()).sum();
        let run = rt.run_litex_code(target).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{target}");
        assert_eq!(run.statement_results.len(), 1);
        let result = crate::json_output::project_stmt_normal(&run.statement_results[0], &rt);
        let fields = result.as_object().unwrap();
        assert_eq!(fields.get("why_failed").unwrap().as_object().unwrap()
            .get("phase").unwrap().as_str().unwrap(), phase);
        assert!(fields.get("stores").unwrap().as_array().unwrap().is_empty());
        assert!(fields.get("infers").unwrap().as_array().unwrap().is_empty());
        let after: usize = rt.execution_environments_stack.iter()
            .map(|env| env.facts.facts_by_id.len()).sum();
        assert_eq!(before, after, "failed application published facts: {target}");
        assert!(rt.run_litex_code("1=1").unwrap().success);
    }
}

#[test]
fn curried_beta_value_preserves_both_application_carriers_and_evidence() {
    let mut rt = runtime();
    let source = "have fn add(x R) fn(y R) R = fn(y R) R {x+y}\nadd(2) $in fn(y R) R\nadd(2)(3) $in R\nadd(2)(3)=5\n";
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let detailed =
        crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
    let normalization = field_rec(&detailed, "normalization").unwrap();
    let steps = normalization
        .as_object()
        .unwrap()
        .get("expansions")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(steps.len(), 2);
    for step in steps {
        let fields = step.as_object().unwrap();
        assert!(fields.get("application_well_defined").is_some());
        assert!(fields.get("body_application_well_defined").is_some());
        assert!(fields.get("function_body").is_some());
        assert!(fields.get("continued_body").is_some());
    }
    assert!(field_rec(&detailed, "residual_equal").is_some());
    assert!(!rt.run_litex_code("0=1\n").unwrap().success);
}

#[test]
fn anonymous_three_layer_named_return_and_composition_compute_exact_values() {
    for source in [
        "fn(x R) (fn(y R) R) {fn(y R) R {x+y}}(2)(3)=5\n",
        "have fn add_three(x R) fn(u R) fn(v R) R = fn(y R) (fn(w R) R) {fn(z R) R {x+y+z}}\nadd_three(1)(2)(3)=6\n",
        "have fn step(x R) R = x+1\nhave fn choose(k N) fn(x R) R = step\nchoose(0)(2)=3\n",
        "have fn step(x R) R = x+1\nhave fn apply(g fn(x R) R, a R) R = g(a)\napply(step, 2)=3\n",
        "have fn compose(f, g fn(x R) R) fn(t R) R = fn(t R) R {f(g(t))}\nhave fn step(x R) R = x+1\ncompose(step, step)(2)=4\n",
        "have fn add(x R) fn(y R) R = fn(y R) R {x+y}\nadd(1/3)(1/6)=1/2\nadd(0.1)(0.2)=0.3\n",
        "have fn step(x R) R = x+1\nhave fn twice(x R) R = step(x)+step(x)\ntwice(2)=6\n",
    ] {
        let run = runtime().run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}: {:?}", run.session_error);
    }
}

#[test]
fn template_bodies_keep_specializations_and_continue_returned_calls() {
    for source in [
        "template<a R>:\n    have fn add(x R) fn(y R) R = fn(y R) R {a+x+y}\n\\add<1>(2)(3)=6\n\\add<2>(2)(3)=7\n",
        "template<S nonempty_set>:\n    have fn apply(g fn(x S) S, a S) S = g(a)\nhave fn step(x R) R = x+1\n\\apply<R>(step, 2)=3\n",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}: {:?}", run.session_error);
        let detailed = crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
        assert!(field_rec(&detailed, "instantiated_function").is_some());
    }
}

#[test]
fn curried_wrong_value_type_arity_and_missing_guards_reject_after_setup() {
    for (setup, goal) in [
        (
            "have fn add(x R) fn(y R) R = fn(y R) R {x+y}\n",
            "add(2)(3)=6\n",
        ),
        (
            "have fn add(x R) fn(y R) R = fn(y R) R {x+y}\n",
            "add(2)(i)=2+i\n",
        ),
        (
            "have fn add(x R) fn(y R) R = fn(y R) R {x+y}\n",
            "add(2)(3,4)=5\n",
        ),
        (
            "have fn choose(k N) fn(x R: x!=0) R = fn(x R: x!=0) R {1/x}\n",
            "choose(0)(0)=0\n",
        ),
        (
            "have fn choose(k R: k>0) fn(x R) R = fn(x R) R {x+k}\n",
            "choose(0)(3)=3\n",
        ),
        (
            "have fn add(x R) fn(y R) R = fn(y R) R {x+y}\n",
            "add(1/3)(1/6)=0.500000000001\n",
        ),
    ] {
        let mut rt = runtime();
        let before = rt.run_litex_code(setup).unwrap();
        assert!(before.success && before.session_error.is_none(), "{setup}");
        let rejected = rt.run_litex_code(goal).unwrap();
        assert!(
            !rejected.success && rejected.session_error.is_none(),
            "{goal}"
        );
        assert!(rt.run_litex_code("1=1\n").unwrap().success);
    }
}

#[test]
fn recursive_stored_equation_stops_without_proving_a_numeric_value() {
    let mut rt = runtime();
    let setup = rt
        .run_litex_code(
            "forall f fn(x N) N:\n    f = fn(x N) N {f(x+1)}\n    =>:\n        f(0) $in N\n",
        )
        .unwrap();
    assert!(setup.success && setup.session_error.is_none());
    let run = rt
        .run_litex_code(
            "forall f fn(x N) N:\n    f = fn(x N) N {f(x+1)}\n    =>:\n        f(0)=0\n",
        )
        .unwrap();
    assert!(!run.success && run.session_error.is_none());
    assert!(rt.run_litex_code("1=1\n").unwrap().success);
}

#[test]
fn the_selected_body_guard_is_required_even_with_a_broader_named_signature() {
    let mut rt = runtime();
    let valid = rt
        .run_litex_code(
            "forall f fn(x R) R:\n    f = fn(x R: x!=0) R {1/x}\n    =>:\n        f(2)=1/2\n",
        )
        .unwrap();
    assert!(valid.success && valid.session_error.is_none());
    let invalid = rt
        .run_litex_code(
            "forall f fn(x R) R:\n    f = fn(x R: x!=0) R {1/x}\n    =>:\n        f(0)=0\n",
        )
        .unwrap();
    assert!(!invalid.success && invalid.session_error.is_none());
    assert!(rt.run_litex_code("1=1\n").unwrap().success);
}

#[test]
fn many_sibling_calls_exhaust_the_local_budget_and_preserve_the_session() {
    let mut rt = runtime();
    let mut layer = vec![String::from("step(x)"); 70];
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|pair| {
                if pair.len() == 1 {
                    pair[0].clone()
                } else {
                    format!("({}+{})", pair[0], pair[1])
                }
            })
            .collect();
    }
    assert!(
        rt.run_litex_code("have fn step(x R) R = x+1\n")
            .unwrap()
            .success
    );
    let code = format!("{}=70", layer[0].replace("step(x)", "step(0)"));
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(&code, rt.current_file.clone())
        .unwrap();
    let mut stmts = rt.parse(&tokens).unwrap();
    let crate::ast::stmt::Stmt::Fact(crate::ast::fact::Fact::AtomicFact(
        crate::ast::fact::AtomicFact::EqualFact(goal),
    )) = stmts.remove(0)
    else {
        panic!("one equality")
    };
    // Exercise the local substitution budget directly; the statement-level
    // WD/transaction pipeline is covered by the value and guard tests above.
    let limited = rt
        .normalize_function_body(
            &goal.left,
            &goal.right,
            crate::execute::execute_fact_stmt::VerifyState::new(
                crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule,
            ),
        )
        .unwrap();
    assert!(limited.is_none());
    assert!(rt.run_litex_code("step(0)=1\n").unwrap().success);
}

#[test]
fn a_function_may_ignore_a_well_defined_argument_with_a_cyclic_body() {
    let mut rt = runtime();
    assert!(
        rt.run_litex_code("have fn ignore(x R) R = 1\n")
            .unwrap()
            .success
    );
    let run = rt
        .run_litex_code(
            "forall f fn(x R) R:\n    f = fn(x R) R {f(x+1)}\n    =>:\n        ignore(f(0))=1\n",
        )
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    assert!(!rt.run_litex_code("ignore(1/0)=1\n").unwrap().success);
    assert!(rt.run_litex_code("1=1\n").unwrap().success);
}

#[test]
fn one_step_beta_preserves_symbolic_arguments_and_checked_evidence() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!(
        "../../../../examples/proof_nodes/equal/by_object_definition/nested_call_one_step.lit"
    )).unwrap();
    assert!(run.success && run.session_error.is_none());
    for index in [3, 7] {
        let detail = crate::json_output::project_stmt_detailed(&run.statement_results[index], &rt);
        let normalization = field_rec(&detail, "normalization").unwrap();
        let steps = normalization.as_object().unwrap().get("expansions").unwrap().as_array().unwrap();
        assert_eq!(steps.len(), 1);
        let step = steps[0].as_object().unwrap();
        assert!(step.get("application_well_defined").is_some());
        assert!(step.get("body_application_well_defined").is_some());
        assert!(step.get("function_body").is_some());
    }
}

#[test]
fn exact_beta_body_still_requires_domains_and_does_not_accept_wrong_values() {
    for (setup, bad) in [
        ("have fn inner(x R) R = x+1\nhave fn outer(x R) R = x*x\nhave x R\n",
         "outer(inner(x))=inner(x)*inner(x)+1\n"),
        ("have fn inner(x R) R = x+1\nhave fn outer(x R) R = x*x\n",
         "outer(inner(i))=inner(i)*inner(i)\n"),
        ("", "forall f fn(x R) R:\n    f = fn(x R: x!=0) R {x*x}\n    =>:\n        f(0)=0*0\n"),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code(setup).unwrap().success);
        let run = rt.run_litex_code(bad).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{bad}");
        assert!(rt.run_litex_code("1=1\n").unwrap().success);
    }
}

#[test]
fn restriction_beta_consumes_exact_parent_wd_without_raising_premise_permissions() {
    use crate::ast::fact::{AtomicFact, Fact};
    use crate::ast::obj::Obj;
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};

    let source = "forall X, Y set, K power_set(X), f fn(x X) Y, point K:\n    point $in X\n    f(point) $in Y\n    fn(x K) Y {f(x)}(point) = f(point)\n";
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone()).unwrap();
    let mut stmts = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::ForallFact(forall)) = stmts.remove(0) else {
        panic!("one quantified diagnostic context")
    };
    // Inspect primitives within the same legitimate universal parameter
    // context. These unchanged scope/intro APIs do not execute a stmt branch.
    rt.run_in_local_env_and_take_env(|rt| {
        assert!(rt.introduce_typed_parameters(
            &forall.typed_parameters, VerifyState::top_level()
        )?.is_ok());
        for then in &forall.then_facts[..2] {
            let fact: Fact = then.clone().into();
            assert!(!rt.verify_fact(&fact, VerifyState::top_level())?.is_failed());
            rt.store_fact_and_infer(&fact, VerifyState::top_level())?;
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(goal)) =
            Fact::from(forall.then_facts[2].clone()) else {
            panic!("beta equality")
        };
        let parent_wd = match rt.verify_equal_fact_well_definedness(
            &goal, VerifyState::top_level()
        )? {
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::VerifyEqualFactWellDefinedResult::Success(p) => p,
            _ => panic!("parent equality WD must pass"),
        };
        let Obj::FnObj(app) = &goal.left else { panic!("literal application") };
        let expanded = rt.expanded_named_or_literal_anon_fn_application_body(app)?
            .expect("literal beta body exists");
        assert!(expanded.expanded_body == goal.right, "beta substitution must be exact");
        assert!(expanded.function_equal.path.is_empty(), "literal needs no invented equality");
        let child = VerifyState::new(VerifyStateLevel::BuiltinRule);
        let app_top = !rt.verify_obj_well_definedness(&goal.left, VerifyState::top_level())?.is_failed();
        let app_child = !rt.verify_obj_well_definedness(&goal.left, child)?.is_failed();
        let residual_child = !rt.verify_obj_well_definedness(&goal.right, child)?.is_failed();
        let top = rt.normalize_function_body(&goal.left, &goal.right, VerifyState::top_level())?;
        let restricted = rt.normalize_function_body(&goal.left, &goal.right, child)?;
        eprintln!("restriction beta stages: app_top={app_top}, app_builtin={app_child}, residual_builtin={residual_child}, normalize_top={}, normalize_builtin={}", top.is_some(), restricted.is_some());
        assert!(app_top && residual_child && top.is_some());
        assert!(!app_child && restricted.is_none(), "do not raise the ordinary normalizer ceiling");
        for level in [VerifyStateLevel::Direct, VerifyStateLevel::KnownSpecialProperty,
            VerifyStateLevel::BuiltinRule, VerifyStateLevel::Strategy] {
            assert!(rt.try_parent_checked_beta_with_parent_well_definedness(
                &goal, &parent_wd, VerifyState::new(level)
            )?.is_none(), "definition stage unavailable at {level:?}");
        }
        assert!(rt.try_parent_checked_beta_with_parent_well_definedness(
            &goal, &parent_wd, VerifyState::top_level()
        )?.is_some());
        let mut mismatched = goal.clone();
        std::mem::swap(&mut mismatched.left, &mut mismatched.right);
        assert!(rt.try_parent_checked_beta_with_parent_well_definedness(
            &mismatched, &parent_wd, VerifyState::top_level()
        )?.is_none(), "parent certificate must match both exact AST sides");
        Ok(())
    }).unwrap();

    // Public root entry remains run_litex_code -> exec_stmt. This is the
    // formerly rejected user-visible contract, not a direct exec branch call.
    let mut root = runtime();
    let run = root.run_litex_code(
        "claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point K:\n        fn(x K) Y {f(x)}(point) = f(point)\n    point $in X\n    f(point) $in Y\n    fn(x K) Y {f(x)}(point) = f(point)\n"
    ).unwrap();
    assert!(run.success && run.session_error.is_none(), "restriction beta root must verify");
    let detailed = crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &root);
    assert_eq!(field_rec(&detailed, "parent_well_defined_side"), Some(JsonValue::String("left".into())));
    assert!(field_rec(&detailed, "residual_proof").is_some());
}

#[test]
fn restricted_literal_beta_right_side_and_cited_residual_keep_evidence() {
    let mut rt = runtime();
    let run = rt.run_litex_code("claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point K:\n        f(point) = fn(x K) Y {f(x)}(point)\n    point $in X\n    f(point) $in Y\n    f(point) = fn(x K) Y {f(x)}(point)\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let detailed = crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
    assert_eq!(field_rec(&detailed, "parent_well_defined_side"), Some(JsonValue::String("right".into())));

    let mut rt = runtime();
    let run = rt.run_litex_code("claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point K, other Y:\n        f(point) = other\n        =>:\n            fn(x K) Y {f(x)}(point) = other\n    point $in X\n    f(point) $in Y\n    fn(x K) Y {f(x)}(point) = other\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let detailed = crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
    assert!(field_rec(&detailed, "parent_well_defined_side").is_some());
    let residual = field_rec(&detailed, "residual_proof").unwrap();
    assert!(field_rec(&residual, "cite_fact_id").is_some(), "residual must retain the actual equality citation ID after the local scope closes");
    let path = field_rec(&residual, "path").unwrap();
    assert_eq!(path.as_array().unwrap().len(), 1);
    assert_eq!(field_rec(&path, "from"), Some(JsonValue::String("f(point)".into())));
    assert_eq!(field_rec(&path, "to"), Some(JsonValue::String("other".into())));
}

#[test]
fn restricted_literal_beta_rejects_missing_guards_carriers_arity_and_wrong_body() {
    for source in [
        "claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point X:\n        fn(x K) Y {f(x)}(point) = f(point)\n    f(point) $in Y\n    fn(x K) Y {f(x)}(point) = f(point)\n",
        "claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point K:\n        fn(x K: x != point) Y {f(x)}(point) = f(point)\n    point $in X\n    f(point) $in Y\n    fn(x K: x != point) Y {f(x)}(point) = f(point)\n",
        "claim:\n    ? forall X, Y, W set, K power_set(X), f fn(x X) Y, point K:\n        fn(x K) W {f(x)}(point) = f(point)\n    point $in X\n    f(point) $in Y\n    fn(x K) W {f(x)}(point) = f(point)\n",
        "claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point K:\n        fn(x, y K) Y {f(x)}(point) = f(point)\n    point $in X\n    f(point) $in Y\n    fn(x, y K) Y {f(x)}(point) = f(point)\n",
        "claim:\n    ? forall X, Y set, K power_set(X), f fn(x X) Y, point K, other Y:\n        fn(x K) Y {f(x)}(point) = other\n    point $in X\n    f(point) $in Y\n    fn(x K) Y {f(x)}(point) = other\n",
    ] {
        let mut rt = runtime();
        let rejected = rt.run_litex_code(source).unwrap();
        assert!(!rejected.success && rejected.session_error.is_none(), "must reject through proof/WD: {source}");
        assert!(rt.run_litex_code("1=1\n").unwrap().success, "failed claim must leave the session usable");
    }
}

fn field_rec(value: &JsonValue, name: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(fields) => fields
            .get(name)
            .cloned()
            .or_else(|| fields.iter().find_map(|(_, v)| field_rec(v, name))),
        JsonValue::Array(items) => items.iter().find_map(|v| field_rec(v, name)),
        _ => None,
    }
}
