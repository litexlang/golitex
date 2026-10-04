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
fn a_long_acyclic_expansion_exhausts_the_local_budget_and_preserves_the_session() {
    let mut rt = runtime();
    let mut source = String::from("have fn chain_0(x N) N = x+1\n");
    for index in 1..=70 {
        source.push_str(&format!(
            "have fn chain_{index}(x N) N = chain_{}(x)+1\n",
            index - 1
        ));
    }
    let setup = rt.run_litex_code(&source).unwrap();
    assert!(setup.success && setup.session_error.is_none());
    let limited = rt.run_litex_code("chain_70(0)=71\n").unwrap();
    assert!(!limited.success && limited.session_error.is_none());
    assert!(rt.run_litex_code("chain_0(0)=1\n").unwrap().success);
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
