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

fn accepts(rt: &mut Runtime, code: &str) {
    let run = rt.run_litex_code(code).unwrap();
    assert!(run.success && run.session_error.is_none(), "{code}");
}

#[test]
fn function_preimages_run_the_durable_guarded_tracer() {
    accepts(
        &mut runtime(),
        include_str!("../../../../examples/wd/function_preimages.lit"),
    );
}

#[test]
fn function_preimages_reject_bad_members_and_keep_the_session() {
    let mut rt = runtime();
    accepts(
        &mut rt,
        "have fn reciprocal(x R: x != 0) R = 1 / x\nreciprocal(2) = 1 / 2\n",
    );
    for code in [
        "0 $in preimage(reciprocal, 1 / 2)",
        "3 $in preimage(reciprocal, 1 / 2)",
        "0 $in preimage_set(reciprocal, {1 / 2})",
        "3 $in preimage_set(reciprocal, {1 / 2})",
        "2 $in preimage_set(reciprocal, {})",
        "let bad = preimage(1, 2)",
        "let bad = preimage_set(1, {})",
        "let bad = preimage(reciprocal, reciprocal(0))",
    ] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        accepts(&mut rt, "2 $in preimage(reciprocal, 1 / 2)");
        assert!(!rt.plain_atom_is_visible("bad"));
    }
}

#[test]
fn function_preimages_allow_empty_and_outside_return_targets() {
    accepts(&mut runtime(), "have fn square(x R) R = x^2\npreimage(square, i) = preimage(square, i)\npreimage_set(square, {i}) = preimage_set(square, {i})\npreimage_set(square, {}) = preimage_set(square, {})\n");
}

#[test]
fn function_preimages_point_target_can_itself_be_a_set() {
    accepts(&mut runtime(), "have fn singleton(x R) power_set(R) = {x}\nsingleton(2) = {2}\n2 $in preimage(singleton, {2})\n2 $in preimage_set(singleton, {{2}})\nforall x preimage(singleton, {2}):\n    singleton(x) = {2}\n");
}

#[test]
fn function_preimages_aliases_transport_and_nested_substitution() {
    accepts(&mut runtime(), "have fn square(x R) R = x^2\nsquare(2) = 4\nhave alias fn(x R) R = square\nalias(2) = square(2) = 4\nlet fiber = preimage(alias, 4)\n2 $in fiber\nforall x fiber:\n    x $in R\n    alias(x) = 4\nforall y R:\n    preimage(square, y) = preimage(square, y)\n");
}

#[test]
fn function_preimages_tuples_preserve_arity_and_guards() {
    let mut rt = runtime();
    accepts(&mut rt, "have fn divide(a, b R: b != 0) R = a / b\ndivide(6, 2) = 3\n(6, 2) $in preimage(divide, 3)\n");
    for code in [
        "6 $in preimage(divide, 3)",
        "(6, 2, 3) $in preimage(divide, 3)",
        "(6, 0) $in preimage(divide, 3)",
        "(6, 0) $in preimage_set(divide, {3})",
    ] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
    accepts(&mut rt, "have fn add_pair(p cart(R, R)) R = p(1) + p(2)\nadd_pair((1, 2)) = 3\n(1, 2) $in preimage(add_pair, 3)\n");
}

#[test]
fn function_preimages_returned_and_literal_functions() {
    accepts(&mut runtime(), "have fn shift_by(a R) fn(x R) R = fn(x R) R {a + x}\nshift_by(1)(2) = 3\n2 $in preimage(shift_by(1), 3)\n2 $in preimage_set(shift_by(1), {3})\nlet pair = (3, 4)\npair(2) = 4\n2 $in preimage(pair, 4)\n");
}

#[test]
fn function_preimages_do_not_hide_malformed_constructor_calls() {
    for code in [
        "preimage(1)",
        "preimage_set(1)",
        "preimage(1, 2, 3)",
        "preimage_set(1, {}, {})",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_some(), "{code}");
    }
}

#[test]
fn function_preimages_own_their_names_and_migrated_witnesses_work() {
    accepts(
        &mut runtime(),
        "witness exist x R st {x = 2} from 2\nobtain source_input from exist x R st {x = 2}\nsource_input = 2\nhave target_value R = 3\nsource_input + target_value = 5\nhave fn square(x R) R = x^2\nsquare(2) = 4\n2 $in preimage(square, 4)\n2 $in preimage_set(square, {4})\n",
    );
    for code in ["preimage = 2", "preimage_set = 3"] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_some(), "{code}");
    }
}

#[test]
fn function_preimages_keep_unpublished_function_alias_boundary() {
    let mut rt = runtime();
    accepts(
        &mut rt,
        "have fn square(x R) R = x^2\nlet opaque_alias = square\n",
    );
    for code in [
        "let bad = preimage(opaque_alias, 4)",
        "let bad = preimage_set(opaque_alias, {4})",
    ] {
        let run = rt.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
        assert!(!rt.plain_atom_is_visible("bad"));
    }
}

#[test]
fn function_preimages_fields_and_templates_keep_their_signatures() {
    accepts(&mut runtime(), "struct Ops:\n    op fn(x R) R\n    tag N\nhave fn shift(x R) R = x + 1\nhave ops &Ops = (shift, 0)\n2 $in preimage(ops.op, ops.op(2))\n2 $in preimage_set(ops.op, {ops.op(2)})\ntemplate<S set>:\n    have fn identity(x S) S = x\n\\identity<R>(2) = 2\n2 $in preimage(\\identity<R>, 2)\n2 $in preimage_set(\\identity<R>, {2})\n");
}

#[test]
fn function_preimages_run_specific_strategy_and_infer_examples() {
    for source in [
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_strategy/preimage_membership.lit"),
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_strategy/preimage_set_membership.lit"),
        include_str!("../../../../examples/infer/atomic/in_preimage_projects_domain_and_value.lit"),
        include_str!("../../../../examples/infer/atomic/in_preimage_set_projects_domain_and_membership.lit"),
    ] {
        accepts(&mut runtime(), source);
    }
    for source in [
        include_str!("../../../../examples/wd_negative/preimage_not_callable.lit"),
        include_str!("../../../../examples/wd_negative/preimage_set_not_callable.lit"),
        include_str!("../../../../examples/wd_negative/preimage_target_not_well_defined.lit"),
    ] {
        let run = runtime().run_litex_code(source).unwrap();
        assert!(!run.success && run.session_error.is_none());
    }
}

#[test]
fn function_preimages_self_domain_aliases_expand_once_and_keep_context() {
    let mut rt = runtime();
    accepts(&mut rt, "forall S set, f fn(t S) S, x S:\n    S = preimage_set(f, S)\n    =>:\n        f(x) $in S\n");
    accepts(
        &mut rt,
        "have fn square(x R) R = x^2\nsquare(2) = 4\n2 $in preimage(square, 4)\n",
    );
    let run = rt.run_litex_code("3 $in preimage(square, 4)").unwrap();
    assert!(!run.success && run.session_error.is_none());
    accepts(&mut rt, "2 $in preimage_set(square, {4})");
}
