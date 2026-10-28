use crate::prelude::*;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

fn accepted(rt: &mut Runtime, source: &str) {
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{source}\n{}",
        crate::json_output::emit_run_detailed(&run, rt, "struct-return", None)
    );
    assert!(run.statement_results.iter().all(|stmt| !stmt.is_failed()));
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

fn rejected(rt: &mut Runtime, source: &str) {
    let before = rt.top_exec_env().facts.facts_by_id.len();
    let run = rt.run_litex_code(source).unwrap();
    assert!(!run.success && run.session_error.is_none(), "{source}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert_eq!(
        rt.top_exec_env().facts.facts_by_id.len(),
        before,
        "failed statement published facts"
    );
}

#[test]
fn struct_return_fields_factories_templates_and_generic_carriers() {
    accepted(
        &mut runtime(),
        include_str!("../../../../examples/wd/struct_return_field_access.lit"),
    );
}

#[test]
fn struct_return_fields_preserve_argument_template_and_field_guards() {
    let mut rt = runtime();
    accepted(
        &mut rt,
        include_str!("../../../../examples/wd/struct_return_field_access.lit"),
    );
    for source in [
        "make(i).op(3) = 5",
        "make(2).op(i) = 5",
        "make(2).op(3) = 6",
        "make(2).missing = 0",
        "make(2).tag.extra = 0",
        "\\pair<N>(-1, 2).first = -1",
    ] {
        rejected(&mut rt, source);
    }
    accepted(&mut rt, "have fn positive(a R+) &Box = make(a)\ntemplate<a R+>:\n    have shifted_positive &Box = (fn(x R) R {x+a}, 0)");
    rejected(&mut rt, "positive(0).tag = 0");
    rejected(&mut rt, "\\shifted_positive<0>.tag = 0");
    rejected(&mut rt, "0 = 1");
}

#[test]
fn struct_return_fields_membership_does_not_choose_a_view() {
    let mut rt = runtime();
    accepted(&mut rt, "struct Pair:\n    first R\n    second R\nhave fn raw(x R) cart(R, R) = (x, x)\nraw(2) $in &Pair");
    rejected(&mut rt, "raw(2).first = 2");
    accepted(
        &mut rt,
        "have fn pair(x R) &Pair = (x, x)\nlet alias = pair",
    );
    rejected(&mut rt, "alias(2).first = 2");
}

#[test]
fn struct_return_fields_nested_values_and_declared_types() {
    let mut rt = runtime();
    accepted(
        &mut rt,
        include_str!("../../../../examples/wd/struct_return_field_access.lit"),
    );
    accepted(&mut rt, "struct Outer:\n    inner &Box\n    tag N\nforall b &Box:\n    (b, 0) $in &Outer\nhave fn outer(a R) &Outer = (make(a), 0)");
    accepted(&mut rt, "outer(2).inner.op(3) = 5\nouter(2).inner.tag = 0\nouter(2).inner.tag $in N\nrelease struct def outer(2)");
    accepted(
        &mut rt,
        "thm nested_type:\n    ? forall maker fn(a R) &Outer:\n        maker(1).inner.tag $in N",
    );
    rejected(&mut rt, "outer(2).inner.op(3) = 6");
}

#[test]
fn struct_return_fields_do_not_bypass_original_or_callable_field_guards() {
    let mut rt = runtime();
    accepted(
        &mut rt,
        "struct NonzeroOp:\n    call fn(x R: x != 0) R\n    tag N",
    );
    accepted(&mut rt, "thm good_guard:\n    ? forall maker fn(a R) &NonzeroOp:\n        maker(1).call(2) = maker(1).call(2)");
    rejected(&mut rt, "thm bad_guard:\n    ? forall maker fn(a R) &NonzeroOp:\n        maker(1).call(0) = maker(1).call(0)");
    rejected(&mut rt, "thm alternate_signature:\n    ? forall maker fn(a R+) &NonzeroOp:\n        maker $in fn(a R) &NonzeroOp\n        =>:\n            maker(0).tag = maker(0).tag");
    rejected(&mut rt, "0 = 1");
}

#[test]
fn struct_return_fields_keep_typed_sources_in_detailed_output() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/wd/struct_return_field_access.lit"
        ))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = crate::json_output::emit_run_detailed(&run, &rt, "struct-return", None);
    for evidence in [
        "struct_field_value",
        "function_tuple",
        "template_tuple",
        "receiver_well_defined",
        "applicability",
    ] {
        assert!(json.contains(evidence), "missing {evidence}");
    }
    // The existing compiler rejects unsupported struct evidence for the whole
    // artifact; this verifier repair does not pretend to add Lean struct support.
    assert!(crate::compile_to_lean::compile_run(&run, rt, "StructReturn").is_err());
}
