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

fn check(rt: &mut Runtime, source: &str, expected: &[bool]) {
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.session_error.is_none(),
        "{source}\n{:?}",
        run.session_error
    );
    assert_eq!(
        run.statement_results
            .iter()
            .map(|s| !s.is_failed())
            .collect::<Vec<_>>(),
        expected,
        "{source}"
    );
    assert_eq!(run.success, expected.iter().all(|ok| *ok));
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn struct_field_instantiation_preserves_generic_concrete_nested_and_dependent_domains() {
    let source = include_str!("../../../../examples/wd/struct_field_instantiation.lit");
    check(&mut runtime(), source, &[true; 8]);
}

#[test]
fn struct_field_instantiation_rejects_wrong_argument_carriers_and_false_laws() {
    for goal in ["s.add(i, 0) = s.add(i, 0)", "s.add(0, 0) = 1"] {
        let source = format!("struct Op<A nonempty_set>:\n    zero A\n    add fn(x, y A) A\nthm bad:\n    ? forall s &Op<R>:\n        {goal}\n0 = 1");
        check(&mut runtime(), &source, &[true, false, false]);
    }
}

#[test]
fn struct_field_instantiation_keeps_callable_guards() {
    let mut rt = runtime();
    check(
        &mut rt,
        "struct NonzeroOp<A nonempty_set, zero A>:\n    tag N\n    call fn(x A: x != zero) A",
        &[true],
    );
    check(&mut rt, "thm guarded:\n    ? forall s &NonzeroOp<R, 0>, x R:\n        x != 0\n        =>:\n            s.call(x) = s.call(x)", &[true]);
    check(
        &mut rt,
        "thm unguarded:\n    ? forall s &NonzeroOp<R, 0>:\n        s.call(0) = s.call(0)",
        &[false],
    );
    check(&mut rt, "0 != 0\n0 = 1", &[false, false]);
}

#[test]
fn struct_field_instantiation_rejects_scalar_paths_and_unknown_fields() {
    for goal in ["s.zero.extra = s.zero.extra", "s.missing = s.missing"] {
        let source = format!("struct Op<A nonempty_set>:\n    zero A\n    add fn(x, y A) A\nthm bad:\n    ? forall s &Op<R>:\n        {goal}");
        let run = runtime().run_litex_code(&source).unwrap();
        assert!(!run.success, "{source}");
    }
}

#[test]
fn struct_field_instantiation_does_not_open_nested_laws() {
    let mut rt = runtime();
    check(&mut rt, "struct Inner<A nonempty_set>:\n    first A\n    second A\n    <=>:\n        first = second\nstruct Outer<A nonempty_set>:\n    inner &Inner<A>\n    tag N", &[true, true]);
    check(
        &mut rt,
        "thm without_release:\n    ? forall s &Outer<R>:\n        s.inner.first = s.inner.second",
        &[false],
    );
    check(&mut rt, "thm with_release:\n    ? forall s &Outer<R>:\n        s.inner.first = s.inner.second\n    release struct def s.inner", &[true]);
}
