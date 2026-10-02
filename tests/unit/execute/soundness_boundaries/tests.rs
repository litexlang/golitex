use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(code: &str, expected_statements: &[bool]) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(code).expect("valid Litex input");
    let actual: Vec<_> = result
        .statement_results
        .iter()
        .map(|statement| !statement.is_failed())
        .collect();
    assert!(result.session_error.is_none(), "{code}\n{:?}", result.session_error);
    assert_eq!(actual, expected_statements, "{code}");
    assert_eq!(result.success, expected_statements.iter().all(|&ok| ok), "{code}");
    assert_eq!(runtime.execution_environments_stack.len(), 1, "{code}");
}

#[test]
fn explicit_theorem_calls_require_every_instantiated_parameter_type() {
    let theorem = "thm only_natural:\n    ? forall n N:\n        n >= 0\n";
    check(&format!("{theorem}release thm only_natural(-1)\n-1 >= 0\n"), &[true, false, false]);
    check(&format!("{theorem}by thm only_natural(-1) => -1 >= 0\n"), &[true, false]);
    check(&format!("{theorem}release thm only_natural(0)\n0 >= 0\n"), &[true, true, true]);
    check("thm constant:\n    ? forall n N:\n        1 = 1\nrelease thm constant(1 / 0)\n", &[true, false]);
}

#[test]
fn existential_witness_types_are_proved_before_local_binder_facts() {
    check("witness exist x {1} st {x = 0} from 0\n", &[false]);
    check("witness exist x {1} st {x = 1} from 1\n", &[true]);
    check("witness exist x nonempty_set st {x = {}} from {}\n", &[false]);
    check("witness exist x nonempty_set st {x = {1}} from {1}\n", &[true]);
    check("witness exist x {1} st {x = 0} from 0:\n    x = 0\n", &[false]);
}

#[test]
fn predicate_witness_requires_predicate_call_types() {
    let prop = "prop has_any(a N):\n    exist x R st {x = 0}\n";
    check(&format!("{prop}witness $has_any(-1) from 0\n"), &[true, false]);
    check(&format!("{prop}witness $has_any(0) from 0\n"), &[true, true]);
}

#[test]
fn adjacent_predicate_and_object_entry_points_keep_their_type_boundary() {
    let prop = "prop has_any(a N):\n    exist x R st {x = 0}\n";
    check(&format!("{prop}$has_any(-1)\n"), &[true, false]);
    check(&format!("{prop}by def $has_any(-1)\n"), &[true, false]);
    check(&format!("{prop}obtain x from $has_any(-1)\n"), &[true, false]);
    check("have x {1} = 0\n", &[false]);
    check("have x {1} = 1\n", &[true]);
    check("have x {}\n", &[false]);
}

#[test]
fn unstructured_induction_has_a_base_scope_without_its_hypothesis() {
    let bad = "prop bad(n Z):\n    1 = 2\n";
    check(&format!("{bad}by induc n from 0:\n    ? $bad(n)\n$bad(0)\n1 = 2\n"), &[true, false, false, false]);
    check(&format!("{bad}by strong_induc n from 0:\n    ? $bad(n)\n"), &[true, false]);
    check("by induc n from 0:\n    ? n = n\n", &[true]);
    check("by strong_induc n from 0:\n    ? n = n\n", &[true]);
}

#[test]
fn self_dependent_theorem_premise_fails_without_recursing_forever() {
    let theorem = "thm with_premise:\n    ? forall n Z:\n        n >= 0\n        =>:\n            n >= 0\n";
    check(&format!("{theorem}release thm with_premise(-1)\n"), &[true, false]);
    check(&format!("{theorem}release thm with_premise(0)\n"), &[true, true]);

    for (name, premise, argument) in [
        ("chain_self", "n < 0 < n", "1"),
        ("and_self", "n < 0 and n > 0", "0"),
        ("or_self", "n < 0 or n > 0", "0"),
        ("exist_self", "exist x {n} st {x = 0}", "1"),
    ] {
        check(
            &format!(
                "thm {name}:\n    ? forall n Z:\n        {premise}\n        =>:\n            {premise}\nrelease thm {name}({argument})\n"
            ),
            &[true, false],
        );
    }
}
