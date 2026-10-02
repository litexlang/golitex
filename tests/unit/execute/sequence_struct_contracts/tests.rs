use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    })
}

fn check(source: &str, expected: bool) {
    let mut rt = runtime();
    let result = rt.run_litex_code(source).unwrap();
    assert!(result.session_error.is_none(), "{source}\n{:?}", result.session_error);
    assert_eq!(result.success, expected, "{source}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn sequence_struct_contract_sequence_tracer() {
    check(include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/sequence_one_based.lit"), true);
}

#[test]
fn sequence_struct_contract_rejects_old_index_domains_and_extra_guards() {
    for source in [
        "seq(R) = fn(k N) R",
        "finite_seq(R, 2) = fn(k closed_range(0, 1)) R",
        "finite_seq(R, 2) = fn(k N+: k < 2) R",
        "finite_seq(R, 2) = fn(k N+: k <= 3) R",
        "finite_seq(R, 2) = fn(k N+: k <= 2, k > 1) R",
        "finite_seq(R, 2) = fn(k closed_range(1, 2)) N",
    ] { check(source, false); }
}

#[test]
fn sequence_struct_contract_struct_tracer() {
    check(include_str!("../../../../examples/proof_nodes/exist/by_known_forall/struct_existential_law.lit"), true);
}

#[test]
fn sequence_struct_contract_exist_matching_preserves_carrier_and_body() {
    for source in [
        "forall f fn(x, y R) R:\n    forall x R:\n        exist y R st {f(x, y) = 0}\n    =>:\n        exist z {0} st {f(2, z) = 0}",
        "forall f fn(x R) R:\n    exist x {0} st {f(x) = 0}\n    =>:\n        exist y {0} st {f(y) = 1}",
        "forall f fn(x, y R) R:\n    forall x R:\n        exist y R st {f(x, y) = 0}\n    =>:\n        exist z R st {f(2, z) = 1}",
    ] { check(source, false); }
}

#[test]
fn sequence_struct_contract_struct_guards_are_retained() {
    let definition = "struct Guarded:\n    zero R\n    add fn(x, y R) R\n    <=>:\n        forall x R:\n            x != 0\n            =>:\n                exist y R st {add(x, y) = zero}\n";
    check(&format!("{definition}forall s &Guarded:\n    exist z R st {{s.add(2, z) = s.zero}}"), true);
    check(&format!("{definition}forall s &Guarded:\n    exist z R st {{s.add(0, z) = s.zero}}"), false);
}
