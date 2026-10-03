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
        "forall p finite_seq(R, 2):\n    p(0) = p(0)",
        "forall p finite_seq(R, 2):\n    p(3) = p(3)",
        "forall p finite_seq(R, 0):\n    p(1) = p(1)",
        "forall p seq(R):\n    p(0) = p(0)",
        "finite_seq(R, -1) = finite_seq(R, -1)",
        "finite_seq(R, 1 / 2) = finite_seq(R, 1 / 2)",
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

#[test]
fn sequence_struct_contract_publishes_flat_law_and_retains_source_evidence() {
    use crate::ast::fact::{ExistOrAndChainAtomicFact, Fact};
    use crate::execute::{ExecDefinitionStmtResult, ExecDefStructStmtResult, ExecStmtResult};
    use crate::store_fact_and_infer::StoreFactResult;

    let mut rt = runtime();
    let result = rt.run_litex_code("struct Op<A nonempty_set>:\n    zero A\n    add fn(x, y A) A\n    <=>:\n        forall x A:\n            exist y A st {add(x, y) = zero}").unwrap();
    assert!(result.success);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(ExecDefStructStmtResult::Success(proof))) = &result.statement_results[0] else { panic!("struct result") };
    assert_eq!(proof.definition_facts.len(), 1);
    let published = &proof.definition_facts[0];
    assert!(proof.field_scope.field_local_env.facts.facts_by_id.contains_key(&published.source_fact_id));
    let StoreFactResult::ForallFact(stored) = &published.store_and_infer.store else { panic!("flat forall") };
    assert_eq!(stored.fact.typed_parameters.ordered_param_ids().len(), 3);
    let ExistOrAndChainAtomicFact::ExistFact(witness) = &stored.fact.then_facts[0] else { panic!("existential stays inside") };
    let witness_id = witness.typed_parameters.ordered_param_ids()[0];
    assert!(!stored.fact.typed_parameters.ordered_param_ids().contains(&witness_id));
    assert!(rt.execution_environments_stack[0].facts.facts_by_id.values().any(|f| matches!(f, Fact::ForallFact(_))));
    assert!(!rt.execution_environments_stack[0].facts.facts_by_id.values().any(|f| matches!(f, Fact::ExistFact(_))));
    let detailed = crate::json_output::project_stmt_detailed(&result.statement_results[0], &rt).stringify();
    assert!(detailed.contains("definition_facts") && detailed.contains("source_fact_id"));
    let normal = crate::json_output::project_stmt_normal(&result.statement_results[0], &rt).stringify();
    assert!(normal.contains("exist y"));
    assert!(crate::knowledge_base::store_definition_memory(&rt.execution_environments_stack[0].definitions).is_err());
}

#[test]
fn sequence_struct_contract_local_struct_laws_do_not_escape_sketch() {
    let mut rt = runtime();
    let before = rt.execution_environments_stack[0].facts.facts_by_id.len();
    let result = rt.run_litex_code("sketch:\n    struct Local:\n        a R\n        b R\n        <=>:\n            a = b").unwrap();
    assert!(result.success);
    assert_eq!(rt.execution_environments_stack[0].facts.facts_by_id.len(), before);
    assert!(rt.def_struct_visible_in_stack("Local").is_none());
}

#[test]
fn sequence_struct_contract_failed_definition_publishes_no_laws() {
    let mut rt = runtime();
    let before = rt.execution_environments_stack[0].facts.facts_by_id.len();
    let result = rt.run_litex_code("struct Invalid:\n    a R\n    b R\n    <=>:\n        a = b\n        1 / 0 = a").unwrap();
    assert!(!result.success);
    assert_eq!(rt.execution_environments_stack[0].facts.facts_by_id.len(), before);
    assert!(rt.def_struct_visible_in_stack("Invalid").is_none());
}
