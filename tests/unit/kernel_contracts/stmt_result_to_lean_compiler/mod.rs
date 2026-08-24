mod builtin_evidence_and_fact_ids;
mod definitions_and_collections;
mod existentials_claims_and_theorems;
mod forall_and_direct_fact_proofs;
mod known_forall_and_transformations;
mod proof_composition_and_scopes;
mod registered_rules_and_environments;
mod result_schema_contracts;

fn run_registered_rule_test(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name("stmt-result-direct-compiler-test".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("spawn direct-compiler test thread")
        .join()
        .expect("direct-compiler test panicked");
}
