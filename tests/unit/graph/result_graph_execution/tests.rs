use super::render_result_graph_from_stmt_results;
use crate::prelude::*;
use crate::test_support::execute_source;

fn graph_output(source: &'static str) -> String {
    std::thread::Builder::new()
        .name("graph_output_large_stack".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            run_graph(GraphRequest::new(
                GraphKind::Result,
                RunRequest::new(RunTarget::code(source), RunOptions::default()),
                true,
            ))
            .1
        })
        .expect("spawn graph output test")
        .join()
        .expect("graph output test panicked")
}

#[test]
fn result_graph_records_statement_verification_proof_and_store_layers() {
    let output = graph_output("2 + 3 $in N\n");

    assert!(output.contains(r#""graph": "litex-result-graph""#));
    assert!(output.contains(r#""graph_version": "2""#));
    assert!(output.contains(r#""label": "-graph -e""#));
    assert!(output.contains(r#""kind": "statement""#));
    assert!(output.contains(r#""kind": "well_definedness""#));
    assert!(output.contains(r#""kind": "verification""#));
    assert!(output.contains(r#""kind": "proof""#));
    assert!(output.contains(r#""kind": "store""#));
    assert!(output.contains(r#""role": "AtomicFact""#));
    assert!(output.contains(r#""role": "DirectObject""#));
    assert!(output.contains(r#""kind": "argument""#));
    assert!(output.contains(r#""role": "BuiltinRule""#));
    assert!(output.contains(r#""kind": "verification""#));
    assert!(output.contains(r#""kind": "proof""#));
}

#[test]
fn result_graph_uses_fact_ids_for_inference_edges() {
    let output = graph_output("2 + 3 $in N\n");

    assert!(output.contains(r#""role": "NaturalMembershipImpliesNonnegative""#));
    assert!(output.contains(r#""kind": "premise""#));
    assert!(output.contains(r#""kind": "conclusion""#));
    assert!(output.contains(r#""id": "fact:f"#));
    assert!(output.contains(r#""fact_id": "f"#));
}

#[test]
fn result_graph_recurses_through_statement_children() {
    let output = graph_output("sketch:\n    1 = 1\n");

    assert!(output.contains(r#""role": "ProofBlockStmt""#));
    assert!(output.contains(r#""kind": "child""#));
    assert!(output.contains(r#""id": "stmt:0/execution/child:0""#));
}

#[test]
fn result_graph_recurses_through_claim_binder_well_definedness() {
    let output = graph_output("claim:\n    ? forall x R:\n        x = x\n");

    assert!(output.contains(r#""role": "ForallFact""#));
    assert!(output.contains(r#""role": "FactBinder""#));
    assert!(output.contains(r#""kind": "parameter_group""#));
    assert!(output.contains(r#""kind": "well_definedness""#));
}

#[test]
fn result_graph_projects_def_struct_named_local_results() {
    let output =
        graph_output("struct ValueBox<S set>:\n    value S\n    <=>:\n        value = value\n");

    assert!(output.contains(r#""role": "DefStructLocalEnv""#));
    assert!(output.contains(r#""role": "StructureParameterDefinition""#));
    assert!(output.contains(r#""role": "DefStructFieldLocalEnv""#));
    assert!(output.contains(r#""kind": "field_type""#));
    assert!(output.contains(r#""kind": "equivalent_fact""#));
}

#[test]
fn result_graph_projects_inductive_function_local_results() {
    let output = graph_output(
        r#"have fn step(x R+) R+ = (x + 2 / x) / 2
have fn iterate(n N) R+ by induc n from 0:
    case n = 0: 1
    case n > 0: step(iterate(n - 1))
"#,
    );

    assert!(output.contains(r#""role": "HaveFnByInducWellDefinednessLocalEnv""#));
    assert!(output.contains(r#""role": "HaveFnByInducVerificationLocalEnv""#));
    assert!(output.contains(r#""role": "HaveFnByInducCaseDisjointness""#));
    assert!(output.contains(r#""kind": "recursive_function""#));
    assert!(output.contains(r#""kind": "assumption_store""#));
}

#[test]
fn completed_result_graph_does_not_need_runtime() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("runtime_free_result_graph");
    let (results, error) = execute_source("2 + 3 $in N", &mut runtime);
    assert!(error.is_none());
    drop(runtime);

    let output =
        render_result_graph_from_stmt_results(RunTargetKind::Code, "dropped", true, &results);
    assert!(output.contains(r#""graph": "litex-result-graph""#));
    assert!(output.contains(r#""role": "NaturalMembershipImpliesNonnegative""#));
    assert!(output.contains(r#""kind": "well_definedness""#));
}
