//! Normal feedback for completed and rejected proof stages.
use super::helper::{array_of_strings, fact_source_line, object_for, store_fact_texts, string};
use super::json_keys::localize_key;
use super::project_normal::{build_proof_method, project_stmt_normal, verify_goal_fact};
use crate::ast::Stmt;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_by_stmt::*;
use crate::execute::execute_def_thm_stmt::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    SearchProofByKnownForallFact, VerifyEqualityFailed,
};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::*;
use crate::execute::execute_fact_stmt::verify_forall_fact::*;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    DetailedObjWellDefinedProof, ObjWellDefinedProofByDef,
};
use crate::execute::execute_proof_block_stmt::*;
use crate::execute::execute_witness_stmt::*;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
use crate::run::run_source::RunSource;

mod blocks;
mod commands;
mod verification;

use blocks::{claim_steps, theorem_steps, witness_steps};
use commands::{by_steps, invocation_steps};
use verification::{method, verification_step, verification_steps};

pub(super) fn project_statement(
    result: &ExecStmtResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    line: Option<usize>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    let mut output = project_stmt_normal(result, rt);
    field(&mut output, rt, "kind", string("statement"));
    if let Some(line) = line {
        field(&mut output, rt, "line", number(line));
        if let Some(source) = source {
            field(&mut output, rt, "file", string(source.origin.to_string()));
            if let Some(raw) = source.block(line) {
                field(&mut output, rt, "source", string(raw));
            }
        }
    }
    let steps = match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => {
            field(
                &mut output,
                rt,
                "proof_method",
                method(&proof.verify_result, rt, scopes),
            );
            let mut steps = verification_steps(&proof.verify_result, rt, source, scopes);
            if matches!(&proof.verify_result, VerifyFactResult::ForallFact(_)) {
                steps.push(publish(rt, None, &[&proof.store_and_infer_result]));
            }
            steps
        }
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(verification)) => {
            verification_steps(verification, rt, source, scopes)
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(claim)) => {
            claim_steps(claim, rt, source, scopes)
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(sketch)) => match sketch {
            ExecSketchStmtResult::Success(proof) => {
                let local = scoped(scopes, &proof.local_env);
                body_steps(
                    &proof.proof_steps,
                    &[],
                    source,
                    children(source, line),
                    rt,
                    &local,
                )
            }
            ExecSketchStmtResult::Failed(ExecSketchStmtFailed::ProofBody(failure)) => {
                failed_body_steps(failure, &[], source, children(source, line), rt, scopes)
            }
        },
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(theorem)) => {
            theorem_steps(theorem, rt, source, scopes)
        }
        ExecStmtResult::Witness(witness) => witness_steps(witness, rt, source, line, scopes),
        ExecStmtResult::By(proof) => by_steps(proof, rt, source, line, scopes),
        ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(proof),
        )) => {
            let local = scoped(scopes, &proof.local_env);
            let mut steps = invocation_steps(
                &proof.call,
                &proof.callee,
                &proof.type_proofs,
                &proof.dom_proofs,
                rt,
                source,
                &local,
            );
            steps.push(publish(rt, None, &proof.stored.iter().collect::<Vec<_>>()));
            steps
        }
        _ => Vec::new(),
    };
    if !steps.is_empty() {
        field(&mut output, rt, "steps", JsonValue::Array(steps));
    }
    output
}

fn forall_open(
    fact: &Fact,
    assumed_count: usize,
    rt: &Runtime,
    source: Option<&RunSource>,
) -> Vec<JsonValue> {
    let Fact::ForallFact(fact) = fact else {
        return Vec::new();
    };
    let line = fact.line_file.as_ref().map(|position| position.line);
    let mut steps = introduce_parameters(&fact.typed_parameters, line, rt);
    steps.extend(
        fact.dom_facts
            .iter()
            .take(assumed_count)
            .map(|fact| assumption(fact, rt, source)),
    );
    steps
}

fn introduce_parameters(
    parameters: &crate::ast::param::TypedParameterList,
    line: Option<usize>,
    rt: &Runtime,
) -> Vec<JsonValue> {
    let mut steps = Vec::new();
    for group in &parameters.groups {
        for name in &group.params {
            let mut fields = vec![
                ("kind", string("introduce_parameter")),
                ("name", string(name.to_string())),
                ("domain", string(group.param_type.display_string())),
            ];
            if let Some(line) = line {
                fields.push(("line", number(line)));
            }
            steps.push(object_for(rt, fields));
        }
    }
    steps
}

fn assumption(fact: &Fact, rt: &Runtime, source: Option<&RunSource>) -> JsonValue {
    let mut fields = vec![
        ("kind", string("assume")),
        ("fact", string(fact.readable_string())),
    ];
    if let Some(location) = fact_source_line(fact) {
        fields.push(("line", number(location.line)));
        if let Some(raw) = source
            .filter(|source| source.origin == location.origin)
            .and_then(|source| source.line(location.line))
        {
            fields.push(("source", string(raw)));
        }
    }
    object_for(rt, fields)
}

fn body_steps(
    results: &[ExecStmtResult],
    statements: &[Stmt],
    source: Option<&RunSource>,
    lines: &[usize],
    rt: &Runtime,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    results
        .iter()
        .enumerate()
        .map(|(index, result)| {
            let line = statements
                .get(index)
                .and_then(super::source::statement_source_line)
                .map(|position| position.line)
                .or_else(|| lines.get(index).copied());
            project_statement(result, rt, source, line, scopes)
        })
        .collect()
}

fn failed_body_steps(
    failed: &ProofBlockBodyFailed,
    statements: &[Stmt],
    source: Option<&RunSource>,
    lines: &[usize],
    rt: &Runtime,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let mut steps = body_steps(&failed.prior_steps, statements, source, lines, rt, scopes);
    let line =
        super::source::statement_source_line(&failed.statement).map(|position| position.line);
    steps.push(project_statement(&failed.result, rt, source, line, scopes));
    steps
}

fn publish(
    rt: &Runtime,
    theorem: Option<String>,
    stores: &[&StoreFactAndInferResult],
) -> JsonValue {
    let facts = stores
        .iter()
        .flat_map(|store| store_fact_texts(&store.store))
        .collect();
    let mut fields = vec![
        ("kind", string("publish")),
        ("scope", string("parent")),
        ("facts", array_of_strings(facts)),
    ];
    if let Some(theorem) = theorem {
        fields.push(("theorem", string(theorem)));
    }
    object_for(rt, fields)
}

fn goal_wd(goal: &Fact, success: bool, rt: &Runtime) -> JsonValue {
    let mut fields = vec![("fact", string(goal.readable_string()))];
    if let Some(position) = fact_source_line(goal) {
        fields.push(("line", number(position.line)));
    }
    stage("well_defined", success, rt, fields)
}

fn rejected_wd(result: &VerifyFactWellDefinedResult, rt: &Runtime) -> Vec<JsonValue> {
    match result {
        VerifyFactWellDefinedResult::Failed(reason) => {
            let mut step = goal_wd(&reason.fact(), false, rt);
            if let Some(position) = super::source::failed_fact_wd_line(reason) {
                field(&mut step, rt, "line", number(position.line));
            }
            vec![step]
        }
        VerifyFactWellDefinedResult::Success(_) => Vec::new(),
    }
}

fn stage(kind: &str, success: bool, rt: &Runtime, mut fields: Vec<(&str, JsonValue)>) -> JsonValue {
    fields.insert(0, ("kind", string(kind)));
    fields.insert(1, ("result", super::helper::run_result_value(success)));
    object_for(rt, fields)
}

fn field(output: &mut JsonValue, rt: &Runtime, name: &str, value: JsonValue) {
    if let JsonValue::Object(fields) = output {
        fields.insert(
            localize_key(name, rt.launch_command.output_language()),
            value,
        );
    }
}

fn number(value: usize) -> JsonValue {
    JsonValue::Number(value as f64)
}

fn children(source: Option<&RunSource>, line: Option<usize>) -> &[usize] {
    source
        .zip(line)
        .map_or(&[], |(source, line)| source.children(line))
}

fn scoped<'a>(scopes: &[&'a ExecEnv], local: &'a ExecEnv) -> Vec<&'a ExecEnv> {
    let mut result = scopes.to_vec();
    result.push(local);
    result
}
