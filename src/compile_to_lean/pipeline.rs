use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::helper::{
    lean_generic_carrier_name, lean_generic_object_binder, TO_LEAN_IS_FINITE_SET,
    TO_LEAN_IS_NONEMPTY_SET, TO_LEAN_IS_SET, TO_LEAN_OBJECT_CLASS,
};
use super::local_builtin_adapters::{linked_local_builtin_adapter_module, local_builtin_adapter};
use super::rational_expression::{lean_name, LeanRationalExpression};
use super::set_prelude::{lean_object_prelude, lean_standard_set_name};
use super::type_context::LeanTypeContext;
use super::{
    LitexToLeanCompilationPhase, LitexToLeanCompilationReport, LitexToLeanCompilationStatus,
    LitexToLeanUnsupportedStatement,
};
use crate::litex_to_lean_ir::LitexToLeanRegisteredRuleApplicationIr;
#[cfg(test)]
use crate::verify::rule_schema::RuleFingerprint;
use crate::verify::rule_schema::RuleId;

enum LitexToLeanStatementOutcome {
    Ir(LitexToLeanStatementIr),
    Unsupported(String),
}

struct LitexToLeanStatementInput {
    statement_index: usize,
    statement: String,
    line_file: LineFile,
    outcome: LitexToLeanStatementOutcome,
}

pub fn compile_to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let namespace = lean_namespace_for_runtime(runtime);
    compile_to_lean_with_namespace(source_code, runtime, namespace)
}

/// Compiles every supported statement and returns an explicit completeness
/// status. Parsing, execution, and verification errors remain hard failures.
pub fn compile_to_lean_with_report(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<LitexToLeanCompilationReport, RuntimeError> {
    let namespace = lean_namespace_for_runtime(runtime);
    compile_to_lean_with_report_and_namespace(source_code, runtime, namespace)
}

fn compile_to_lean_with_namespace(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<String>,
) -> Result<String, RuntimeError> {
    let previous_mode = runtime.replace_litex_to_lean_ir_mode(true);
    let result = compile_to_lean_in_mode(source_code, runtime, namespace.as_deref());
    runtime.replace_litex_to_lean_ir_mode(previous_mode);
    result
}

fn compile_to_lean_in_mode(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<&str>,
) -> Result<String, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut ir = Vec::new();

    for mut block in blocks {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(litex_to_lean_error(
                &statement.line_file(),
                "Litex-to-Lean received an unverified Litex statement",
            ));
        }
        let Some(statement_ir) = result.litex_to_lean_ir() else {
            return Err(litex_to_lean_error(
                &statement.line_file(),
                "Litex-to-Lean mode completed a statement without producing IR",
            ));
        };
        ir.push(statement_ir.clone());
    }

    if ir.is_empty() {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "Litex-to-Lean requires at least one supported statement",
        ));
    }

    emit_lean_from_litex_to_lean_ir_with_namespace(&ir, namespace)
}

pub fn compile_to_lean_from_source(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    compile_to_lean_with_namespace(&normalized, &mut runtime, None)
}

pub fn compile_to_lean_from_source_with_report(
    source_code: &str,
    entry_label: &str,
) -> Result<LitexToLeanCompilationReport, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    compile_to_lean_with_report_and_namespace(&normalized, &mut runtime, None)
}

/// Pure backend boundary: this function has no Runtime and cannot inspect raw
/// Litex statements or re-run proof search.
pub fn emit_lean_from_litex_to_lean_ir(
    ir: &[LitexToLeanStatementIr],
) -> Result<String, RuntimeError> {
    emit_lean_from_litex_to_lean_ir_with_namespace(ir, None)
}

/// Pure partial backend boundary. Every rejected IR statement is represented
/// in the returned report and as a Lean comment; no axiom or sorry is added.
pub fn emit_lean_from_litex_to_lean_ir_with_report(
    ir: &[LitexToLeanStatementIr],
) -> LitexToLeanCompilationReport {
    let statements = ir
        .iter()
        .enumerate()
        .map(|(index, statement)| LitexToLeanStatementInput {
            statement_index: index + 1,
            statement: statement_ir_display(statement),
            line_file: statement_ir_line_file(statement),
            outcome: LitexToLeanStatementOutcome::Ir(statement.clone()),
        })
        .collect::<Vec<_>>();
    emit_lean_report(statements, None)
}

fn compile_to_lean_with_report_and_namespace(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<String>,
) -> Result<LitexToLeanCompilationReport, RuntimeError> {
    // Eager Litex-to-Lean mode turns IR construction failures into execution errors.
    // Report mode owns that boundary so it can retain the verified statement,
    // record the unsupported IR, and continue with later statements.
    let previous_mode = runtime.replace_litex_to_lean_ir_mode(false);
    let previous_well_definedness_mode = runtime.replace_litex_to_lean_well_definedness_mode(true);
    let result = compile_to_lean_report_in_mode(source_code, runtime, namespace.as_deref());
    runtime.replace_litex_to_lean_well_definedness_mode(previous_well_definedness_mode);
    runtime.replace_litex_to_lean_ir_mode(previous_mode);
    result
}

fn compile_to_lean_report_in_mode(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<&str>,
) -> Result<LitexToLeanCompilationReport, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut statements = Vec::with_capacity(blocks.len());

    for (index, mut block) in blocks.into_iter().enumerate() {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(litex_to_lean_error(
                &statement.line_file(),
                "Litex-to-Lean received an unverified Litex statement",
            ));
        }
        let outcome = match runtime.build_litex_to_lean_ir_statement(&result) {
            Ok(ir) => LitexToLeanStatementOutcome::Ir(ir),
            Err(error) => LitexToLeanStatementOutcome::Unsupported(error.trace_message()),
        };
        statements.push(LitexToLeanStatementInput {
            statement_index: index + 1,
            statement: statement.to_string(),
            line_file: statement.line_file(),
            outcome,
        });
    }

    if statements.is_empty() {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "Litex-to-Lean requires at least one supported statement",
        ));
    }

    Ok(emit_lean_report(statements, namespace))
}

fn emit_lean_report(
    statements: Vec<LitexToLeanStatementInput>,
    namespace: Option<&str>,
) -> LitexToLeanCompilationReport {
    let mut emitter = LeanEmitter::new(namespace.map(str::to_string));
    let mut unsupported = Vec::new();

    for statement in statements {
        let diagnostic = match statement.outcome {
            LitexToLeanStatementOutcome::Unsupported(reason) => {
                Some(LitexToLeanUnsupportedStatement::new(
                    statement.statement_index,
                    statement.statement,
                    &statement.line_file,
                    LitexToLeanCompilationPhase::IrConstruction,
                    reason,
                ))
            }
            LitexToLeanStatementOutcome::Ir(ir) => {
                let checkpoint = emitter.clone();
                match emitter.emit_statement(&ir) {
                    Ok(()) => None,
                    Err(error) => {
                        emitter = checkpoint;
                        Some(LitexToLeanUnsupportedStatement::new(
                            statement.statement_index,
                            statement.statement,
                            &statement.line_file,
                            LitexToLeanCompilationPhase::LeanEmission,
                            error.trace_message(),
                        ))
                    }
                }
            }
        };
        if let Some(diagnostic) = diagnostic {
            emitter.emit_unsupported(&diagnostic);
            unsupported.push(diagnostic);
        }
    }

    let status = if unsupported.is_empty() {
        LitexToLeanCompilationStatus::Complete
    } else {
        LitexToLeanCompilationStatus::Incomplete
    };
    let lean_code = emitter.finish_with_report(status, unsupported.len());
    LitexToLeanCompilationReport::new(lean_code, unsupported)
}

fn emit_lean_from_litex_to_lean_ir_with_namespace(
    ir: &[LitexToLeanStatementIr],
    namespace: Option<&str>,
) -> Result<String, RuntimeError> {
    let mut emitter = LeanEmitter::new(namespace.map(str::to_string));
    for statement in ir {
        emitter.emit_statement(statement)?;
    }
    Ok(emitter.finish())
}

#[derive(Clone)]
struct LeanEmitter {
    namespace: Option<String>,
    declarations: Vec<String>,
    emitted_fact_names: HashMap<FactId, String>,
    emitted_well_defined_fact_names: HashMap<WellDefinedFactId, String>,
    emitted_well_defined_declarations: HashSet<WellDefinedFactId>,
    emitted_declaration_names: HashSet<String>,
    emitted_function_definition_equalities: HashMap<FactId, String>,
    generalized_scoped_well_definedness:
        HashMap<WellDefinedFactId, (String, Vec<(SymbolId, String)>)>,
    next_local_space_id: usize,
    type_context: LeanTypeContext,
    required_local_builtin_rules: HashSet<RuleId>,
}

#[derive(Clone, Default)]
struct LeanProofContext {
    // Litex FactIds remain the lookup keys; emitted local names use independent
    // proof-space coordinates.
    proof_fact_names: HashMap<FactId, String>,
    well_defined_fact_names: HashMap<WellDefinedFactId, String>,
    nonzero_names: Vec<String>,
    local_space_id: Option<usize>,
    next_local_index: usize,
    type_context: LeanTypeContext,
    /// Scoped projections of environment-owned WD facts. They are replayed
    /// only after this forall's parameter and domain binders enter scope.
    scoped_well_definedness: Vec<LitexToLeanWellDefinednessFactIr>,
    /// Source binders that have corresponding Lean term binders in this proof
    /// space. Function-signature-only binders deliberately do not enter here.
    bound_symbol_ids: HashSet<SymbolId>,
}

fn direct_citation_fact_id(proof: &LitexToLeanFactProofIr) -> Option<FactId> {
    match proof {
        LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => Some(*source_fact_id),
        LitexToLeanFactProofIr::Memo { proof } => direct_citation_fact_id(proof),
        LitexToLeanFactProofIr::Composite { steps } if steps.len() == 1 => {
            direct_citation_fact_id(&steps[0].proof)
        }
        _ => None,
    }
}

fn unresolved_comparison_duality(proof: &LitexToLeanFactProofIr) -> Option<(&Fact, &Fact)> {
    match proof {
        LitexToLeanFactProofIr::RuleApplication {
            rule:
                LitexToLeanProofRuleIr::ComparisonNotationDuality {
                    expected_source,
                    expected_target,
                },
            parameter_requirements,
            premises,
        } if parameter_requirements.is_empty() && premises.is_empty() => {
            Some((expected_source, expected_target))
        }
        LitexToLeanFactProofIr::Memo { proof } => unresolved_comparison_duality(proof),
        LitexToLeanFactProofIr::Composite { steps } if steps.len() == 1 => {
            unresolved_comparison_duality(&steps[0].proof)
        }
        _ => None,
    }
}

fn strict_order_not_equal_premises(proof: &LitexToLeanFactProofIr) -> Option<&[LitexToLeanFactIr]> {
    match proof {
        LitexToLeanFactProofIr::RuleApplication {
            rule: LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::NotEqualFromStrictOrder),
            parameter_requirements,
            premises,
        } if parameter_requirements.is_empty() => Some(premises),
        LitexToLeanFactProofIr::Memo { proof } => strict_order_not_equal_premises(proof),
        LitexToLeanFactProofIr::Composite { steps } if steps.len() == 1 => {
            strict_order_not_equal_premises(&steps[0].proof)
        }
        _ => None,
    }
}

fn proof_is_forall_introduction(proof: &LitexToLeanFactProofIr) -> bool {
    match proof {
        LitexToLeanFactProofIr::ForallIntroduction { .. } => true,
        LitexToLeanFactProofIr::Memo { proof } => proof_is_forall_introduction(proof),
        LitexToLeanFactProofIr::Composite { steps } if steps.len() == 1 => {
            proof_is_forall_introduction(&steps[0].proof)
        }
        _ => false,
    }
}

fn well_definedness_certificate_symbol_carriers(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
) -> HashMap<SymbolId, (String, LitexToLeanCarrierIr)> {
    let mut result = HashMap::new();
    for evidence in certificate.facts.iter() {
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &evidence.fact.proposition else {
            continue;
        };
        let (Ok(LitexToLeanObjectIr::Symbol { symbol_id, name }), Ok(set)) = (
            LitexToLeanObjectIr::lower(&membership.element),
            LitexToLeanObjectIr::lower(&membership.set),
        ) else {
            continue;
        };
        result
            .entry(symbol_id)
            .or_insert_with(|| (name, LitexToLeanCarrierIr::for_membership_set(&set)));
    }
    result
}

fn well_definedness_certificate_object_carriers(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
) -> HashMap<String, LitexToLeanCarrierIr> {
    let mut result = HashMap::new();
    for evidence in certificate.facts.iter() {
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &evidence.fact.proposition else {
            continue;
        };
        let Ok(set) = LitexToLeanObjectIr::lower(&membership.set) else {
            continue;
        };
        result
            .entry(obj_equality_key(&membership.element))
            .or_insert_with(|| LitexToLeanCarrierIr::for_membership_set(&set));
    }
    result
}

fn validate_well_definedness_object_contract(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
) -> Result<(), RuntimeError> {
    let facts_by_id = certificate
        .facts
        .iter()
        .map(|evidence| (evidence.certificate_id, &evidence.expected_proposition))
        .collect::<HashMap<_, _>>();
    if facts_by_id.len() != certificate.facts.len() {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "well-definedness environment projection repeats a statement-local fact ID",
        ));
    }
    let facts_by_stable_id = certificate
        .facts
        .iter()
        .map(|evidence| {
            (
                evidence.well_defined_fact_id,
                &evidence.expected_proposition,
            )
        })
        .collect::<HashMap<_, _>>();
    if facts_by_stable_id.len() != certificate.facts.len() {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "well-definedness environment projection repeats a WellDefinedFactId",
        ));
    }
    let mut objects_by_id = HashMap::new();
    let mut objects_by_stable_id = HashMap::new();
    let mut referenced_fact_ids = HashSet::new();
    for object in certificate.objects.iter() {
        if objects_by_id.insert(object.occurrence_id, object).is_some() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness object occurrence IDs are duplicated",
            ));
        }
        if objects_by_stable_id
            .insert(object.well_defined_obj_proof_id, object)
            .is_some()
        {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness environment projection repeats a WellDefinedObjProofId",
            ));
        }
        for certificate_id in object.fact_ids.iter() {
            if !facts_by_id.contains_key(certificate_id) {
                return Err(litex_to_lean_error(
                    &default_line_file(),
                    "well-definedness object occurrence references a missing fact certificate",
                ));
            }
            referenced_fact_ids.insert(*certificate_id);
        }
        if object
            .well_defined_fact_ids
            .iter()
            .any(|fact_id| !facts_by_stable_id.contains_key(fact_id))
        {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness DAG node references a missing WellDefinedFactId",
            ));
        }
        if matches!(object.source_object, Obj::Mod(_))
            && object.intrinsic_result_carrier != Some(LitexToLeanCarrierIr::Integer)
        {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "integer remainder object occurrence lost its intrinsic result carrier",
            ));
        }
    }
    if certificate
        .root_proof_ids
        .iter()
        .any(|proof_id| !objects_by_stable_id.contains_key(proof_id))
    {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "well-definedness statement use references a missing root proof",
        ));
    }
    if certificate
        .root_proof_ids
        .iter()
        .copied()
        .collect::<HashSet<_>>()
        .len()
        != certificate.root_proof_ids.len()
    {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "well-definedness statement use repeats a root proof",
        ));
    }
    for object in certificate.objects.iter() {
        if object
            .child_proof_ids
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != object.child_proof_ids.len()
            || object
                .well_defined_fact_ids
                .iter()
                .copied()
                .collect::<HashSet<_>>()
                .len()
                != object.well_defined_fact_ids.len()
        {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness DAG node repeats a direct child or fact edge",
            ));
        }
        if object
            .child_proof_ids
            .iter()
            .any(|proof_id| !objects_by_stable_id.contains_key(proof_id))
        {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness DAG node references a missing child proof",
            ));
        }
    }
    validate_well_definedness_dag_projection(certificate, &objects_by_stable_id)?;
    if !certificate.objects.is_empty()
        && certificate
            .facts
            .iter()
            .any(|evidence| !referenced_fact_ids.contains(&evidence.certificate_id))
    {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "well-definedness fact certificate is not owned by any checked object occurrence",
        ));
    }
    for requirement in certificate.target_requirements.iter() {
        if requirement.role == WellDefinednessRequirementRole::SourceObjectRequirement {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement has an audit-only role",
            ));
        }
        let Some(expected_proposition) = facts_by_id.get(&requirement.certificate_id) else {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement references a missing fact certificate",
            ));
        };
        let Some(stable_expected_proposition) =
            facts_by_stable_id.get(&requirement.well_defined_fact_id)
        else {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement references a missing WellDefinedFactId",
            ));
        };
        if expected_proposition.to_string() != requirement.expected_proposition.to_string() {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement changed its frozen proposition",
            ));
        }
        if stable_expected_proposition.to_string() != requirement.expected_proposition.to_string() {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement changed its stable fact proposition",
            ));
        }
        let Some(object) = objects_by_id.get(&requirement.object_occurrence_id) else {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement references a missing object occurrence",
            ));
        };
        if obj_equality_key(&object.source_object) != obj_equality_key(&requirement.source_object)
            || object.well_defined_obj_proof_id != requirement.well_defined_obj_proof_id
            || !object
                .well_defined_fact_ids
                .contains(&requirement.well_defined_fact_id)
            || !object.fact_ids.contains(&requirement.certificate_id)
            || !matches!(requirement.source_object, Obj::FnObj(_))
        {
            return Err(litex_to_lean_error(
                &requirement.expected_proposition.line_file(),
                "target well-definedness requirement does not belong to its function application occurrence",
            ));
        }
    }
    Ok(())
}

fn validate_well_definedness_dag_projection(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
    objects: &HashMap<WellDefinedObjProofId, &LitexToLeanWellDefinednessObjectIr>,
) -> Result<(), RuntimeError> {
    let certificate_ids = certificate
        .facts
        .iter()
        .map(|fact| (fact.well_defined_fact_id, fact.certificate_id))
        .collect::<HashMap<_, _>>();
    let mut visiting = HashSet::new();
    let mut reachable = HashSet::new();
    let mut transitive_fact_ids = HashMap::new();

    fn visit(
        proof_id: WellDefinedObjProofId,
        objects: &HashMap<WellDefinedObjProofId, &LitexToLeanWellDefinednessObjectIr>,
        certificate_ids: &HashMap<WellDefinedFactId, WellDefinednessCertificateId>,
        visiting: &mut HashSet<WellDefinedObjProofId>,
        reachable: &mut HashSet<WellDefinedObjProofId>,
        transitive_fact_ids: &mut HashMap<WellDefinedObjProofId, Vec<WellDefinedFactId>>,
    ) -> Result<Vec<WellDefinedFactId>, RuntimeError> {
        reachable.insert(proof_id);
        if let Some(known) = transitive_fact_ids.get(&proof_id) {
            return Ok(known.clone());
        }
        if !visiting.insert(proof_id) {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness object proof graph contains a cycle",
            ));
        }
        let object = objects.get(&proof_id).ok_or_else(|| {
            litex_to_lean_error(
                &default_line_file(),
                "well-definedness DAG traversal reached a missing object proof",
            )
        })?;
        let mut facts = object.well_defined_fact_ids.clone();
        for child_id in object.child_proof_ids.iter().copied() {
            for fact_id in visit(
                child_id,
                objects,
                certificate_ids,
                visiting,
                reachable,
                transitive_fact_ids,
            )? {
                if !facts.contains(&fact_id) {
                    facts.push(fact_id);
                }
            }
        }
        visiting.remove(&proof_id);
        facts.sort_by_key(|fact_id| fact_id.value());
        let projected_ids = facts
            .iter()
            .map(|fact_id| {
                certificate_ids.get(fact_id).copied().ok_or_else(|| {
                    litex_to_lean_error(
                        &default_line_file(),
                        "well-definedness DAG projection references a missing stable fact",
                    )
                })
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        if projected_ids != object.fact_ids {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "well-definedness stable DAG edges disagree with the statement-local fact projection",
            ));
        }
        transitive_fact_ids.insert(proof_id, facts.clone());
        Ok(facts)
    }

    for root_id in certificate.root_proof_ids.iter().copied() {
        visit(
            root_id,
            objects,
            &certificate_ids,
            &mut visiting,
            &mut reachable,
            &mut transitive_fact_ids,
        )?;
    }
    if reachable.len() != objects.len() {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "well-definedness environment projection contains an object proof unreachable from its statement roots",
        ));
    }
    Ok(())
}

/// Source checks beneath an object-owned binder cannot be replayed as global
/// Lean theorems: their free-looking symbols denote the SetBuilder/FnSet/
/// anonymous-function parameters that only exist inside the emitted term.
///
/// Object occurrences retain the exact verifier certificate IDs observed
/// while their constructor was active, including child occurrences.  Use that
/// ownership record rather than attempting to rediscover binders from the
/// printed proposition.
fn binder_owned_well_definedness_fact_ids(
    certificate: &LitexToLeanWellDefinednessCertificateIr,
) -> HashSet<WellDefinednessCertificateId> {
    certificate
        .objects
        .iter()
        .filter(|object| {
            matches!(
                object.source_object,
                Obj::SetBuilder(_) | Obj::FnSet(_) | Obj::AnonymousFn(_)
            ) || !object
                .source_object
                .collect_param_obj_names(ParamObjType::SetBuilder)
                .is_empty()
                || !object
                    .source_object
                    .collect_param_obj_names(ParamObjType::FnSet)
                    .is_empty()
                || !object
                    .source_object
                    .collect_param_obj_names(ParamObjType::Forall)
                    .is_empty()
        })
        .flat_map(|object| object.fact_ids.iter().copied())
        .collect()
}

fn collect_obj_ir_symbols(object: &LitexToLeanObjectIr, symbols: &mut Vec<(SymbolId, String)>) {
    match object {
        LitexToLeanObjectIr::Symbol { symbol_id, name } => symbols.push((*symbol_id, name.clone())),
        LitexToLeanObjectIr::BuiltinApp { arguments, .. } => {
            for argument in arguments {
                collect_obj_ir_symbols(argument, symbols);
            }
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            collect_obj_ir_symbols(&application.head, symbols);
            for layer in application.argument_layers.iter() {
                for argument in layer {
                    collect_obj_ir_symbols(argument, symbols);
                }
            }
        }
        LitexToLeanObjectIr::Collection { items, .. } => {
            for item in items {
                collect_obj_ir_symbols(item, symbols);
            }
        }
        LitexToLeanObjectIr::FunctionSet { function } => {
            for parameter in function.parameters.iter() {
                collect_obj_ir_symbols(&parameter.set, symbols);
            }
            collect_obj_ir_symbols(&function.return_set, symbols);
        }
        LitexToLeanObjectIr::SetBuilder(builder) => {
            collect_obj_ir_symbols(&builder.set, symbols);
            for fact in builder.facts.iter() {
                if let Ok(mut local_symbols) = fact_ir_symbols(fact) {
                    local_symbols.retain(|(symbol_id, _)| *symbol_id != builder.symbol_id);
                    symbols.extend(local_symbols);
                }
            }
        }
        LitexToLeanObjectIr::AnonymousFunction(function) => {
            let bound_ids = function
                .function
                .parameters
                .iter()
                .map(|parameter| parameter.symbol_id)
                .collect::<HashSet<_>>();
            for parameter in function.function.parameters.iter() {
                let mut local_symbols = Vec::new();
                collect_obj_ir_symbols(&parameter.set, &mut local_symbols);
                local_symbols.retain(|(symbol_id, _)| !bound_ids.contains(symbol_id));
                symbols.extend(local_symbols);
            }
            let mut local_symbols = Vec::new();
            collect_obj_ir_symbols(&function.function.return_set, &mut local_symbols);
            collect_obj_ir_symbols(&function.body, &mut local_symbols);
            local_symbols.retain(|(symbol_id, _)| !bound_ids.contains(symbol_id));
            symbols.extend(local_symbols);
        }
        LitexToLeanObjectIr::Number { .. }
        | LitexToLeanObjectIr::Constant(_)
        | LitexToLeanObjectIr::StandardSet(_) => {}
    }
}

fn fact_ir_symbols(fact: &Fact) -> Result<Vec<(SymbolId, String)>, RuntimeError> {
    let mut objects = Vec::new();
    collect_fact_objects_for_lean_name_check(fact, &mut objects);
    let mut symbols = Vec::new();
    for object in objects {
        let object = LitexToLeanObjectIr::lower(object)
            .map_err(|message| litex_to_lean_error(&fact.line_file(), message))?;
        collect_obj_ir_symbols(&object, &mut symbols);
    }
    symbols.sort_by_key(|(symbol_id, _)| *symbol_id);
    symbols.dedup_by_key(|(symbol_id, _)| *symbol_id);
    Ok(symbols)
}

impl LeanProofContext {
    fn new_proof_space(&self) -> Self {
        LeanProofContext {
            proof_fact_names: self.proof_fact_names.clone(),
            well_defined_fact_names: self.well_defined_fact_names.clone(),
            nonzero_names: self.nonzero_names.clone(),
            local_space_id: None,
            next_local_index: 0,
            type_context: self.type_context.clone(),
            scoped_well_definedness: self.scoped_well_definedness.clone(),
            bound_symbol_ids: self.bound_symbol_ids.clone(),
        }
    }
}

impl LeanEmitter {
    fn new(namespace: Option<String>) -> Self {
        LeanEmitter {
            namespace,
            declarations: Vec::new(),
            emitted_fact_names: HashMap::new(),
            emitted_well_defined_fact_names: HashMap::new(),
            emitted_well_defined_declarations: HashSet::new(),
            emitted_declaration_names: HashSet::from([
                TO_LEAN_OBJECT_CLASS.to_string(),
                TO_LEAN_IS_SET.to_string(),
                TO_LEAN_IS_NONEMPTY_SET.to_string(),
                TO_LEAN_IS_FINITE_SET.to_string(),
            ]),
            emitted_function_definition_equalities: HashMap::new(),
            generalized_scoped_well_definedness: HashMap::new(),
            next_local_space_id: 1,
            type_context: LeanTypeContext::default(),
            required_local_builtin_rules: HashSet::new(),
        }
    }

    fn root_proof_context(&self) -> LeanProofContext {
        LeanProofContext {
            well_defined_fact_names: self.emitted_well_defined_fact_names.clone(),
            type_context: self.type_context.clone(),
            ..LeanProofContext::default()
        }
    }

    fn finish(self) -> String {
        self.finish_with_status_comment(None)
    }

    fn finish_with_report(
        self,
        status: LitexToLeanCompilationStatus,
        unsupported_count: usize,
    ) -> String {
        let status_comment = match status {
            LitexToLeanCompilationStatus::Complete => {
                "-- Litex-to-Lean status: complete".to_string()
            }
            LitexToLeanCompilationStatus::Incomplete => format!(
                "-- Litex-to-Lean status: incomplete\n-- Omitted statements: {}",
                unsupported_count
            ),
        };
        self.finish_with_status_comment(Some(status_comment))
    }

    fn finish_with_status_comment(self, status_comment: Option<String>) -> String {
        let adapter_module =
            linked_local_builtin_adapter_module(&self.required_local_builtin_rules)
                .expect("registered local builtin adapters were validated during emission");
        let adapter_module = if adapter_module.is_empty() {
            String::new()
        } else {
            format!("{}\n\n", adapter_module)
        };
        let status_comment = status_comment
            .map(|comment| format!("{}\n\n", comment))
            .unwrap_or_default();
        let body = format!(
            "{}noncomputable section\n\n{}\n\n{}",
            status_comment,
            lean_object_prelude(),
            self.declarations.join("\n\n")
        );
        match self.namespace {
            Some(namespace) => format!(
                "import Mathlib\n\n{}namespace {}\n\n{}\n\nend\n\nend {}\n",
                adapter_module, namespace, body, namespace
            ),
            None => format!("import Mathlib\n\n{}{}\n\nend\n", adapter_module, body),
        }
    }

    fn emit_unsupported(&mut self, diagnostic: &LitexToLeanUnsupportedStatement) {
        self.declarations.push(format!(
            "-- Litex-to-Lean omitted statement {} during {} at {}:{}.\n-- Statement: {}\n-- Reason: {}",
            diagnostic.statement_index,
            diagnostic.phase.label(),
            lean_comment_text(&diagnostic.source_path),
            diagnostic.line,
            lean_comment_text(&diagnostic.statement),
            lean_comment_text(&diagnostic.reason),
        ));
    }

    fn emit_statement(&mut self, statement: &LitexToLeanStatementIr) -> Result<(), RuntimeError> {
        match statement {
            LitexToLeanStatementIr::AbstractProp(ir) => {
                self.reserve_declaration_name(&lean_name(&ir.name), &default_line_file())?;
                self.declarations.push(lean_abstract_prop(ir));
                Ok(())
            }
            LitexToLeanStatementIr::Prop(ir) => {
                let line_file = ir
                    .iff_facts
                    .first()
                    .map(Fact::line_file)
                    .unwrap_or_else(default_line_file);
                self.reserve_declaration_name(&lean_name(&ir.name), &line_file)?;
                self.declarations.push(lean_prop(ir)?);
                Ok(())
            }
            LitexToLeanStatementIr::HaveObjChoice(ir) => self.emit_object_choices(ir),
            LitexToLeanStatementIr::HaveExistentialWitness(ir) => {
                self.emit_existential_witnesses(ir)
            }
            LitexToLeanStatementIr::HaveFnEqual(ir) => self.emit_function_definition(ir),
            LitexToLeanStatementIr::HaveObjEqual(ir) => {
                for definition in ir.definitions.iter() {
                    let line_file = ir
                        .facts
                        .first()
                        .map(|fact| fact.proposition.line_file())
                        .unwrap_or_else(default_line_file);
                    self.reserve_declaration_name(&lean_name(&definition.name), &line_file)?;
                    let lean_type = lean_ir_param_type(&definition.param_type, &self.type_context)?;
                    let expected = param_type_object_carrier(&definition.param_type)?;
                    self.declarations.push(format!(
                        "def {} : {} := {}",
                        lean_name(&definition.name),
                        lean_type,
                        lean_obj_ir_with_expected(
                            &definition.value,
                            &expected,
                            &self.type_context,
                            false,
                        )?
                    ));
                    self.type_context
                        .insert_param(definition.symbol_id, &definition.param_type);
                }
                for fact in ir.facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            LitexToLeanStatementIr::NamedTheorem(ir) => {
                let previous = self
                    .type_context
                    .replace_well_definedness_context(Default::default());
                let result = self.emit_named_theorem(ir);
                self.type_context.replace_well_definedness_context(previous);
                result
            }
            LitexToLeanStatementIr::Proof(ir) => {
                for fact in ir.facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            LitexToLeanStatementIr::Trust(ir) => {
                for fact in ir.facts.iter() {
                    self.emit_trusted_fact(fact)?;
                }
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            LitexToLeanStatementIr::Fact(ir) => {
                let previous = self
                    .type_context
                    .replace_well_definedness_context(Default::default());
                let result = self.emit_fact_statement_with_well_definedness(ir);
                self.type_context.replace_well_definedness_context(previous);
                result
            }
            LitexToLeanStatementIr::ProjectedForall(ir) => {
                let previous = self
                    .type_context
                    .replace_well_definedness_context(Default::default());
                let result = self.emit_projected_forall_with_well_definedness(ir);
                self.type_context.replace_well_definedness_context(previous);
                result
            }
        }
    }

    fn emit_named_theorem(&mut self, ir: &LitexToLeanNamedTheoremIr) -> Result<(), RuntimeError> {
        validate_named_theorem_ir(ir)?;
        let line_file = ir.theorem.proposition.line_file();
        let theorem_name = lean_name(&ir.name);
        self.reserve_declaration_name(&theorem_name, &line_file)?;
        if let Some(fact_id) = ir.theorem.fact_id {
            if self.emitted_fact_names.contains_key(&fact_id) {
                return Err(litex_to_lean_error(
                    &line_file,
                    "named theorem primary FactId was emitted before its declaration",
                ));
            }
        }
        self.emit_scoped_certificate_type_witnesses(&ir.well_definedness, &ir.theorem.proposition)?;
        let mut proof_context = self.root_proof_context();
        proof_context.scoped_well_definedness = ir.well_definedness.facts.clone();
        apply_fact_proof_type_hints(&ir.theorem, &mut proof_context.type_context)?;
        let LitexToLeanFactProofIr::ForallIntroduction {
            parameter_premises,
            premises,
            inferred_premises,
            conclusions,
        } = &ir.theorem.proof
        else {
            return Err(litex_to_lean_error(
                &line_file,
                "named theorem does not retain a direct forall-introduction proof",
            ));
        };
        let mut current_context = proof_context.new_proof_space();
        let proof_steps = ir
            .proof_steps
            .iter()
            .map(|step| step.statement.clone())
            .collect::<Vec<_>>();
        let proof = self.lean_forall_introduction_with_steps(
            &ir.theorem.proposition,
            parameter_premises,
            premises,
            inferred_premises,
            &proof_steps,
            conclusions,
            &mut current_context,
        )?;
        let proposition =
            lean_fact_with_context(&ir.theorem.proposition, &proof_context.type_context)?;
        if let Some(fact_id) = ir.theorem.fact_id {
            self.emitted_fact_names
                .insert(fact_id, theorem_name.clone());
        }
        self.declarations.push(format!(
            "-- Litex theorem `{}`\ntheorem {} : {} := {}",
            lean_comment_text(&ir.name),
            theorem_name,
            proposition,
            proof
        ));

        for projection in ir.stored_projections.iter() {
            self.emit_proved_fact_with_scoped_well_definedness(projection, &ir.well_definedness)?;
        }
        for fact in ir.inferred_facts.iter() {
            self.emit_proved_fact(fact)?;
        }
        Ok(())
    }

    fn reserve_declaration_name(
        &mut self,
        name: &str,
        line_file: &LineFile,
    ) -> Result<(), RuntimeError> {
        if self.emitted_declaration_names.insert(name.to_string()) {
            return Ok(());
        }
        Err(litex_to_lean_error(
            line_file,
            format!("Lean declaration name `{name}` is already reserved"),
        ))
    }

    fn well_definedness_helper_name(
        &mut self,
        fact_id: WellDefinedFactId,
        line_file: &LineFile,
    ) -> Result<String, RuntimeError> {
        let name = format!("well_defined_fact_{}", fact_id.value());
        self.reserve_declaration_name(&name, line_file)?;
        self.emitted_well_defined_declarations.insert(fact_id);
        Ok(name)
    }

    fn emit_fact_statement_with_well_definedness(
        &mut self,
        ir: &LitexToLeanFactStatementIr,
    ) -> Result<(), RuntimeError> {
        if proof_is_forall_introduction(&ir.fact.proof) {
            self.emit_proved_fact_with_scoped_well_definedness(&ir.fact, &ir.well_definedness)?;
        } else {
            self.emit_global_well_definedness_certificate(&ir.well_definedness)?;
            self.emit_proved_fact(&ir.fact)?;
        }
        for fact in ir.inferred_facts.iter() {
            self.emit_proved_fact(fact)?;
        }
        Ok(())
    }

    fn emit_projected_forall_with_well_definedness(
        &mut self,
        ir: &LitexToLeanProjectedForallIr,
    ) -> Result<(), RuntimeError> {
        validate_projected_forall_ir(ir)?;
        for fact in ir.facts.iter() {
            self.emit_proved_fact_with_scoped_well_definedness(fact, &ir.well_definedness)?;
        }
        for fact in ir.inferred_facts.iter() {
            self.emit_proved_fact(fact)?;
        }
        Ok(())
    }

    fn emit_global_well_definedness_certificate(
        &mut self,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<(), RuntimeError> {
        validate_well_definedness_object_contract(certificate)?;
        self.type_context
            .install_well_definedness_certificate_metadata(certificate);
        let binder_owned_fact_ids = binder_owned_well_definedness_fact_ids(certificate);
        let mut seen_ids = HashSet::new();
        let certificate_symbol_carriers = well_definedness_certificate_symbol_carriers(certificate);
        let certificate_object_carriers = well_definedness_certificate_object_carriers(certificate);
        for (index, evidence) in certificate.facts.iter().enumerate() {
            if !seen_ids.insert(evidence.certificate_id) {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "well-definedness certificate repeats a statement-local ID",
                ));
            }
            if evidence.certificate_id.value() != index as u64 + 1 {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "well-definedness certificate IDs are missing or out of verifier order",
                ));
            }
            if evidence.expected_proposition.to_string() != evidence.fact.proposition.to_string() {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "well-definedness certificate proof proposition does not match its frozen verifier target",
                ));
            }
            if evidence.role != WellDefinednessRequirementRole::SourceObjectRequirement {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "well-definedness certificate has an unsupported requirement role",
                ));
            }
            if matches!(evidence.fact.proof, LitexToLeanFactProofIr::Trusted) {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "well-definedness certificate cannot introduce trusted evidence",
                ));
            }
            if let Some(name) = self
                .emitted_well_defined_fact_names
                .get(&evidence.well_defined_fact_id)
                .cloned()
            {
                self.type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        name,
                    );
                continue;
            }
            if self
                .emitted_well_defined_declarations
                .contains(&evidence.well_defined_fact_id)
            {
                continue;
            }
            if binder_owned_fact_ids.contains(&evidence.certificate_id) {
                // The exact certificate metadata remains installed above.  A
                // proof argument consumed by a nested application is linked
                // when its owning function/set binder enters Lean scope.
                continue;
            }
            if let Some(fact_id) = evidence.fact.fact_id {
                if let Some(name) = self.emitted_fact_names.get(&fact_id) {
                    self.emitted_well_defined_fact_names
                        .insert(evidence.well_defined_fact_id, name.clone());
                    self.type_context
                        .insert_well_definedness_proof_by_certificate_id(
                            evidence.certificate_id,
                            &evidence.fact.proposition,
                            name.clone(),
                        );
                }
                // A not-yet-emitted FactId belongs to the statement's local
                // verifier scope. Its proposition is already replayed by the
                // corresponding Lean binder; using it in a target term needs
                // the scoped-binder backend rather than a global helper.
                continue;
            }
            if let Some(source_fact_id) = direct_citation_fact_id(&evidence.fact.proof) {
                if let Some(name) = self.emitted_fact_names.get(&source_fact_id) {
                    self.emitted_well_defined_fact_names
                        .insert(evidence.well_defined_fact_id, name.clone());
                    self.type_context
                        .insert_well_definedness_proof_by_certificate_id(
                            evidence.certificate_id,
                            &evidence.fact.proposition,
                            name.clone(),
                        );
                }
                // A direct citation to a not-yet-emitted fact is a local
                // binder assumption, not a newly proved WD obligation. The
                // corresponding source binder is represented by the native
                // function/forall type. If an application consumes it, the
                // lookup below still fails until the scoped-name backend has
                // installed that exact FactId.
                continue;
            }
            if let Some((proposition, proof, is_closed)) = self
                .lean_standard_membership_well_definedness(evidence, &certificate_symbol_carriers)?
            {
                let helper_name = self.well_definedness_helper_name(
                    evidence.well_defined_fact_id,
                    &evidence.fact.proposition.line_file(),
                )?;
                self.declarations.push(format!(
                    "-- Litex well-definedness certificate {}\ntheorem {} : {} := {}",
                    evidence.certificate_id.value(),
                    helper_name,
                    proposition,
                    proof
                ));
                if is_closed {
                    self.emitted_well_defined_fact_names
                        .insert(evidence.well_defined_fact_id, helper_name.clone());
                    self.type_context
                        .insert_well_definedness_proof_by_certificate_id(
                            evidence.certificate_id,
                            &evidence.fact.proposition,
                            helper_name,
                        );
                }
                continue;
            }
            if let Some((proposition, proof)) =
                self.lean_closed_numeric_well_definedness(evidence, &certificate_object_carriers)?
            {
                let helper_name = self.well_definedness_helper_name(
                    evidence.well_defined_fact_id,
                    &evidence.fact.proposition.line_file(),
                )?;
                self.declarations.push(format!(
                    "-- Litex well-definedness certificate {}\ntheorem {} : {} := {}",
                    evidence.certificate_id.value(),
                    helper_name,
                    proposition,
                    proof
                ));
                self.type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        helper_name,
                    );
                self.emitted_well_defined_fact_names.insert(
                    evidence.well_defined_fact_id,
                    format!(
                        "well_defined_fact_{}",
                        evidence.well_defined_fact_id.value()
                    ),
                );
                continue;
            }
            if let Some((proposition, proof)) = self.lean_generalized_comparison_well_definedness(
                evidence,
                &certificate_symbol_carriers,
            )? {
                let helper_name = self.well_definedness_helper_name(
                    evidence.well_defined_fact_id,
                    &evidence.fact.proposition.line_file(),
                )?;
                self.declarations.push(format!(
                    "-- Litex well-definedness certificate {} (generalized local premise)\ntheorem {} : {} := {}",
                    evidence.certificate_id.value(),
                    helper_name,
                    proposition,
                    proof
                ));
                continue;
            }
            if let Some((proposition, proof)) = self
                .lean_generalized_strict_order_not_equal_well_definedness(
                    evidence,
                    &certificate_symbol_carriers,
                )?
            {
                let helper_name = self.well_definedness_helper_name(
                    evidence.well_defined_fact_id,
                    &evidence.fact.proposition.line_file(),
                )?;
                self.declarations.push(format!(
                    "-- Litex well-definedness certificate {} (generalized strict-order premise)\ntheorem {} : {} := {}",
                    evidence.certificate_id.value(),
                    helper_name,
                    proposition,
                    proof
                ));
                continue;
            }
            let mut proof_context = self.root_proof_context();
            apply_fact_proof_type_hints(&evidence.fact, &mut proof_context.type_context)?;
            let proof = self
                .lean_proof(
                    &evidence.fact.proposition,
                    &evidence.fact.proof,
                    &proof_context,
                )
                .map_err(|error| {
                    litex_to_lean_error(
                        &evidence.fact.proposition.line_file(),
                        format!(
                            "cannot replay well-definedness certificate {} for `{}` in global scope: {}",
                            evidence.certificate_id.value(),
                            evidence.fact.proposition,
                            error.trace_message()
                        ),
                    )
                })?;
            let helper_name = self.well_definedness_helper_name(
                evidence.well_defined_fact_id,
                &evidence.fact.proposition.line_file(),
            )?;
            self.declarations.push(format!(
                "-- Litex well-definedness certificate {}\ntheorem {} : {} := {}",
                evidence.certificate_id.value(),
                helper_name,
                lean_fact_with_context(&evidence.fact.proposition, &proof_context.type_context,)?,
                proof
            ));
            self.type_context
                .insert_well_definedness_proof_by_certificate_id(
                    evidence.certificate_id,
                    &evidence.fact.proposition,
                    helper_name,
                );
            self.emitted_well_defined_fact_names.insert(
                evidence.well_defined_fact_id,
                format!(
                    "well_defined_fact_{}",
                    evidence.well_defined_fact_id.value()
                ),
            );
        }
        Ok(())
    }

    /// A forall proposition can contain a dependent function application in
    /// its *type*.  Proofs supplied by the forall's own parameter/domain
    /// binders are installed by `lean_forall_fact_with_context`, but a closed
    /// application such as `f(2)` needs its checked `2 > 0` proof before the
    /// theorem body exists. Emit only those globally scoped certificate facts
    /// here; the complete certificate is still replayed, in verifier order,
    /// after the forall binders have entered scope.
    fn emit_scoped_certificate_type_witnesses(
        &mut self,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
        proposition: &Fact,
    ) -> Result<(), RuntimeError> {
        validate_well_definedness_object_contract(certificate)?;
        self.type_context
            .install_well_definedness_certificate_metadata(certificate);
        let forall_bound_symbol_ids = match proposition {
            Fact::ForallFact(forall) => forall
                .params_def_with_type
                .groups
                .iter()
                .flat_map(|group| group.params.iter().map(SymbolBinding::id))
                .collect::<HashSet<_>>(),
            _ => HashSet::new(),
        };
        let certificate_symbol_carriers = well_definedness_certificate_symbol_carriers(certificate);
        let certificate_object_carriers = well_definedness_certificate_object_carriers(certificate);
        for evidence in certificate.facts.iter() {
            if evidence.expected_proposition.to_string() != evidence.fact.proposition.to_string()
                || evidence.role != WellDefinednessRequirementRole::SourceObjectRequirement
                || matches!(evidence.fact.proof, LitexToLeanFactProofIr::Trusted)
            {
                // The full scoped replay reports the more specific malformed
                // certificate error before any Lean text can be returned.
                continue;
            }
            if let Some(name) = self
                .emitted_well_defined_fact_names
                .get(&evidence.well_defined_fact_id)
                .cloned()
            {
                self.type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        name,
                    );
                continue;
            }
            if self
                .emitted_well_defined_declarations
                .contains(&evidence.well_defined_fact_id)
            {
                continue;
            }
            if self
                .type_context
                .well_definedness_proof(&evidence.fact.proposition)
                .is_some()
            {
                continue;
            }
            if fact_ir_symbols(&evidence.fact.proposition)?
                .iter()
                .any(|(symbol_id, _)| forall_bound_symbol_ids.contains(symbol_id))
            {
                // The theorem type renderer and proof introduction install
                // these binders with their actual declared carriers. Trying
                // to generalize them from a single intermediate membership
                // can choose a later coercion carrier instead.
                continue;
            }
            if let Some(fact_id) = evidence.fact.fact_id {
                if let Some(name) = self.emitted_fact_names.get(&fact_id) {
                    self.emitted_well_defined_fact_names
                        .insert(evidence.well_defined_fact_id, name.clone());
                    self.type_context
                        .insert_well_definedness_proof_by_certificate_id(
                            evidence.certificate_id,
                            &evidence.fact.proposition,
                            name.clone(),
                        );
                    continue;
                }
            }
            if let Some(source_fact_id) = direct_citation_fact_id(&evidence.fact.proof) {
                if let Some(name) = self.emitted_fact_names.get(&source_fact_id) {
                    self.emitted_well_defined_fact_names
                        .insert(evidence.well_defined_fact_id, name.clone());
                    self.type_context
                        .insert_well_definedness_proof_by_certificate_id(
                            evidence.certificate_id,
                            &evidence.fact.proposition,
                            name.clone(),
                        );
                    continue;
                }
            }

            let standard_witness = self.lean_standard_membership_well_definedness(
                evidence,
                &certificate_symbol_carriers,
            )?;
            let (proposition, proof, is_closed) =
                if let Some((proposition, proof, is_closed)) = standard_witness {
                    (proposition, proof, is_closed)
                } else if let Some((proposition, proof)) = self
                    .lean_closed_numeric_well_definedness(evidence, &certificate_object_carriers)?
                {
                    (proposition, proof, true)
                } else {
                    continue;
                };
            let helper_name = self.well_definedness_helper_name(
                evidence.well_defined_fact_id,
                &evidence.fact.proposition.line_file(),
            )?;
            self.declarations.push(format!(
                "-- Litex well-definedness certificate {} (forall type witness)\ntheorem {} : {} := {}",
                evidence.certificate_id.value(),
                helper_name,
                proposition,
                proof
            ));
            if is_closed {
                self.emitted_well_defined_fact_names
                    .insert(evidence.well_defined_fact_id, helper_name.clone());
                self.type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        helper_name,
                    );
            } else {
                let Fact::AtomicFact(AtomicFact::InFact(membership)) = &evidence.fact.proposition
                else {
                    return Err(litex_to_lean_error(
                        &evidence.fact.proposition.line_file(),
                        "generalized scoped well-definedness helper is not a membership fact",
                    ));
                };
                let element = LitexToLeanObjectIr::lower(&membership.element)
                    .map_err(|message| litex_to_lean_error(&membership.line_file, message))?;
                let mut helper_binders = Vec::new();
                collect_obj_ir_symbols(&element, &mut helper_binders);
                helper_binders.sort_by_key(|(symbol_id, _)| *symbol_id);
                helper_binders.dedup_by_key(|(symbol_id, _)| *symbol_id);
                helper_binders.retain(|(symbol_id, _)| {
                    self.type_context.symbol_carrier(*symbol_id).is_none()
                });
                self.generalized_scoped_well_definedness
                    .insert(evidence.well_defined_fact_id, (helper_name, helper_binders));
            }
        }
        Ok(())
    }

    fn lean_standard_membership_well_definedness(
        &self,
        evidence: &LitexToLeanWellDefinednessFactIr,
        certificate_symbol_carriers: &HashMap<SymbolId, (String, LitexToLeanCarrierIr)>,
    ) -> Result<Option<(String, String, bool)>, RuntimeError> {
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &evidence.fact.proposition else {
            return Ok(None);
        };
        let Obj::StandardSet(set) = &membership.set else {
            return Ok(None);
        };
        if !matches!(
            set,
            StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C
        ) {
            return Ok(None);
        }

        let element = LitexToLeanObjectIr::lower(&membership.element)
            .map_err(|message| litex_to_lean_error(&membership.line_file, message))?;
        let mut symbols = Vec::new();
        collect_obj_ir_symbols(&element, &mut symbols);
        symbols.sort_by_key(|(symbol_id, _)| *symbol_id);
        symbols.dedup_by_key(|(symbol_id, _)| *symbol_id);

        let mut type_context = self.type_context.clone();
        let mut binders = Vec::new();
        for (symbol_id, occurrence_name) in symbols {
            if type_context.symbol_carrier(symbol_id).is_some() {
                continue;
            }
            let Some((source_name, carrier)) = certificate_symbol_carriers.get(&symbol_id) else {
                return Err(litex_to_lean_error(
                    &membership.line_file,
                    format!(
                        "well-definedness certificate {} uses unscoped symbol `{}`",
                        evidence.certificate_id.value(),
                        occurrence_name
                    ),
                ));
            };
            type_context.insert(symbol_id, carrier.clone());
            binders.push((lean_name(source_name), carrier.clone()));
        }

        let mut proposition = lean_fact_with_context(&evidence.fact.proposition, &type_context)?;
        for (name, carrier) in binders.iter().rev() {
            proposition = format!(
                "∀ ({} : {}), {}",
                name,
                type_context
                    .lean_type(carrier)
                    .map_err(|message| litex_to_lean_error(&membership.line_file, message))?,
                proposition
            );
        }
        let mut proof = vec!["by".to_string()];
        if !binders.is_empty() {
            proof.push(format!(
                "  intro {}",
                binders
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>()
                    .join(" ")
            ));
        }
        proof.push("  change True".to_string());
        proof.push("  trivial".to_string());
        Ok(Some((proposition, proof.join("\n"), binders.is_empty())))
    }

    fn lean_closed_numeric_well_definedness(
        &self,
        evidence: &LitexToLeanWellDefinednessFactIr,
        object_carriers: &HashMap<String, LitexToLeanCarrierIr>,
    ) -> Result<Option<(String, String)>, RuntimeError> {
        let Fact::AtomicFact(atomic) = &evidence.fact.proposition else {
            return Ok(None);
        };
        if !matches!(
            atomic,
            AtomicFact::EqualFact(_)
                | AtomicFact::NotEqualFact(_)
                | AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
        ) {
            return Ok(None);
        }
        let arguments = atomic.args_ref();
        if arguments.is_empty()
            || !arguments
                .iter()
                .all(|argument| closed_rational_expression(argument))
        {
            return Ok(None);
        }
        let carrier = arguments
            .iter()
            .find_map(|argument| object_carriers.get(&obj_equality_key(argument)).cloned());
        let Some(carrier) = carrier else {
            return Ok(None);
        };
        if !matches!(
            carrier,
            LitexToLeanCarrierIr::Natural
                | LitexToLeanCarrierIr::Integer
                | LitexToLeanCarrierIr::Rational
                | LitexToLeanCarrierIr::Real
                | LitexToLeanCarrierIr::Complex
        ) {
            return Ok(None);
        }
        let mut type_context = self.type_context.clone();
        for argument in arguments {
            type_context.expect_object(argument, carrier.clone());
        }
        Ok(Some((
            lean_fact_with_context(&evidence.fact.proposition, &type_context)?,
            "by\n  norm_num".to_string(),
        )))
    }

    fn lean_generalized_comparison_well_definedness(
        &self,
        evidence: &LitexToLeanWellDefinednessFactIr,
        certificate_symbol_carriers: &HashMap<SymbolId, (String, LitexToLeanCarrierIr)>,
    ) -> Result<Option<(String, String)>, RuntimeError> {
        let Some((source, target)) = unresolved_comparison_duality(&evidence.fact.proof) else {
            return Ok(None);
        };
        if target.to_string() != evidence.fact.proposition.to_string()
            || !crate::litex_to_lean_ir::facts_are_comparison_notation_duals(source, target)
        {
            return Err(litex_to_lean_error(
                &evidence.fact.proposition.line_file(),
                "generalized comparison WD evidence does not match its retained target",
            ));
        }

        let mut symbols = fact_ir_symbols(source)?;
        symbols.extend(fact_ir_symbols(target)?);
        symbols.sort_by_key(|(symbol_id, _)| *symbol_id);
        symbols.dedup_by_key(|(symbol_id, _)| *symbol_id);
        symbols.retain(|(symbol_id, _)| self.type_context.symbol_carrier(*symbol_id).is_none());
        if symbols.is_empty() {
            return Err(litex_to_lean_error(
                &evidence.fact.proposition.line_file(),
                "comparison WD evidence without a FactId has no local binder to generalize",
            ));
        }

        let mut type_context = self.type_context.clone();
        let mut binders = Vec::with_capacity(symbols.len());
        for (symbol_id, occurrence_name) in symbols {
            let Some((source_name, carrier)) = certificate_symbol_carriers.get(&symbol_id) else {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    format!(
                        "generalized comparison WD evidence uses untyped local binder `{}`",
                        occurrence_name
                    ),
                ));
            };
            type_context.insert(symbol_id, carrier.clone());
            binders.push((lean_name(source_name), carrier.clone()));
        }
        let source_text = lean_fact_with_context(source, &type_context)?;
        let target_text = lean_fact_with_context(target, &type_context)?;
        let mut proposition = format!("{} → {}", source_text, target_text);
        for (name, carrier) in binders.iter().rev() {
            proposition = format!(
                "∀ ({} : {}), {}",
                name,
                type_context
                    .lean_type(carrier)
                    .map_err(|message| litex_to_lean_error(
                        &evidence.fact.proposition.line_file(),
                        message
                    ))?,
                proposition
            );
        }
        let mut proof_lines = vec!["by".to_string()];
        proof_lines.push(format!(
            "  intro {} litex_wd_source",
            binders
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        ));
        proof_lines.push("  exact litex_wd_source".to_string());
        Ok(Some((proposition, proof_lines.join("\n"))))
    }

    fn lean_generalized_strict_order_not_equal_well_definedness(
        &self,
        evidence: &LitexToLeanWellDefinednessFactIr,
        certificate_symbol_carriers: &HashMap<SymbolId, (String, LitexToLeanCarrierIr)>,
    ) -> Result<Option<(String, String)>, RuntimeError> {
        let Some(premises) = strict_order_not_equal_premises(&evidence.fact.proof) else {
            return Ok(None);
        };
        if premises.len() != 3 {
            return Err(litex_to_lean_error(
                &evidence.fact.proposition.line_file(),
                "generalized strict-order WD evidence has the wrong premise arity",
            ));
        }
        let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) = &evidence.fact.proposition else {
            return Err(litex_to_lean_error(
                &evidence.fact.proposition.line_file(),
                "generalized strict-order WD evidence has a non-inequality target",
            ));
        };
        for (index, expected_object) in [&target.left, &target.right].into_iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premises[index].proposition
            else {
                return Err(litex_to_lean_error(
                    &premises[index].proposition.line_file(),
                    "generalized strict-order WD carrier premise is not a membership fact",
                ));
            };
            if obj_equality_key(&membership.element) != obj_equality_key(expected_object)
                || !matches!(&membership.set, Obj::StandardSet(StandardSet::R))
            {
                return Err(litex_to_lean_error(
                    &premises[index].proposition.line_file(),
                    "generalized strict-order WD carrier premise does not match its target real operand",
                ));
            }
        }
        let (order_left, order_right) = match &premises[2].proposition {
            Fact::AtomicFact(AtomicFact::LessFact(order)) => (&order.left, &order.right),
            Fact::AtomicFact(AtomicFact::GreaterFact(order)) => (&order.left, &order.right),
            _ => {
                return Err(litex_to_lean_error(
                    &premises[2].proposition.line_file(),
                    "generalized strict-order WD evidence has no strict-order premise",
                ))
            }
        };
        let direct = obj_equality_key(order_left) == obj_equality_key(&target.left)
            && obj_equality_key(order_right) == obj_equality_key(&target.right);
        let reverse = obj_equality_key(order_left) == obj_equality_key(&target.right)
            && obj_equality_key(order_right) == obj_equality_key(&target.left);
        if !direct && !reverse {
            return Err(litex_to_lean_error(
                &premises[2].proposition.line_file(),
                "generalized strict-order WD premise does not compare the target operands",
            ));
        }

        let mut symbols = fact_ir_symbols(&evidence.fact.proposition)?;
        symbols.extend(fact_ir_symbols(&premises[2].proposition)?);
        symbols.sort_by_key(|(symbol_id, _)| *symbol_id);
        symbols.dedup_by_key(|(symbol_id, _)| *symbol_id);
        symbols.retain(|(symbol_id, _)| self.type_context.symbol_carrier(*symbol_id).is_none());
        if symbols.is_empty() {
            return Ok(None);
        }
        let mut type_context = self.type_context.clone();
        let mut binders = Vec::with_capacity(symbols.len());
        for (symbol_id, occurrence_name) in symbols {
            let Some((source_name, carrier)) = certificate_symbol_carriers.get(&symbol_id) else {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    format!(
                        "generalized strict-order WD evidence uses untyped local binder `{}`",
                        occurrence_name
                    ),
                ));
            };
            type_context.insert(symbol_id, carrier.clone());
            binders.push((lean_name(source_name), carrier.clone()));
        }
        let order_text = lean_fact_with_context(&premises[2].proposition, &type_context)?;
        let target_text = lean_fact_with_context(&evidence.fact.proposition, &type_context)?;
        let mut proposition = format!("{} → {}", order_text, target_text);
        for (name, carrier) in binders.iter().rev() {
            proposition = format!(
                "∀ ({} : {}), {}",
                name,
                type_context
                    .lean_type(carrier)
                    .map_err(|message| litex_to_lean_error(
                        &evidence.fact.proposition.line_file(),
                        message
                    ))?,
                proposition
            );
        }
        let mut proof_lines = vec!["by".to_string()];
        proof_lines.push(format!(
            "  intro {} litex_strict_order litex_equal",
            binders
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        ));
        proof_lines.push("  rw [litex_equal] at litex_strict_order".to_string());
        proof_lines.push("  exact (lt_irrefl _ litex_strict_order)".to_string());
        Ok(Some((proposition, proof_lines.join("\n"))))
    }

    fn emit_existential_witnesses(
        &mut self,
        ir: &LitexToLeanHaveExistentialWitnessIr,
    ) -> Result<(), RuntimeError> {
        let layout = validate_existential_elimination(ir)?;
        let first_witness = ir.witnesses.first().ok_or_else(|| {
            litex_to_lean_error(
                &ir.source.proposition.line_file(),
                "existential elimination IR must contain at least one witness",
            )
        })?;
        let source_name = lean_exist_source_name(first_witness.symbol_id);
        self.reserve_declaration_name(&source_name, &ir.source.proposition.line_file())?;
        let source_proof = self.lean_proof(
            &ir.source.proposition,
            &ir.source.proof,
            &self.root_proof_context(),
        )?;
        self.declarations.push(format!(
            "-- Litex checked existential source for `{}`\ntheorem {} : {} := {}",
            lean_comment_text(&first_witness.name),
            source_name,
            lean_fact_with_context(&ir.source.proposition, &self.type_context)?,
            source_proof
        ));

        for (witness, value_term) in ir.witnesses.iter().zip(layout.witness_terms.iter()) {
            self.reserve_declaration_name(
                &lean_name(&witness.name),
                &ir.source.proposition.line_file(),
            )?;
            let lean_type = lean_ir_param_type(&witness.param_type, &self.type_context)?;
            self.declarations.push(format!(
                "noncomputable def {} : {} := {}",
                lean_name(&witness.name),
                lean_type,
                value_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name)
            ));
            self.type_context
                .insert_param(witness.symbol_id, &witness.param_type);
        }
        for (projection, proof_term) in ir.projections.iter().zip(layout.proof_terms.iter()) {
            let fact_id = required_fact_id(projection)?;
            if self.emitted_fact_names.contains_key(&fact_id) {
                return Err(litex_to_lean_error(
                    &projection.proposition.line_file(),
                    "existential projection FactId was emitted before its witness definition",
                ));
            }
            let fact_name = lean_stored_fact_name(fact_id);
            self.reserve_declaration_name(&fact_name, &projection.proposition.line_file())?;
            self.emitted_fact_names.insert(fact_id, fact_name.clone());
            let proof_term = proof_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name);
            self.declarations.push(format!(
                "-- Litex fact {}\ntheorem {} : {} := by\n  exact {}",
                fact_id,
                fact_name,
                lean_fact_with_context(&projection.proposition, &self.type_context)?,
                proof_term
            ));
        }
        Ok(())
    }

    fn emit_object_choices(
        &mut self,
        ir: &LitexToLeanHaveObjectChoiceIr,
    ) -> Result<(), RuntimeError> {
        if ir.choices.is_empty() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "object-choice IR must contain at least one selected object",
            ));
        }
        for choice in ir.choices.iter() {
            let membership_fact_id = validate_object_choice(choice)?;
            if self.emitted_fact_names.contains_key(&membership_fact_id) {
                return Err(litex_to_lean_error(
                    &choice.membership.proposition.line_file(),
                    "object-choice membership FactId was emitted before its definition",
                ));
            }
            let source_name = lean_choice_source_name(choice.symbol_id);
            self.reserve_declaration_name(
                &source_name,
                &choice.membership.proposition.line_file(),
            )?;
            let source_proof = self.lean_proof(
                &choice.nonempty_proof.proposition,
                &choice.nonempty_proof.proof,
                &self.root_proof_context(),
            )?;
            self.declarations.push(format!(
                "-- Litex checked choice source for `{}`\ntheorem {} : {} := {}",
                lean_comment_text(&choice.name),
                source_name,
                lean_fact_with_context(&choice.nonempty_proof.proposition, &self.type_context)?,
                source_proof
            ));
            let element_carrier = self
                .type_context
                .membership_element_carrier(&choice.carrier)
                .map_err(|message| {
                    litex_to_lean_error(&choice.membership.proposition.line_file(), message)
                })?;
            self.reserve_declaration_name(
                &lean_name(&choice.name),
                &choice.membership.proposition.line_file(),
            )?;
            self.declarations.push(format!(
                "noncomputable def {} : {} := Exists.choose {}",
                lean_name(&choice.name),
                self.type_context
                    .lean_type(&element_carrier)
                    .map_err(|message| litex_to_lean_error(
                        &choice.membership.proposition.line_file(),
                        message
                    ))?,
                source_name
            ));
            self.type_context.insert(choice.symbol_id, element_carrier);
            let membership_fact_name = lean_stored_fact_name(membership_fact_id);
            self.reserve_declaration_name(
                &membership_fact_name,
                &choice.membership.proposition.line_file(),
            )?;
            self.emitted_fact_names
                .insert(membership_fact_id, membership_fact_name.clone());
            self.declarations.push(format!(
                "-- Litex fact {}\ntheorem {} : {} := by\n  exact Exists.choose_spec {}",
                membership_fact_id,
                membership_fact_name,
                lean_fact_with_context(&choice.membership.proposition, &self.type_context)?,
                source_name
            ));
        }
        Ok(())
    }

    fn emit_function_definition(
        &mut self,
        ir: &LitexToLeanHaveFunctionEqualIr,
    ) -> Result<(), RuntimeError> {
        let line_file = ir.return_check.proposition.line_file();
        self.reserve_declaration_name(&lean_name(&ir.name), &line_file)?;
        if ir.membership.proposition.to_string() != ir.membership.expected_proposition.to_string()
            || ir.defining_equality.proposition.to_string()
                != ir.defining_equality.expected_proposition.to_string()
        {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition stored fact does not match its frozen verifier target",
            ));
        }
        if ir.membership.fact_id == ir.defining_equality.fact_id
            || self.emitted_fact_names.contains_key(&ir.membership.fact_id)
            || self
                .emitted_fact_names
                .contains_key(&ir.defining_equality.fact_id)
        {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition facts have duplicate or previously emitted FactIds",
            ));
        }

        let Obj::FnSet(source_function_set) = &ir.source_function_set else {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition source signature is not a function set",
            ));
        };
        let rebuilt_function = LitexToLeanFunctionTypeIr::lower(source_function_set)
            .map_err(|message| litex_to_lean_error(&line_file, message))?;
        if rebuilt_function.semantic_key != ir.function.semantic_key {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition native signature does not match its frozen source function set",
            ));
        }
        let rebuilt_body = LitexToLeanObjectIr::lower(&ir.source_body)
            .map_err(|message| litex_to_lean_error(&line_file, message))?;
        if rebuilt_body != ir.body {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition body does not match its frozen source object",
            ));
        }
        let expected_return_check: Fact = InFact::new(
            ir.source_body.clone(),
            ir.source_return_set.clone(),
            line_file.clone(),
        )
        .into();
        if ir.return_check.proposition.to_string() != expected_return_check.to_string() {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition return proof was retargeted after verification",
            ));
        }

        if ir.parameter_premises.len() != ir.function.parameters.len()
            || ir.domain_premises.len() != ir.function.domain_facts.len()
        {
            return Err(litex_to_lean_error(
                &line_file,
                "function-definition parameter/domain evidence has the wrong arity",
            ));
        }
        for ((parameter, premise), source_parameter) in ir
            .function
            .parameters
            .iter()
            .zip(ir.parameter_premises.iter())
            .zip(
                source_function_set
                    .body
                    .params_def_with_set
                    .iter()
                    .flat_map(|group| group.params.iter().map(move |binding| (group, binding))),
            )
        {
            let (source_group, source_binding) = source_parameter;
            if parameter.symbol_id != source_binding.id() {
                return Err(litex_to_lean_error(
                    &line_file,
                    "function-definition parameter identity changed during lowering",
                ));
            }
            let expected: Fact = InFact::new(
                obj_for_bound_param_in_scope(source_binding, ParamObjType::FnSet),
                source_group.set_obj().clone(),
                line_file.clone(),
            )
            .into();
            if premise.fact.to_string() != expected.to_string() {
                return Err(litex_to_lean_error(
                    &line_file,
                    "function-definition parameter premise does not match its declared source set",
                ));
            }
        }
        for (premise, expected) in ir
            .domain_premises
            .iter()
            .zip(ir.function.domain_facts.iter())
        {
            if premise.fact.to_string() != expected.to_string() {
                return Err(litex_to_lean_error(
                    &line_file,
                    "function-definition domain premise changed during lowering",
                ));
            }
        }

        let mut context = self.root_proof_context();
        let mut seen_lean_parameter_names = HashMap::<String, (SymbolId, String)>::new();
        for parameter in ir.function.parameters.iter() {
            let emitted_name = lean_name(&parameter.name);
            if let Some((other_id, other_name)) = seen_lean_parameter_names.get(&emitted_name) {
                if *other_id != parameter.symbol_id {
                    return Err(lean_binder_name_collision_error(
                        &line_file,
                        "function definition",
                        other_name,
                        &parameter.name,
                        &emitted_name,
                    ));
                }
            }
            seen_lean_parameter_names
                .insert(emitted_name, (parameter.symbol_id, parameter.name.clone()));
            context
                .type_context
                .insert(parameter.symbol_id, parameter.element_carrier.clone());
            context.bound_symbol_ids.insert(parameter.symbol_id);
        }

        let mut binders = Vec::new();
        let mut binder_names = Vec::new();
        for parameter in ir.function.parameters.iter() {
            let parameter_name = lean_name(&parameter.name);
            binders.push(format!(
                "({} : {})",
                parameter_name,
                context
                    .type_context
                    .lean_type(&parameter.element_carrier)
                    .map_err(|message| litex_to_lean_error(&line_file, message))?
            ));
            binder_names.push(parameter_name);
        }

        let mut body_lines = Vec::new();
        for (index, (parameter, premise)) in ir
            .function
            .parameters
            .iter()
            .zip(ir.parameter_premises.iter())
            .enumerate()
        {
            let proof_name = lean_forall_parameter_proof_name(index + 1);
            let proposition = lean_fact_with_context(&premise.fact, &context.type_context)?;
            if parameter.requires_membership_proof {
                binders.push(format!("({proof_name} : {proposition})"));
                binder_names.push(proof_name.clone());
            } else {
                body_lines.push(format!("  have {proof_name} : {proposition} := by"));
                body_lines.push("    change True".to_string());
                body_lines.push("    trivial".to_string());
            }
            register_local_fact(premise.fact_id, &premise.fact, &proof_name, &mut context);
            context
                .type_context
                .insert_parameter_well_definedness_proof(&premise.fact, proof_name);
        }
        for (index, premise) in ir.domain_premises.iter().enumerate() {
            let proof_name = lean_forall_domain_proof_name(index + 1);
            binders.push(format!(
                "({proof_name} : {})",
                lean_fact_with_context(&premise.fact, &context.type_context)?
            ));
            binder_names.push(proof_name.clone());
            register_local_fact(premise.fact_id, &premise.fact, &proof_name, &mut context);
            context
                .type_context
                .insert_well_definedness_proof(&premise.fact, proof_name);
        }

        for inferred in ir.inferred_premises.iter() {
            let fact_id = required_fact_id(inferred)?;
            let (name, lines) = self.lean_named_local_fact(inferred, &mut context)?;
            body_lines.extend(lines);
            register_local_fact(fact_id, &inferred.proposition, &name, &mut context);
            context
                .type_context
                .insert_well_definedness_proof(&inferred.proposition, name);
        }
        body_lines.extend(self.lean_function_well_definedness_lines(
            &ir.well_definedness,
            ir.symbol_id,
            &mut context,
        )?);

        apply_fact_proof_type_hints(&ir.return_check, &mut context.type_context)?;
        let return_check_name = format!("litex_function_return_check_{}", ir.symbol_id.value());
        let return_proposition =
            lean_fact_with_context(&ir.return_check.proposition, &context.type_context)?;
        let return_proof = if ir.function.return_set.is_universal_native_set() {
            // Universal native carriers lower to `Set.univ`, so their checked
            // return-membership fact is definitionally `True`.  Refined
            // return sets keep and replay the verifier's exact proof below.
            "by\n  change True\n  trivial".to_string()
        } else {
            self.lean_proof(
                &ir.return_check.proposition,
                &ir.return_check.proof,
                &context,
            )?
        };
        let mut return_proof_lines = return_proof.lines();
        let first_return_proof_line = return_proof_lines.next().ok_or_else(|| {
            litex_to_lean_error(&line_file, "function-definition return proof is empty")
        })?;
        body_lines.push(format!(
            "  have {return_check_name} : {return_proposition} := {first_return_proof_line}"
        ));
        body_lines.extend(return_proof_lines.map(|line| format!("  {line}")));
        let membership_body_lines = body_lines.clone();

        let rendered_body = lean_obj_ir_with_expected(
            &ir.body,
            &ir.function.return_carrier,
            &context.type_context,
            false,
        )?;
        body_lines.push(format!("  exact {rendered_body}"));
        let lambda = if binders.is_empty() {
            format!("by\n{}", body_lines.join("\n"))
        } else {
            format!("fun {} => by\n{}", binders.join(" "), body_lines.join("\n"))
        };
        let function_type = lean_function_type_with_context(&ir.function, &self.type_context)?;
        self.declarations.push(format!(
            "-- Litex checked function definition `{}`\ndef {} : {} := {}",
            lean_comment_text(&ir.name),
            lean_name(&ir.name),
            function_type,
            lambda
        ));

        self.type_context.insert(
            ir.symbol_id,
            LitexToLeanCarrierIr::Function {
                function: Box::new(ir.function.clone()),
            },
        );
        let membership_fact_name = lean_stored_fact_name(ir.membership.fact_id);
        self.reserve_declaration_name(&membership_fact_name, &line_file)?;
        self.emitted_fact_names
            .insert(ir.membership.fact_id, membership_fact_name.clone());
        let membership_proof = if ir.function.return_set.is_universal_native_set() {
            "by\n  change True\n  trivial".to_string()
        } else {
            let mut lines = vec!["by".to_string()];
            if !binder_names.is_empty() {
                lines.push(format!("  intro {}", binder_names.join(" ")));
            }
            lines.extend(membership_body_lines);
            lines.push(format!(
                "  simpa only [{}] using {return_check_name}",
                lean_name(&ir.name)
            ));
            lines.join("\n")
        };
        self.declarations.push(format!(
            "-- Litex fact {}\ntheorem {} : {} := {}",
            ir.membership.fact_id,
            membership_fact_name,
            lean_fact_with_context(&ir.membership.proposition, &self.type_context)?,
            membership_proof
        ));
        let defining_equality_fact_name = lean_stored_fact_name(ir.defining_equality.fact_id);
        self.reserve_declaration_name(&defining_equality_fact_name, &line_file)?;
        self.emitted_fact_names.insert(
            ir.defining_equality.fact_id,
            defining_equality_fact_name.clone(),
        );
        self.emitted_function_definition_equalities.insert(
            ir.defining_equality.fact_id,
            ir.defining_equality.proposition.to_string(),
        );
        self.declarations.push(format!(
            "-- Litex checked defining equality: {}\n-- Litex fact {}\ntheorem {} : {} = ({}) := by\n  rfl",
            lean_comment_text(&ir.defining_equality.proposition.to_string()),
            ir.defining_equality.fact_id,
            defining_equality_fact_name,
            lean_name(&ir.name),
            lambda
        ));
        Ok(())
    }

    fn lean_function_well_definedness_lines(
        &mut self,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
        _function_symbol_id: SymbolId,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        validate_well_definedness_object_contract(certificate)?;
        context
            .type_context
            .install_well_definedness_certificate_metadata(certificate);
        self.lean_scoped_well_definedness_lines(&certificate.facts, context)
    }

    fn lean_scoped_well_definedness_lines(
        &mut self,
        evidence_facts: &[LitexToLeanWellDefinednessFactIr],
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let mut lines = Vec::new();
        let mut seen_ids = HashSet::new();
        for (index, evidence) in evidence_facts.iter().enumerate() {
            if !seen_ids.insert(evidence.certificate_id)
                || evidence.certificate_id.value() != index as u64 + 1
            {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "scoped well-definedness certificate IDs are duplicated, missing, or out of verifier order",
                ));
            }
            if evidence.expected_proposition.to_string() != evidence.fact.proposition.to_string() {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "scoped well-definedness proof proposition does not match its frozen verifier target",
                ));
            }
            if evidence.role != WellDefinednessRequirementRole::SourceObjectRequirement
                || matches!(evidence.fact.proof, LitexToLeanFactProofIr::Trusted)
            {
                return Err(litex_to_lean_error(
                    &evidence.fact.proposition.line_file(),
                    "scoped well-definedness certificate has an unsupported or trusted evidence role",
                ));
            }

            let reusable = context
                .well_defined_fact_names
                .get(&evidence.well_defined_fact_id)
                .cloned()
                .or_else(|| {
                    evidence
                        .fact
                        .fact_id
                        .and_then(|fact_id| context.proof_fact_names.get(&fact_id).cloned())
                })
                .or_else(|| {
                    direct_citation_fact_id(&evidence.fact.proof)
                        .and_then(|fact_id| context.proof_fact_names.get(&fact_id).cloned())
                })
                .or_else(|| {
                    context
                        .type_context
                        .well_definedness_proof(&evidence.fact.proposition)
                        .map(str::to_string)
                });
            if let Some(reusable) = reusable {
                lines.push(format!(
                    "  -- Litex well-definedness certificate {} reuses {}",
                    evidence.certificate_id.value(),
                    reusable
                ));
                context
                    .type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        reusable.clone(),
                    );
                context
                    .well_defined_fact_names
                    .insert(evidence.well_defined_fact_id, reusable.clone());
                continue;
            }

            if let Some((helper_name, helper_binders)) = self
                .generalized_scoped_well_definedness
                .get(&evidence.well_defined_fact_id)
                .cloned()
            {
                if helper_binders
                    .iter()
                    .any(|(symbol_id, _)| !context.bound_symbol_ids.contains(symbol_id))
                {
                    // These are binders belonging to a `fn(...)` signature,
                    // not terms in the surrounding theorem. The generalized
                    // helper is the exact Lean replay of that source-only WD
                    // check; introducing its binder here would be ill-scoped.
                    lines.push(format!(
                        "  -- Litex well-definedness certificate {} replayed by generalized helper {}",
                        evidence.certificate_id.value(),
                        helper_name
                    ));
                    continue;
                }
                let local_name = self.next_well_defined_fact_name(context);
                let proposition =
                    lean_fact_with_context(&evidence.fact.proposition, &context.type_context)?;
                let helper_arguments = helper_binders
                    .iter()
                    .map(|(_, name)| lean_name(name))
                    .collect::<Vec<_>>();
                let helper_application = if helper_arguments.is_empty() {
                    helper_name
                } else {
                    format!("{} {}", helper_name, helper_arguments.join(" "))
                };
                lines.push(format!("  have {local_name} : {proposition} := by"));
                lines.push(format!("    exact {helper_application}"));
                context
                    .type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        local_name.clone(),
                    );
                context
                    .well_defined_fact_names
                    .insert(evidence.well_defined_fact_id, local_name.clone());
                if let Some(fact_id) = evidence.fact.fact_id {
                    register_local_fact(fact_id, &evidence.fact.proposition, &local_name, context);
                }
                continue;
            }

            apply_fact_proof_type_hints(&evidence.fact, &mut context.type_context)?;
            let local_name = self.next_well_defined_fact_name(context);
            let proposition =
                lean_fact_with_context(&evidence.fact.proposition, &context.type_context)?;
            if is_universal_native_membership_fact(&evidence.fact.proposition) {
                lines.push(format!("  have {local_name} : {proposition} := by"));
                lines.push("    change True".to_string());
                lines.push("    trivial".to_string());
            } else if crate::litex_to_lean_ir::is_closed_numeric_relation(
                &evidence.fact.proposition,
            ) {
                lines.push(format!("  have {local_name} : {proposition} := by"));
                lines.push("    norm_num".to_string());
            } else {
                let (generated_name, generated_lines) = self
                    .lean_named_local_fact(&evidence.fact, context)
                    .map_err(|error| {
                        litex_to_lean_error(
                            &evidence.fact.proposition.line_file(),
                            format!(
                                "cannot replay scoped well-definedness certificate {} for `{}`: {}",
                                evidence.certificate_id.value(),
                                evidence.fact.proposition,
                                error.trace_message()
                            ),
                        )
                    })?;
                lines.extend(generated_lines);
                let proposition =
                    lean_fact_with_context(&evidence.fact.proposition, &context.type_context)?;
                lines.push(format!(
                    "  have {local_name} : {proposition} := {generated_name}"
                ));
                context
                    .type_context
                    .insert_well_definedness_proof_by_certificate_id(
                        evidence.certificate_id,
                        &evidence.fact.proposition,
                        local_name.clone(),
                    );
                context
                    .well_defined_fact_names
                    .insert(evidence.well_defined_fact_id, local_name.clone());
                if let Some(fact_id) = evidence.fact.fact_id {
                    register_local_fact(fact_id, &evidence.fact.proposition, &local_name, context);
                }
                continue;
            }
            context
                .type_context
                .insert_well_definedness_proof_by_certificate_id(
                    evidence.certificate_id,
                    &evidence.fact.proposition,
                    local_name.clone(),
                );
            context
                .well_defined_fact_names
                .insert(evidence.well_defined_fact_id, local_name.clone());
            if let Some(fact_id) = evidence.fact.fact_id {
                register_local_fact(fact_id, &evidence.fact.proposition, &local_name, context);
            }
        }
        Ok(lines)
    }

    fn emit_trusted_fact(&mut self, fact: &LitexToLeanFactIr) -> Result<(), RuntimeError> {
        if !matches!(fact.proof, LitexToLeanFactProofIr::Trusted) {
            return Err(litex_to_lean_error(
                &fact.proposition.line_file(),
                "only an explicit Litex `trust` statement may emit a Lean axiom",
            ));
        }
        let fact_id = required_fact_id(fact)?;
        if self.emitted_fact_names.contains_key(&fact_id) {
            return Ok(());
        }
        let fact_name = lean_stored_fact_name(fact_id);
        self.reserve_declaration_name(&fact_name, &fact.proposition.line_file())?;
        self.emitted_fact_names.insert(fact_id, fact_name.clone());
        self.declarations.push(format!(
            "-- Litex trust boundary: {}\naxiom {} : {}",
            fact_id,
            fact_name,
            lean_fact_with_context(&fact.proposition, &self.type_context)?
        ));
        Ok(())
    }

    fn emit_proved_fact(&mut self, fact: &LitexToLeanFactIr) -> Result<(), RuntimeError> {
        let fact_id = required_fact_id(fact)?;
        if self.emitted_fact_names.contains_key(&fact_id) {
            return Ok(());
        }
        if matches!(fact.proof, LitexToLeanFactProofIr::Trusted) {
            return Err(litex_to_lean_error(
                &fact.proposition.line_file(),
                "trusted evidence reached theorem emission outside a `trust` statement",
            ));
        }
        let mut proof_context = self.root_proof_context();
        apply_fact_proof_type_hints(fact, &mut proof_context.type_context)?;
        let proof = self.lean_proof(&fact.proposition, &fact.proof, &proof_context)?;
        let fact_name = lean_stored_fact_name(fact_id);
        self.reserve_declaration_name(&fact_name, &fact.proposition.line_file())?;
        self.emitted_fact_names.insert(fact_id, fact_name.clone());
        self.declarations.push(format!(
            "-- Litex fact {}\ntheorem {} : {} := {}",
            fact_id,
            fact_name,
            lean_fact_with_context(&fact.proposition, &proof_context.type_context)?,
            proof
        ));
        Ok(())
    }

    fn emit_proved_fact_with_scoped_well_definedness(
        &mut self,
        fact: &LitexToLeanFactIr,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<(), RuntimeError> {
        let fact_id = required_fact_id(fact)?;
        if self.emitted_fact_names.contains_key(&fact_id) {
            return Ok(());
        }
        if !proof_is_forall_introduction(&fact.proof) {
            return Err(litex_to_lean_error(
                &fact.proposition.line_file(),
                "scoped well-definedness evidence requires a forall-introduction proof",
            ));
        }
        self.emit_scoped_certificate_type_witnesses(certificate, &fact.proposition)?;
        let mut proof_context = self.root_proof_context();
        proof_context.scoped_well_definedness = certificate.facts.clone();
        apply_fact_proof_type_hints(fact, &mut proof_context.type_context)?;
        let proof = self.lean_proof(&fact.proposition, &fact.proof, &proof_context)?;
        let fact_name = lean_stored_fact_name(fact_id);
        self.reserve_declaration_name(&fact_name, &fact.proposition.line_file())?;
        self.emitted_fact_names.insert(fact_id, fact_name.clone());
        self.declarations.push(format!(
            "-- Litex fact {}\ntheorem {} : {} := {}",
            fact_id,
            fact_name,
            lean_fact_with_context(&fact.proposition, &proof_context.type_context)?,
            proof
        ));
        Ok(())
    }

    fn lean_proof(
        &mut self,
        proposition: &Fact,
        proof: &LitexToLeanFactProofIr,
        parent_context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let mut context = parent_context.new_proof_space();
        self.lean_proof_in_current_space(proposition, proof, &mut context)
    }

    fn lean_proof_in_current_space(
        &mut self,
        proposition: &Fact,
        proof: &LitexToLeanFactProofIr,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        match proof {
            LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => {
                if closed_rational_equality_with_target_expectation(
                    proposition,
                    &context.type_context,
                ) {
                    return Ok("by\n  norm_num".to_string());
                }
                let source = self.available_fact_name(*source_fact_id, proposition, context)?;
                Ok(format!("by\n  exact {}", source))
            }
            LitexToLeanFactProofIr::ExistentialAlphaRenameCitation {
                source_fact_id,
                source_proposition,
            } => {
                validate_existential_alpha_rename(source_proposition, proposition)?;
                let source = self.available_fact_name(*source_fact_id, proposition, context)?;
                Ok(format!("by\n  exact {}", source))
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::Builtin(rule),
                parameter_requirements,
                premises,
            } => self.lean_builtin_rule_application(
                proposition,
                rule,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                parameter_requirements,
                premises,
            } => self.lean_registered_rule_application(
                proposition,
                application,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ObjectReflexivity,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "object-reflexivity evidence was attached to a non-equality",
                    ));
                };
                if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "object-reflexivity evidence has different left and right objects",
                    ));
                }
                Ok("by\n  rfl".to_string())
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedRealMembership,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                Ok("by\n  change True\n  trivial".to_string())
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedUniversalNativeMembership,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty()
                && premises.is_empty()
                && crate::litex_to_lean_ir::is_closed_universal_native_membership(proposition) =>
            {
                Ok("by\n  change True\n  trivial".to_string())
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedNumericReflection { .. },
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                Ok("by\n  norm_num".to_string())
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::RealSetNonempty,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                lean_real_set_nonempty(proposition)
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::StandardSetNonempty,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                lean_standard_set_nonempty(proposition)
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::FunctionApplicationReturnMembership {
                        source_application,
                        function_set,
                        typed_return_set,
                        expected_target,
                        expected_head_membership,
                    },
                parameter_requirements,
                premises,
            } => self.lean_function_application_return_membership(
                proposition,
                source_application,
                function_set,
                typed_return_set,
                expected_target,
                expected_head_membership,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClosedNumericComparison { expected_target },
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty()
                && premises.is_empty()
                && proposition.to_string() == expected_target.to_string()
                && crate::litex_to_lean_ir::is_closed_numeric_relation(proposition) =>
            {
                Ok("by\n  norm_num".to_string())
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::RefinedNumericMembership {
                        target_set,
                        expected_target,
                        expected_premises,
                    },
                parameter_requirements,
                premises,
            } => self.lean_refined_numeric_membership(
                proposition,
                target_set,
                expected_target,
                expected_premises,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::FunctionSetMembership {
                        element,
                        function_set,
                        expected_target,
                        expected_pointwise,
                    },
                parameter_requirements,
                premises,
            } => self.lean_function_set_membership(
                proposition,
                element,
                function_set,
                expected_target,
                expected_pointwise,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::SetBuilderMembership {
                        set_builder,
                        expected_target,
                        expected_premises,
                    },
                parameter_requirements,
                premises,
            } => self.lean_set_builder_membership(
                proposition,
                set_builder,
                expected_target,
                expected_premises,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ClassicalExcludedMiddle,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                lean_classical_excluded_middle(proposition, &context.type_context)
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::KnownForallInstantiation {
                        source_fact_id,
                        arguments,
                    },
                parameter_requirements,
                premises,
            } => self.lean_known_forall_instantiation(
                proposition,
                *source_fact_id,
                arguments,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::Normalization {
                        kind: LitexToLeanNormalizationKindIr::IntegerExpressionSimplification,
                    },
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty()
                && crate::litex_to_lean_ir::is_checked_closed_integer_remainder_equality(
                    proposition,
                ) =>
            {
                let mut lines = vec!["by".to_string()];
                for premise in premises {
                    let (_, premise_lines) = self.lean_named_local_fact(premise, context)?;
                    lines.extend(premise_lines);
                }
                lines.push("  norm_num".to_string());
                Ok(lines.join("\n"))
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::Normalization {
                        kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                    },
                ..
            } if matches!(
                proposition,
                Fact::AtomicFact(AtomicFact::EqualFact(equality))
                    if closed_rational_expression(&equality.left)
                        && closed_rational_expression(&equality.right)
                        && objs_equal_by_rational_expression_evaluation(
                        &equality.left,
                        &equality.right,
                    )
            ) =>
            {
                lean_rational_builtin_proof(proposition, context)
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::Normalization {
                        kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                    },
                premises,
                ..
            } if premises.is_empty() => lean_rational_builtin_proof(proposition, context),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::Normalization {
                        kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                    },
                premises,
                ..
            } if premises.len() == 1 => {
                self.lean_normalization_from_premise(proposition, &premises[0], context)
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::DefinitionProjection {
                        definition,
                        expected_source,
                        expected_target,
                    },
                parameter_requirements,
                premises,
            } => self.lean_definition_projection(
                proposition,
                definition,
                expected_source,
                expected_target,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::DefinitionIntroduction {
                        definition,
                        expected_source,
                        expected_target,
                    },
                parameter_requirements,
                premises,
            } => self.lean_definition_introduction(
                proposition,
                definition,
                expected_source,
                expected_target,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::ComparisonNotationDuality {
                        expected_source,
                        expected_target,
                    },
                parameter_requirements,
                premises,
            } => self.lean_comparison_notation_duality(
                proposition,
                expected_source,
                expected_target,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::DefinitionReduction { definition },
                premises,
                ..
            } if premises.is_empty() => Ok(format!("by\n  simp [{}]", lean_name(definition))),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::CheckedFunctionDefinitionReplay {
                        definition,
                        defining_equality_fact_id,
                        defining_equality,
                        expected_target,
                        application_side,
                        reduced,
                        other_side,
                        application_is_left,
                        reduced_matches_other_by_alpha,
                    },
                parameter_requirements,
                premises,
            } => self.lean_checked_function_definition_replay(
                proposition,
                definition,
                *defining_equality_fact_id,
                defining_equality,
                expected_target,
                application_side,
                reduced,
                other_side,
                *application_is_left,
                *reduced_matches_other_by_alpha,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::EqualityRewrite(rewrite),
                premises,
                ..
            } => self.lean_equality_rewrite(proposition, rewrite, premises, context),
            LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::ExistIntroduction {
                        witnesses,
                        steps,
                        expected_parameter_requirements,
                        expected_body_facts,
                    },
                parameter_requirements,
                premises,
            } => self.lean_exist_introduction(
                proposition,
                witnesses,
                steps,
                expected_parameter_requirements,
                expected_body_facts,
                parameter_requirements,
                premises,
                context,
            ),
            LitexToLeanFactProofIr::RuleApplication { rule, .. } => Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "Litex-to-Lean has no checked backend for proof rule {:?} on `{}`",
                    rule, proposition
                ),
            )),
            LitexToLeanFactProofIr::ForallIntroduction {
                parameter_premises,
                premises,
                inferred_premises,
                conclusions,
            } => self.lean_forall_introduction(
                proposition,
                parameter_premises,
                premises,
                inferred_premises,
                conclusions,
                context,
            ),
            LitexToLeanFactProofIr::ObjectDefinition {
                definition,
                value,
                value_check,
            } => self.lean_object_definition_fact(
                proposition,
                definition,
                value,
                value_check.as_deref(),
                context,
            ),
            LitexToLeanFactProofIr::ObjectChoice { .. } => Err(litex_to_lean_error(
                &proposition.line_file(),
                "object-choice membership must be emitted with its defining choice statement",
            )),
            LitexToLeanFactProofIr::ExistentialElimination { .. } => Err(litex_to_lean_error(
                &proposition.line_file(),
                "existential projections must be emitted with their defining elimination statement",
            )),
            LitexToLeanFactProofIr::CaseSplit { coverage, branches } => {
                self.lean_case_split(proposition, coverage, branches, context)
            }
            LitexToLeanFactProofIr::ByContradiction {
                reverse_assumption,
                steps,
                contradiction,
            } => self.lean_by_contradiction(
                proposition,
                reverse_assumption,
                steps,
                contradiction,
                context,
            ),
            LitexToLeanFactProofIr::Memo { proof } => {
                self.lean_proof_in_current_space(proposition, proof, context)
            }
            LitexToLeanFactProofIr::Composite { steps } if steps.len() == 1 => {
                self.lean_proof_in_current_space(&steps[0].proposition, &steps[0].proof, context)
            }
            LitexToLeanFactProofIr::UserStrategy { name } => Err(litex_to_lean_error(
                &proposition.line_file(),
                format!("Litex-to-Lean does not yet lower user strategy `{}`", name),
            )),
            LitexToLeanFactProofIr::Inference { reason, .. } => Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "Litex-to-Lean does not yet lower inferred fact origin `{}`",
                    reason
                ),
            )),
            LitexToLeanFactProofIr::Unsupported { reason } => Err(litex_to_lean_error(
                &proposition.line_file(),
                reason.clone(),
            )),
            LitexToLeanFactProofIr::Trusted => Err(litex_to_lean_error(
                &proposition.line_file(),
                "trusted proof cannot be emitted as a theorem",
            )),
            LitexToLeanFactProofIr::Composite { .. } => Err(litex_to_lean_error(
                &proposition.line_file(),
                "Litex-to-Lean does not yet lower multi-step composite evidence",
            )),
        }
    }

    fn lean_named_local_fact(
        &mut self,
        fact: &LitexToLeanFactIr,
        context: &mut LeanProofContext,
    ) -> Result<(String, Vec<String>), RuntimeError> {
        apply_fact_proof_type_hints(fact, &mut context.type_context)?;
        let local_name = self.next_proof_fact_name(context);
        if let Some(fact_id) = fact.fact_id {
            if let Some(local) = context.proof_fact_names.get(&fact_id) {
                return Ok((
                    local_name.clone(),
                    vec![format!(
                        "  have {} : {} := {}",
                        local_name,
                        lean_fact_with_context(&fact.proposition, &context.type_context)?,
                        local
                    )],
                ));
            }
        }
        if let LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } = &fact.proof {
            if closed_rational_equality_with_target_expectation(
                &fact.proposition,
                &context.type_context,
            ) {
                return Ok((
                    local_name.clone(),
                    vec![
                        format!(
                            "  have {} : {} := by",
                            local_name,
                            lean_fact_with_context(&fact.proposition, &context.type_context)?
                        ),
                        "    norm_num".to_string(),
                    ],
                ));
            }
            let source = self.available_fact_name(*source_fact_id, &fact.proposition, context)?;
            return Ok((
                local_name.clone(),
                vec![format!(
                    "  have {} : {} := {}",
                    local_name,
                    lean_fact_with_context(&fact.proposition, &context.type_context)?,
                    source
                )],
            ));
        }

        let proof = self.lean_proof(&fact.proposition, &fact.proof, context)?;
        let mut proof_lines = proof.lines();
        let first = proof_lines.next().ok_or_else(|| {
            litex_to_lean_error(
                &fact.proposition.line_file(),
                "a local fact emitted an empty Lean proof",
            )
        })?;
        let mut lines = vec![format!(
            "  have {} : {} := {}",
            local_name,
            lean_fact_with_context(&fact.proposition, &context.type_context)?,
            first
        )];
        // Formerly the proof was one String containing embedded newlines. A
        // surrounding case bullet could then indent only its first line,
        // leaking nested proof lines out of the branch. Preserve logical lines
        // separately so every enclosing scope can add its own indentation.
        lines.extend(proof_lines.map(|line| format!("  {}", line)));
        Ok((local_name, lines))
    }

    fn lean_object_definition_fact(
        &mut self,
        proposition: &Fact,
        definition: &str,
        value: &LitexToLeanObjectIr,
        value_check: Option<&LitexToLeanFactIr>,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let definition = lean_name(definition);
        if let Some(value_check) = value_check {
            let (value_check_name, mut lines) = self.lean_named_local_fact(value_check, context)?;
            lines.insert(0, "by".to_string());
            lines.push(format!(
                "  simpa only [{}] using {}",
                definition, value_check_name
            ));
            return Ok(lines.join("\n"));
        }

        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "a defining object equality must be an equality fact",
            ));
        };
        let left = LitexToLeanObjectIr::lower(&equality.left)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        let right = LitexToLeanObjectIr::lower(&equality.right)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        let left_matches_definition = matches!(
            &left,
            LitexToLeanObjectIr::Symbol { name, .. } if lean_name(name) == definition
        );
        if !left_matches_definition || right != *value {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "a defining object equality does not match its declaration IR",
            ));
        }
        Ok("by\n  rfl".to_string())
    }

    fn lean_case_split(
        &mut self,
        proposition: &Fact,
        coverage: &LitexToLeanFactIr,
        branches: &[LitexToLeanCaseBranchIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::OrFact(coverage_fact) = &coverage.proposition else {
            return Err(litex_to_lean_error(
                &coverage.proposition.line_file(),
                "case-split coverage must be a disjunction",
            ));
        };
        if coverage_fact.facts.len() != branches.len() || branches.len() < 2 {
            return Err(litex_to_lean_error(
                &coverage.proposition.line_file(),
                "case-split branch count does not match its coverage disjunction",
            ));
        }

        let (coverage_name, coverage_lines) = self.lean_named_local_fact(coverage, context)?;
        let mut branch_names = Vec::with_capacity(branches.len());
        let mut branch_bodies = Vec::with_capacity(branches.len());
        for (index, branch) in branches.iter().enumerate() {
            let expected_case: Fact = coverage_fact.facts[index].clone().into();
            if branch.assumption.fact.to_string() != expected_case.to_string() {
                return Err(litex_to_lean_error(
                    &branch.assumption.fact.line_file(),
                    "case-split assumption does not match its coverage branch",
                ));
            }
            let mut branch_context = context.new_proof_space();
            let assumption_name = self.next_proof_fact_name(&mut branch_context);
            register_local_fact(
                branch.assumption.fact_id,
                &branch.assumption.fact,
                &assumption_name,
                &mut branch_context,
            );
            branch_names.push(assumption_name);

            let mut body = Vec::new();
            for step in branch.steps.iter() {
                body.extend(self.lean_local_statement(step, &mut branch_context)?);
            }
            match &branch.exit {
                LitexToLeanCaseBranchExitIr::Conclusion(conclusion) => {
                    if conclusion.proposition.to_string() != proposition.to_string() {
                        return Err(litex_to_lean_error(
                            &conclusion.proposition.line_file(),
                            "case-split conclusion does not match the parent goal",
                        ));
                    }
                    let proof = self.lean_proof_in_current_space(
                        &conclusion.proposition,
                        &conclusion.proof,
                        &mut branch_context,
                    )?;
                    let Some(proof_body) = proof.strip_prefix("by\n") else {
                        return Err(litex_to_lean_error(
                            &conclusion.proposition.line_file(),
                            "case-split conclusion did not emit a Lean proof block",
                        ));
                    };
                    body.extend(proof_body.lines().map(str::to_string));
                }
                LitexToLeanCaseBranchExitIr::Contradiction(contradiction) => {
                    body.extend(self.lean_contradiction_lines(contradiction, &mut branch_context)?);
                }
            }
            branch_bodies.push(body);
        }

        let mut lines = vec!["by".to_string()];
        lines.extend(coverage_lines);
        lines.push(format!(
            "  rcases {} with {}",
            coverage_name,
            branch_names.join(" | ")
        ));
        for body in branch_bodies {
            push_lean_bullet(&mut lines, &body)?;
        }
        Ok(lines.join("\n"))
    }

    fn lean_by_contradiction(
        &mut self,
        proposition: &Fact,
        reverse_assumption: &LitexToLeanLocalPremiseIr,
        steps: &[LitexToLeanStatementIr],
        contradiction: &LitexToLeanContradictionIr,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::AtomicFact(target) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "this Litex-to-Lean tranche lowers `by contra` only for atomic goals",
            ));
        };
        let expected_reverse = target.logical_negation()?;
        if reverse_assumption.fact.to_string() != Fact::from(expected_reverse).to_string() {
            return Err(litex_to_lean_error(
                &reverse_assumption.fact.line_file(),
                "by-contra reverse assumption is not the logical negation of its goal",
            ));
        }
        let _ = lean_fact_with_context(proposition, &context.type_context)?;
        let reverse_fact_text =
            lean_fact_with_context(&reverse_assumption.fact, &context.type_context)?;

        let mut lines = vec![
            "by".to_string(),
            "  classical".to_string(),
            "  apply Classical.byContradiction".to_string(),
        ];
        let introduced_name = self.next_proof_fact_name(context);
        lines.push(format!("  intro {}", introduced_name));
        let reverse_name = if target.is_true() {
            introduced_name
        } else {
            let reverse_name = self.next_proof_fact_name(context);
            lines.push(format!(
                "  have {} : {} := Classical.byContradiction {}",
                reverse_name, reverse_fact_text, introduced_name
            ));
            reverse_name
        };
        register_local_fact(
            reverse_assumption.fact_id,
            &reverse_assumption.fact,
            &reverse_name,
            context,
        );
        for step in steps.iter() {
            lines.extend(self.lean_local_statement(step, context)?);
        }
        lines.extend(self.lean_contradiction_lines(contradiction, context)?);
        Ok(lines.join("\n"))
    }

    fn lean_local_statement(
        &mut self,
        statement: &LitexToLeanStatementIr,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let mut lines = Vec::new();
        match statement {
            LitexToLeanStatementIr::Fact(ir) => {
                if !ir.well_definedness.facts.is_empty() {
                    validate_well_definedness_object_contract(&ir.well_definedness)?;
                    context
                        .type_context
                        .install_well_definedness_certificate_metadata(&ir.well_definedness);
                    apply_fact_proof_type_hints(&ir.fact, &mut context.type_context)?;
                    lines.extend(
                        self.lean_scoped_well_definedness_lines(
                            &ir.well_definedness.facts,
                            context,
                        )?,
                    );
                }
                lines.extend(self.lean_local_fact(&ir.fact, context)?);
                for fact in ir.inferred_facts.iter() {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            LitexToLeanStatementIr::ProjectedForall(ir) => {
                if !ir.well_definedness.facts.is_empty() {
                    return Err(litex_to_lean_error(
                        &ir.source.line_file(),
                        "proof-local projected facts retain unsupported scoped well-definedness certificates",
                    ));
                }
                validate_projected_forall_ir(ir)?;
                for fact in ir.facts.iter().chain(ir.inferred_facts.iter()) {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            LitexToLeanStatementIr::Proof(ir) => {
                for fact in ir.facts.iter().chain(ir.inferred_facts.iter()) {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            LitexToLeanStatementIr::HaveObjChoice(ir) => {
                lines.extend(self.lean_local_object_choices(ir, context)?);
            }
            LitexToLeanStatementIr::HaveExistentialWitness(ir) => {
                lines.extend(self.lean_local_existential_witnesses(ir, context)?);
            }
            LitexToLeanStatementIr::HaveObjEqual(ir) => {
                for definition in ir.definitions.iter() {
                    let lean_type =
                        lean_ir_param_type(&definition.param_type, &context.type_context)?;
                    let expected = param_type_object_carrier(&definition.param_type)?;
                    lines.push(format!(
                        "  let {} : {} := {}",
                        lean_name(&definition.name),
                        lean_type,
                        lean_obj_ir_with_expected(
                            &definition.value,
                            &expected,
                            &context.type_context,
                            false,
                        )?
                    ));
                    context
                        .type_context
                        .insert_param(definition.symbol_id, &definition.param_type);
                }
                for fact in ir.facts.iter() {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            other => {
                return Err(litex_to_lean_error(
                    &statement_ir_line_file(other),
                    format!(
                        "Litex-to-Lean does not support local statement `{}` inside a proof scope",
                        statement_ir_display(other)
                    ),
                ));
            }
        }
        Ok(lines)
    }

    fn lean_local_existential_witnesses(
        &mut self,
        ir: &LitexToLeanHaveExistentialWitnessIr,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let layout = validate_existential_elimination(ir)?;
        let (source_name, mut lines) = self.lean_named_local_fact(&ir.source, context)?;
        for (witness, value_term) in ir.witnesses.iter().zip(layout.witness_terms.iter()) {
            let lean_type = lean_ir_param_type(&witness.param_type, &context.type_context)?;
            lines.push(format!(
                "  let {} : {} := {}",
                lean_name(&witness.name),
                lean_type,
                value_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name)
            ));
            context
                .type_context
                .insert_param(witness.symbol_id, &witness.param_type);
        }
        for (projection, proof_term) in ir.projections.iter().zip(layout.proof_terms.iter()) {
            let fact_id = required_fact_id(projection)?;
            let local_name = self.next_proof_fact_name(context);
            lines.push(format!(
                "  have {} : {} := by",
                local_name,
                lean_fact_with_context(&projection.proposition, &context.type_context)?
            ));
            lines.push(format!(
                "    exact {}",
                proof_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name)
            ));
            register_local_fact(fact_id, &projection.proposition, &local_name, context);
        }
        Ok(lines)
    }

    fn lean_local_object_choices(
        &mut self,
        ir: &LitexToLeanHaveObjectChoiceIr,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        if ir.choices.is_empty() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "local object-choice IR must contain at least one selected object",
            ));
        }
        let mut lines = Vec::new();
        for choice in ir.choices.iter() {
            let membership_fact_id = validate_object_choice(choice)?;
            let (source_name, source_lines) =
                self.lean_named_local_fact(&choice.nonempty_proof, context)?;
            lines.extend(source_lines);
            let element_carrier = context
                .type_context
                .membership_element_carrier(&choice.carrier)
                .map_err(|message| {
                    litex_to_lean_error(&choice.membership.proposition.line_file(), message)
                })?;
            lines.push(format!(
                "  let {} : {} := Exists.choose {}",
                lean_name(&choice.name),
                context
                    .type_context
                    .lean_type(&element_carrier)
                    .map_err(|message| litex_to_lean_error(
                        &choice.membership.proposition.line_file(),
                        message
                    ))?,
                source_name
            ));
            context
                .type_context
                .insert(choice.symbol_id, element_carrier);
            let membership_name = self.next_proof_fact_name(context);
            lines.push(format!(
                "  have {} : {} := by",
                membership_name,
                lean_fact_with_context(&choice.membership.proposition, &context.type_context)?
            ));
            lines.push(format!("    exact Exists.choose_spec {}", source_name));
            register_local_fact(
                membership_fact_id,
                &choice.membership.proposition,
                &membership_name,
                context,
            );
        }
        Ok(lines)
    }

    fn lean_local_fact(
        &mut self,
        fact: &LitexToLeanFactIr,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let (name, lines) = self.lean_named_local_fact(fact, context)?;
        if let Some(fact_id) = fact.fact_id {
            register_local_fact(fact_id, &fact.proposition, &name, context);
        }
        Ok(lines)
    }

    fn lean_contradiction_lines(
        &mut self,
        contradiction: &LitexToLeanContradictionIr,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let (fact_name, mut lines) = self.lean_named_local_fact(&contradiction.fact, context)?;
        let (negated_name, negated_lines) =
            self.lean_named_local_fact(&contradiction.negated_fact, context)?;
        lines.extend(negated_lines);

        let (Fact::AtomicFact(fact), Fact::AtomicFact(negated_fact)) = (
            &contradiction.fact.proposition,
            &contradiction.negated_fact.proposition,
        ) else {
            return Err(litex_to_lean_error(
                &contradiction.fact.proposition.line_file(),
                "a contradiction exit currently requires complementary atomic facts",
            ));
        };
        let facts_are_complements = fact
            .logical_negation()
            .is_ok_and(|negation| negation.to_string() == negated_fact.to_string());
        if !facts_are_complements {
            return Err(litex_to_lean_error(
                &contradiction.fact.proposition.line_file(),
                "contradiction facts are not logical complements",
            ));
        }
        let (positive_name, negative_name) = if fact.is_true() {
            (&fact_name, &negated_name)
        } else {
            (&negated_name, &fact_name)
        };
        lines.push(format!(
            "  exact False.elim ({} {})",
            negative_name, positive_name
        ));
        Ok(lines)
    }

    #[allow(clippy::too_many_arguments)]
    fn lean_exist_introduction(
        &mut self,
        proposition: &Fact,
        witnesses: &[Obj],
        steps: &[LitexToLeanStatementIr],
        expected_parameter_requirements: &[Fact],
        expected_body_facts: &[Fact],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::ExistFact(ExistFactEnum::ExistFact(body)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "existential-introduction evidence requires a positive `exist` target",
            ));
        };
        let param_types = flattened_exist_param_types(body);
        if witnesses.is_empty() || witnesses.len() != param_types.len() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "existential-introduction witness count does not match its target binders",
            ));
        }
        let required_param_count = param_types
            .iter()
            .filter(|param_type| !matches!(param_type, ParamType::Set(_)))
            .count();
        if parameter_requirements.len() != required_param_count
            || expected_parameter_requirements.len() != required_param_count
            || premises.len() != body.facts.len()
            || expected_body_facts.len() != body.facts.len()
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "existential-introduction requirement or body-premise count is inconsistent",
            ));
        }
        for (actual, expected) in parameter_requirements
            .iter()
            .zip(expected_parameter_requirements.iter())
        {
            if actual.fact_id.is_some() || actual.proposition.to_string() != expected.to_string() {
                return Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "existential-introduction parameter evidence disagrees with its retained proposition",
                ));
            }
        }
        for (actual, expected) in premises.iter().zip(expected_body_facts.iter()) {
            if actual.fact_id.is_some() || actual.proposition.to_string() != expected.to_string() {
                return Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "existential-introduction body evidence disagrees with its retained proposition",
                ));
            }
        }

        let mut witness_carriers = Vec::with_capacity(witnesses.len());
        for (witness, param_type) in witnesses.iter().zip(param_types.iter()) {
            let carrier = match param_type {
                ParamType::Obj(set) => {
                    let set = LitexToLeanObjectIr::lower(set).map_err(|message| {
                        litex_to_lean_error(&proposition.line_file(), message)
                    })?;
                    context
                        .type_context
                        .membership_element_carrier(&set)
                        .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?
                }
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "Litex-to-Lean native ABI does not yet infer a carrier for a concrete generic-set existential witness",
                    ));
                }
            };
            context.type_context.expect_object(witness, carrier.clone());
            witness_carriers.push(carrier);
        }
        if let Some(common_carrier) = witness_carriers.first() {
            if witness_carriers
                .iter()
                .all(|carrier| carrier == common_carrier)
            {
                for premise in premises {
                    expect_binary_fact_carrier(
                        &premise.proposition,
                        common_carrier,
                        &mut context.type_context,
                    );
                }
            }
        }

        let mut lines = vec!["by".to_string()];
        for step in steps {
            lines.extend(self.lean_local_statement(step, context)?);
        }
        let mut requirement_names = Vec::with_capacity(parameter_requirements.len());
        for requirement in parameter_requirements {
            let (name, requirement_lines) = self.lean_named_local_fact(requirement, context)?;
            lines.extend(requirement_lines);
            requirement_names.push(name);
        }
        let mut body_names = Vec::with_capacity(premises.len());
        for premise in premises {
            let (name, premise_lines) = self.lean_named_local_fact(premise, context)?;
            lines.extend(premise_lines);
            body_names.push(name);
        }

        let mut constructor_parts = Vec::new();
        let mut requirement_index = 0;
        for (witness, param_type) in witnesses.iter().zip(param_types.iter()) {
            LitexToLeanObjectIr::lower(witness)
                .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
            constructor_parts.push(lean_obj_with_context(witness, &context.type_context)?);
            if !matches!(param_type, ParamType::Set(_)) {
                validate_exist_introduction_requirement(
                    witness,
                    param_type,
                    &parameter_requirements[requirement_index].proposition,
                )?;
                constructor_parts.push(requirement_names[requirement_index].clone());
                requirement_index += 1;
            }
        }
        if body_names.is_empty() {
            constructor_parts.push("True.intro".to_string());
        } else {
            constructor_parts.extend(body_names);
        }
        lines.push(format!("  exact ⟨{}⟩", constructor_parts.join(", ")));
        Ok(lines.join("\n"))
    }

    fn lean_registered_rule_application(
        &mut self,
        proposition: &Fact,
        application: &LitexToLeanRegisteredRuleApplicationIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if parameter_requirements.len() != application.parameter_requirement_count
            || premises.len() != application.premise_count
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "registered local builtin `{}` expected {} parameter requirements and {} premises but received {} and {}",
                    application.rule_id.as_str(),
                    application.parameter_requirement_count,
                    application.premise_count,
                    parameter_requirements.len(),
                    premises.len()
                ),
            ));
        }
        let adapter =
            local_builtin_adapter(&application.rule_id, &application.semantic_fingerprint)
                .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        self.required_local_builtin_rules
            .insert(application.rule_id.clone());

        let mut arguments = Vec::with_capacity(
            application.bindings.len() + parameter_requirements.len() + premises.len(),
        );
        for binding in &application.bindings {
            let carrier = param_type_object_carrier(&binding.param_type)?;
            arguments.push(lean_obj_ir_with_expected(
                &binding.object,
                &carrier,
                &context.type_context,
                false,
            )?);
        }

        let mut lines = vec!["by".to_string()];
        for child in parameter_requirements.iter().chain(premises.iter()) {
            let (name, child_lines) = self.lean_named_local_fact(child, context)?;
            lines.extend(child_lines);
            arguments.push(name);
        }
        lines.push(format!(
            "  exact _root_.Litex.BuiltinRules.{} {}",
            adapter.theorem_name,
            arguments.join(" ")
        ));
        Ok(lines.join("\n"))
    }

    fn lean_builtin_rule_application(
        &mut self,
        proposition: &Fact,
        rule: &LitexToLeanBuiltinRuleIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        match rule {
            LitexToLeanBuiltinRuleIr::DivNotEqualZero(evidence) => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "div-nonzero builtin evidence does not accept parameter requirements",
                    ));
                }
                self.lean_div_not_equal_zero_builtin(proposition, evidence, premises, context)
            }
            LitexToLeanBuiltinRuleIr::Arithmetic(rule) => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "arithmetic builtin evidence does not accept parameter requirements",
                    ));
                }
                self.lean_arithmetic_builtin_rule(proposition, *rule, premises, context)
            }
            LitexToLeanBuiltinRuleIr::IntegerMembershipClosure(rule) => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "integer-membership closure evidence does not accept parameter requirements",
                    ));
                }
                self.lean_integer_membership_closure(proposition, *rule, premises, context)
            }
            LitexToLeanBuiltinRuleIr::NotEqualSymmetry => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "not-equality symmetry evidence does not accept parameter requirements",
                    ));
                }
                self.lean_not_equal_symmetry_builtin(proposition, premises, context)
            }
            LitexToLeanBuiltinRuleIr::NotEqualFromStrictOrder => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "strict-order not-equality evidence does not accept parameter requirements",
                    ));
                }
                self.lean_not_equal_from_strict_order_builtin(proposition, premises, context)
            }
            LitexToLeanBuiltinRuleIr::SetRelationDuality(rule) => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set-relation duality evidence does not accept parameter requirements",
                    ));
                }
                self.lean_set_relation_duality_builtin(proposition, *rule, premises, context)
            }
            LitexToLeanBuiltinRuleIr::Set(rule) => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set builtin evidence does not accept parameter requirements",
                    ));
                }
                self.lean_set_builtin_rule(proposition, *rule, premises, context)
            }
            LitexToLeanBuiltinRuleIr::AbsoluteValue(rule) => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value builtin evidence does not accept parameter requirements",
                    ));
                }
                self.lean_absolute_value_builtin_rule(proposition, *rule, premises, context)
            }
            LitexToLeanBuiltinRuleIr::PrimeU64Reflection => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "prime reflection evidence does not accept parameter requirements",
                    ));
                }
                lean_prime_u64_reflection(proposition, premises)
            }
            LitexToLeanBuiltinRuleIr::CoprimeNaturalReflection => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "coprime reflection evidence does not accept parameter requirements",
                    ));
                }
                lean_coprime_natural_reflection(proposition, premises)
            }
            LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "standard-set membership projection evidence does not accept parameter requirements",
                    ));
                }
                self.lean_standard_set_membership_projection(proposition, premises, context)
            }
            LitexToLeanBuiltinRuleIr::PositiveRealMembership => {
                if !parameter_requirements.is_empty() {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "positive-real membership evidence does not accept parameter requirements",
                    ));
                }
                self.lean_positive_real_membership(proposition, premises, context)
            }
        }
    }

    fn lean_integer_membership_closure(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanIntegerMembershipClosureBuiltinRuleIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "integer-membership closure evidence requires a membership target",
            ));
        };
        if !matches!(&target.set, Obj::StandardSet(StandardSet::Z)) {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "integer-membership closure evidence requires target set Z",
            ));
        }
        let operands: [&Obj; 2] = match (rule, &target.element) {
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Add, Obj::Add(value)) => {
                [value.left.as_ref(), value.right.as_ref()]
            }
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(value)) => {
                [value.left.as_ref(), value.right.as_ref()]
            }
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(value)) => {
                [value.left.as_ref(), value.right.as_ref()]
            }
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mod, Obj::Mod(value)) => {
                [value.left.as_ref(), value.right.as_ref()]
            }
            _ => {
                return Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "integer-membership closure rule does not match the target operator",
                ));
            }
        };
        if premises.len() != operands.len() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "integer-membership closure evidence expected 2 premises but received {}",
                    premises.len()
                ),
            ));
        }
        for (premise, operand) in premises.iter().zip(operands) {
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premise.proposition else {
                return Err(litex_to_lean_error(
                    &premise.proposition.line_file(),
                    "integer-membership closure premise is not a membership fact",
                ));
            };
            if !matches!(&membership.set, Obj::StandardSet(StandardSet::Z))
                || obj_equality_key(&membership.element) != obj_equality_key(operand)
            {
                return Err(litex_to_lean_error(
                    &premise.proposition.line_file(),
                    "integer-membership closure premise does not match its ordered operand in Z",
                ));
            }
        }

        let mut lines = vec!["by".to_string()];
        for premise in premises {
            let (_, premise_lines) = self.lean_named_local_fact(premise, context)?;
            lines.extend(premise_lines);
        }
        // Standard Z is emitted as `Litex.StandardSets.Z`; after validating and
        // replaying both checked source premises, its membership goal reduces
        // definitionally to True.
        lines.push("  change True".to_string());
        lines.push("  trivial".to_string());
        Ok(lines.join("\n"))
    }

    fn lean_standard_set_membership_projection(
        &mut self,
        proposition: &Fact,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "standard-set membership projection evidence expected 1 premise but received {}",
                    premises.len()
                ),
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "standard-set membership projection evidence requires a membership target",
            ));
        };
        let Fact::AtomicFact(AtomicFact::InFact(source)) = &premises[0].proposition else {
            return Err(litex_to_lean_error(
                &premises[0].proposition.line_file(),
                "standard-set membership projection evidence requires a membership premise",
            ));
        };
        let Obj::StandardSet(source_set) = &source.set else {
            return Err(litex_to_lean_error(
                &premises[0].proposition.line_file(),
                "standard-set membership projection premise must use a standard set",
            ));
        };
        let Obj::StandardSet(target_set) = &target.set else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "standard-set membership projection target must use a standard set",
            ));
        };
        if obj_equality_key(&source.element) != obj_equality_key(&target.element) {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "standard-set membership projection source and target objects do not match",
            ));
        }
        if !source_set.is_subset_eq(target_set) {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "standard-set membership projection does not permit {} -> {}",
                    source_set, target_set
                ),
            ));
        }

        let (premise_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.insert(0, "by".to_string());
        if source_set == target_set {
            lines.push(format!("  exact {}", premise_name));
            return Ok(lines.join("\n"));
        }

        let element_ir = LitexToLeanObjectIr::lower(&source.element)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        let source_carrier = LitexToLeanStandardSetIr::from(source_set).element_carrier();
        let target_carrier = LitexToLeanStandardSetIr::from(target_set).element_carrier();
        let source_element =
            lean_obj_ir_with_expected(&element_ir, &source_carrier, &context.type_context, true)?;
        let target_element =
            lean_obj_ir_with_expected(&element_ir, &target_carrier, &context.type_context, true)?;
        let predicate_text = |set: &StandardSet, element: &str| match set {
            StandardSet::NPos | StandardSet::QPos | StandardSet::RPos => {
                Some(format!("0 < {}", element))
            }
            StandardSet::ZNeg | StandardSet::QNeg | StandardSet::RNeg => {
                Some(format!("{} < 0", element))
            }
            StandardSet::ZStar | StandardSet::QStar | StandardSet::RStar | StandardSet::CStar => {
                Some(format!("{} ≠ 0", element))
            }
            StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C => {
                None
            }
        };

        match target_set {
            StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C => {
                lines.push("  exact Set.mem_univ _".to_string())
            }
            StandardSet::NPos
            | StandardSet::QPos
            | StandardSet::RPos
            | StandardSet::ZNeg
            | StandardSet::QNeg
            | StandardSet::RNeg => {
                let source_predicate = predicate_text(source_set, &source_element).ok_or_else(|| {
                    litex_to_lean_error(
                        &proposition.line_file(),
                        format!(
                            "standard-set membership projection has no predicate adapter for {} -> {}",
                            source_set, target_set
                        ),
                    )
                })?;
                let target_predicate = predicate_text(target_set, &target_element)
                    .expect("refined target must have a predicate");
                let predicate_name = self.next_proof_fact_name(context);
                lines.push(format!(
                    "  have {} : {} := by",
                    predicate_name, source_predicate
                ));
                lines.push(format!("    simpa using {}", premise_name));
                lines.push(format!("  change {}", target_predicate));
                lines.push(format!("  exact_mod_cast {}", predicate_name));
            }
            StandardSet::ZStar | StandardSet::QStar | StandardSet::RStar | StandardSet::CStar => {
                let source_predicate = predicate_text(source_set, &source_element).ok_or_else(|| {
                    litex_to_lean_error(
                        &proposition.line_file(),
                        format!(
                            "standard-set membership projection has no predicate adapter for {} -> {}",
                            source_set, target_set
                        ),
                    )
                })?;
                let target_predicate = predicate_text(target_set, &target_element)
                    .expect("nonzero target must have a predicate");
                let predicate_name = self.next_proof_fact_name(context);
                lines.push(format!(
                    "  have {} : {} := by",
                    predicate_name, source_predicate
                ));
                lines.push(format!("    simpa using {}", premise_name));
                let nonzero_name = match source_set {
                    StandardSet::NPos | StandardSet::QPos | StandardSet::RPos => {
                        let name = self.next_proof_fact_name(context);
                        lines.push(format!("  have {} := ne_of_gt {}", name, predicate_name));
                        name
                    }
                    StandardSet::ZNeg | StandardSet::QNeg | StandardSet::RNeg => {
                        let name = self.next_proof_fact_name(context);
                        lines.push(format!("  have {} := ne_of_lt {}", name, predicate_name));
                        name
                    }
                    StandardSet::ZStar
                    | StandardSet::QStar
                    | StandardSet::RStar
                    | StandardSet::CStar => predicate_name,
                    _ => {
                        return Err(litex_to_lean_error(
                            &proposition.line_file(),
                            format!(
                                "standard-set membership projection has no nonzero proof adapter for {} -> {}",
                                source_set, target_set
                            ),
                        ));
                    }
                };
                lines.push(format!("  change {}", target_predicate));
                lines.push(format!("  exact_mod_cast {}", nonzero_name));
            }
        }
        Ok(lines.join("\n"))
    }

    fn lean_set_builtin_rule(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanSetBuiltinRuleIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        use LitexToLeanSetBuiltinRuleIr::*;

        let expected_premises = match rule {
            UnionCommutative | UnionAssociative | UnionIdempotent | UnionEmptyIdentity
            | IntersectCommutative | IntersectAssociative => 0,
            UnionMembershipLeft
            | UnionMembershipRight
            | IntersectNonMembershipLeft
            | IntersectNonMembershipRight => 1,
            IntersectMembershipBoth | SetMinusMembership => 2,
        };
        if premises.len() != expected_premises {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "set builtin {:?} expected {} premises but received {}",
                    rule,
                    expected_premises,
                    premises.len()
                ),
            ));
        }

        match rule {
            UnionCommutative | UnionAssociative | UnionIdempotent | UnionEmptyIdentity
            | IntersectCommutative | IntersectAssociative => {
                if !set_equality_matches_builtin_rule(proposition, rule) {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        format!("set builtin {:?} target has the wrong shape", rule),
                    ));
                }
                let simp_lemmas = match rule {
                    UnionCommutative => "[or_comm]",
                    UnionAssociative => "[or_assoc]",
                    IntersectCommutative => "[and_comm]",
                    IntersectAssociative => "[and_assoc]",
                    UnionIdempotent | UnionEmptyIdentity => "",
                    _ => unreachable!(),
                };
                Ok(format!("by\n  ext x\n  simp {}", simp_lemmas))
            }
            UnionMembershipLeft | UnionMembershipRight => {
                let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "union membership evidence requires an In target",
                    ));
                };
                let Fact::AtomicFact(AtomicFact::InFact(premise)) = &premises[0].proposition else {
                    return Err(litex_to_lean_error(
                        &premises[0].proposition.line_file(),
                        "union membership evidence requires an In premise",
                    ));
                };
                let Obj::Union(union) = &target.set else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "union membership evidence requires a union target",
                    ));
                };
                let expected_set = match rule {
                    UnionMembershipLeft => union.left.as_ref(),
                    UnionMembershipRight => union.right.as_ref(),
                    _ => unreachable!(),
                };
                if obj_equality_key(&target.element) != obj_equality_key(&premise.element)
                    || obj_equality_key(expected_set) != obj_equality_key(&premise.set)
                {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "union membership premise does not match its selected side",
                    ));
                }
                let (premise_name, mut lines) =
                    self.lean_named_local_fact(&premises[0], context)?;
                lines.insert(0, "by".to_string());
                lines.push("  rw [Set.mem_union]".to_string());
                lines.push(format!(
                    "  exact Or.{} {}",
                    if matches!(rule, UnionMembershipLeft) {
                        "inl"
                    } else {
                        "inr"
                    },
                    premise_name
                ));
                Ok(lines.join("\n"))
            }
            IntersectMembershipBoth => {
                let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "intersection membership evidence requires an In target",
                    ));
                };
                let Obj::Intersect(intersect) = &target.set else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "intersection membership evidence requires an intersection target",
                    ));
                };
                let (left_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
                let (right_name, right_lines) =
                    self.lean_named_local_fact(&premises[1], context)?;
                lines.extend(right_lines);
                for (premise, expected_set) in [
                    (&premises[0].proposition, intersect.left.as_ref()),
                    (&premises[1].proposition, intersect.right.as_ref()),
                ] {
                    let Fact::AtomicFact(AtomicFact::InFact(member)) = premise else {
                        return Err(litex_to_lean_error(
                            &proposition.line_file(),
                            "intersection membership evidence requires two In premises",
                        ));
                    };
                    if obj_equality_key(&member.element) != obj_equality_key(&target.element)
                        || obj_equality_key(&member.set) != obj_equality_key(expected_set)
                    {
                        return Err(litex_to_lean_error(
                            &proposition.line_file(),
                            "intersection membership premise does not match its side",
                        ));
                    }
                }
                lines.insert(0, "by".to_string());
                lines.push("  rw [Set.mem_inter_iff]".to_string());
                lines.push(format!("  exact ⟨{}, {}⟩", left_name, right_name));
                Ok(lines.join("\n"))
            }
            IntersectNonMembershipLeft | IntersectNonMembershipRight => {
                let Fact::AtomicFact(AtomicFact::NotInFact(target)) = proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "intersection non-membership evidence requires a NotIn target",
                    ));
                };
                let Obj::Intersect(intersect) = &target.set else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "intersection non-membership evidence requires an intersection target",
                    ));
                };
                let Fact::AtomicFact(AtomicFact::NotInFact(premise)) = &premises[0].proposition
                else {
                    return Err(litex_to_lean_error(
                        &premises[0].proposition.line_file(),
                        "intersection non-membership evidence requires a NotIn premise",
                    ));
                };
                let expected_set = match rule {
                    IntersectNonMembershipLeft => intersect.left.as_ref(),
                    IntersectNonMembershipRight => intersect.right.as_ref(),
                    _ => unreachable!(),
                };
                if obj_equality_key(&premise.element) != obj_equality_key(&target.element)
                    || obj_equality_key(&premise.set) != obj_equality_key(expected_set)
                {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "intersection non-membership premise does not match its side",
                    ));
                }
                let (premise_name, mut lines) =
                    self.lean_named_local_fact(&premises[0], context)?;
                lines.insert(0, "by".to_string());
                lines.push("  rw [Set.mem_inter_iff]".to_string());
                lines.push(format!(
                    "  exact fun h => {} h.{}",
                    premise_name,
                    if matches!(rule, IntersectNonMembershipLeft) {
                        "1"
                    } else {
                        "2"
                    }
                ));
                Ok(lines.join("\n"))
            }
            SetMinusMembership => {
                let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set-minus membership evidence requires an In target",
                    ));
                };
                let Obj::SetMinus(set_minus) = &target.set else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set-minus membership evidence requires a set-minus target",
                    ));
                };
                let (left_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
                let (right_name, right_lines) =
                    self.lean_named_local_fact(&premises[1], context)?;
                lines.extend(right_lines);
                let Fact::AtomicFact(AtomicFact::InFact(left)) = &premises[0].proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set-minus membership requires an In left premise",
                    ));
                };
                let Fact::AtomicFact(AtomicFact::NotInFact(right)) = &premises[1].proposition
                else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set-minus membership requires a NotIn right premise",
                    ));
                };
                if obj_equality_key(&left.element) != obj_equality_key(&target.element)
                    || obj_equality_key(&left.set) != obj_equality_key(&set_minus.left)
                    || obj_equality_key(&right.element) != obj_equality_key(&target.element)
                    || obj_equality_key(&right.set) != obj_equality_key(&set_minus.right)
                {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "set-minus membership premises do not match the target",
                    ));
                }
                lines.insert(0, "by".to_string());
                lines.push("  rw [Set.mem_diff]".to_string());
                lines.push(format!("  exact ⟨{}, {}⟩", left_name, right_name));
                Ok(lines.join("\n"))
            }
        }
    }

    fn lean_absolute_value_builtin_rule(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanAbsoluteValueBuiltinRuleIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        use LitexToLeanAbsoluteValueBuiltinRuleIr::*;
        let expected = match rule {
            Product => 0,
            _ => 1,
        };
        if premises.len() != expected {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "absolute-value builtin {:?} expected {} premises but received {}",
                    rule,
                    expected,
                    premises.len()
                ),
            ));
        }
        match rule {
            Product => {
                if !abs_product_equality_shape(proposition) {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value product target has the wrong shape",
                    ));
                }
                Ok("by\n  simp only [abs_mul]".to_string())
            }
            NonnegativeIdentity | NonpositiveNegation => {
                let Fact::AtomicFact(AtomicFact::EqualFact(target)) = proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value equality evidence requires an equality target",
                    ));
                };
                let (arg, reversed) = abs_identity_target(target, rule)?;
                let Fact::AtomicFact(premise_fact) = &premises[0].proposition else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value identity evidence requires an order premise",
                    ));
                };
                let (premise_name, mut lines) =
                    self.lean_named_local_fact(&premises[0], context)?;
                let proof = match (rule, premise_fact) {
                    (NonnegativeIdentity, AtomicFact::LessEqualFact(f))
                        if f.left.to_string() == "0"
                            && obj_equality_key(&f.right) == obj_equality_key(arg) =>
                    {
                        format!("abs_of_nonneg {}", premise_name)
                    }
                    (NonnegativeIdentity, AtomicFact::LessFact(f))
                        if f.left.to_string() == "0"
                            && obj_equality_key(&f.right) == obj_equality_key(arg) =>
                    {
                        format!("abs_of_nonneg (le_of_lt {})", premise_name)
                    }
                    (NonpositiveNegation, AtomicFact::LessEqualFact(f))
                        if obj_equality_key(&f.left) == obj_equality_key(arg)
                            && f.right.to_string() == "0" =>
                    {
                        format!("abs_of_nonpos {}", premise_name)
                    }
                    (NonpositiveNegation, AtomicFact::LessFact(f))
                        if obj_equality_key(&f.left) == obj_equality_key(arg)
                            && f.right.to_string() == "0" =>
                    {
                        format!("abs_of_nonpos (le_of_lt {})", premise_name)
                    }
                    _ => {
                        return Err(litex_to_lean_error(
                            &proposition.line_file(),
                            "absolute-value identity premise does not match the target",
                        ))
                    }
                };
                lines.insert(0, "by".to_string());
                let proof = if reversed {
                    format!("({proof}).symm")
                } else {
                    proof
                };
                lines.push(format!("  exact {proof}"));
                Ok(lines.join("\n"))
            }
            PositiveFromNonzero => {
                let (arg, reversed) = abs_positive_target(proposition)?;
                if reversed {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value positivity target must be 0 < abs(x)",
                    ));
                }
                let Fact::AtomicFact(AtomicFact::NotEqualFact(premise)) = &premises[0].proposition
                else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value positivity evidence requires a not-equality premise",
                    ));
                };
                if obj_equality_key(&premise.left) != obj_equality_key(arg)
                    || premise.right.to_string() != "0"
                {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "absolute-value positivity premise does not match the target",
                    ));
                }
                let (premise_name, mut lines) =
                    self.lean_named_local_fact(&premises[0], context)?;
                lines.insert(0, "by".to_string());
                lines.push(format!("  exact abs_pos.mpr {}", premise_name));
                Ok(lines.join("\n"))
            }
        }
    }

    fn lean_not_equal_symmetry_builtin(
        &mut self,
        proposition: &Fact,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "not-equality symmetry evidence expected 1 premise but received {}",
                    premises.len()
                ),
            ));
        }
        let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "not-equality symmetry evidence requires a not-equality target",
            ));
        };
        let Fact::AtomicFact(AtomicFact::NotEqualFact(premise)) = &premises[0].proposition else {
            return Err(litex_to_lean_error(
                &premises[0].proposition.line_file(),
                "not-equality symmetry evidence requires a not-equality premise",
            ));
        };
        if obj_equality_key(&target.left) != obj_equality_key(&premise.right)
            || obj_equality_key(&target.right) != obj_equality_key(&premise.left)
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "not-equality symmetry premise is not the reverse of its target",
            ));
        }

        let (premise_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.insert(0, "by".to_string());
        lines.push(format!("  exact Ne.symm {}", premise_name));
        Ok(lines.join("\n"))
    }

    fn lean_not_equal_from_strict_order_builtin(
        &mut self,
        proposition: &Fact,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 3 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "strict-order not-equality evidence expected 3 premises but received {}",
                    premises.len()
                ),
            ));
        }
        let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "strict-order not-equality evidence requires a not-equality target",
            ));
        };
        for (index, expected_object) in [&target.left, &target.right].into_iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premises[index].proposition
            else {
                return Err(litex_to_lean_error(
                    &premises[index].proposition.line_file(),
                    "strict-order not-equality carrier premise must be a membership fact",
                ));
            };
            if obj_equality_key(&membership.element) != obj_equality_key(expected_object)
                || !matches!(&membership.set, Obj::StandardSet(StandardSet::R))
            {
                return Err(litex_to_lean_error(
                    &premises[index].proposition.line_file(),
                    "strict-order not-equality carrier premise does not match the target real operand",
                ));
            }
        }
        let (order_left, order_right) = match &premises[2].proposition {
            Fact::AtomicFact(AtomicFact::LessFact(order)) => (&order.left, &order.right),
            Fact::AtomicFact(AtomicFact::GreaterFact(order)) => (&order.left, &order.right),
            _ => {
                return Err(litex_to_lean_error(
                    &premises[2].proposition.line_file(),
                    "strict-order not-equality final premise must be `<` or `>`",
                ))
            }
        };
        let direct = obj_equality_key(order_left) == obj_equality_key(&target.left)
            && obj_equality_key(order_right) == obj_equality_key(&target.right);
        let reverse = obj_equality_key(order_left) == obj_equality_key(&target.right)
            && obj_equality_key(order_right) == obj_equality_key(&target.left);
        if !direct && !reverse {
            return Err(litex_to_lean_error(
                &premises[2].proposition.line_file(),
                "strict-order not-equality comparison does not use the target operands",
            ));
        }

        let mut lines = vec!["by".to_string()];
        for carrier in &premises[..2] {
            let (_, carrier_lines) = self.lean_named_local_fact(carrier, context)?;
            lines.extend(carrier_lines);
        }
        let (order_name, order_lines) = self.lean_named_local_fact(&premises[2], context)?;
        lines.extend(order_lines);
        lines.push("  intro litex_equal".to_string());
        lines.push(format!("  rw [litex_equal] at {order_name}"));
        lines.push(format!("  exact (lt_irrefl _ {order_name})"));
        Ok(lines.join("\n"))
    }

    fn lean_set_relation_duality_builtin(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanSetRelationDualityBuiltinRuleIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "set-relation duality evidence expected 1 premise but received {}",
                    premises.len()
                ),
            ));
        }
        let Fact::AtomicFact(target) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "set-relation duality evidence requires an atomic target",
            ));
        };
        let Fact::AtomicFact(premise) = &premises[0].proposition else {
            return Err(litex_to_lean_error(
                &premises[0].proposition.line_file(),
                "set-relation duality evidence requires an atomic premise",
            ));
        };

        let aligned = match (rule, target, premise) {
            (
                LitexToLeanSetRelationDualityBuiltinRuleIr::SubsetFromSuperset,
                AtomicFact::SubsetFact(target),
                AtomicFact::SupersetFact(premise),
            )
            | (
                LitexToLeanSetRelationDualityBuiltinRuleIr::SupersetFromSubset,
                AtomicFact::SupersetFact(premise),
                AtomicFact::SubsetFact(target),
            ) => {
                obj_equality_key(&target.left) == obj_equality_key(&premise.right)
                    && obj_equality_key(&target.right) == obj_equality_key(&premise.left)
            }
            (
                LitexToLeanSetRelationDualityBuiltinRuleIr::NotSubsetFromNotSuperset,
                AtomicFact::NotSubsetFact(target),
                AtomicFact::NotSupersetFact(premise),
            )
            | (
                LitexToLeanSetRelationDualityBuiltinRuleIr::NotSupersetFromNotSubset,
                AtomicFact::NotSupersetFact(premise),
                AtomicFact::NotSubsetFact(target),
            ) => {
                obj_equality_key(&target.left) == obj_equality_key(&premise.right)
                    && obj_equality_key(&target.right) == obj_equality_key(&premise.left)
            }
            _ => false,
        };
        if !aligned {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "set-relation duality premise is not the reversed relation named by its evidence",
            ));
        }

        let (premise_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.insert(0, "by".to_string());
        lines.push(format!("  exact {}", premise_name));
        Ok(lines.join("\n"))
    }

    fn lean_positive_real_membership(
        &mut self,
        proposition: &Fact,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "positive-real membership evidence expected 1 premise but received {}",
                    premises.len()
                ),
            ));
        }
        let positive_object = match proposition {
            Fact::AtomicFact(AtomicFact::LessFact(fact)) if fact.left.to_string() == "0" => {
                &fact.right
            }
            Fact::AtomicFact(AtomicFact::GreaterFact(fact)) if fact.right.to_string() == "0" => {
                &fact.left
            }
            _ => {
                return Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "positive-real membership evidence requires a strict positivity target",
                ));
            }
        };
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premises[0].proposition else {
            return Err(litex_to_lean_error(
                &premises[0].proposition.line_file(),
                "positive-real membership evidence requires an `R+` membership premise",
            ));
        };
        if !matches!(membership.set, Obj::StandardSet(StandardSet::RPos))
            || obj_equality_key(&membership.element) != obj_equality_key(positive_object)
        {
            return Err(litex_to_lean_error(
                &premises[0].proposition.line_file(),
                "positive-real membership evidence premise does not match its target object",
            ));
        }

        let (premise_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.insert(0, "by".to_string());
        lines.push(format!("  simpa using {}", premise_name));
        Ok(lines.join("\n"))
    }

    fn lean_arithmetic_builtin_rule(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanArithmeticBuiltinRuleIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let (target_class, premise_classes) = arithmetic_builtin_contract(rule);
        if lean_fact_class(proposition) != Some(target_class) {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "arithmetic builtin {:?} has the wrong target fact family",
                    rule
                ),
            ));
        }
        if premises.len() != premise_classes.len() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "arithmetic builtin {:?} expected {} premises but received {}",
                    rule,
                    premise_classes.len(),
                    premises.len()
                ),
            ));
        }
        for (index, (premise, expected)) in premises.iter().zip(premise_classes.iter()).enumerate()
        {
            let actual = lean_fact_class(&premise.proposition);
            if actual != Some(*expected) {
                return Err(litex_to_lean_error(
                    &premise.proposition.line_file(),
                    format!(
                        "arithmetic builtin {:?} premise {} expected {:?}, but `{}` has {:?}",
                        rule,
                        index + 1,
                        expected,
                        premise.proposition,
                        actual
                    ),
                ));
            }
        }

        let mut lines = vec!["by".to_string()];
        let mut premise_names = Vec::with_capacity(premises.len());
        for premise in premises {
            let (local_name, local_lines) = self.lean_named_local_fact(premise, context)?;
            lines.extend(local_lines);
            premise_names.push(local_name);
        }
        let proof = match rule {
            LitexToLeanArithmeticBuiltinRuleIr::MulNonnegative => {
                format!("mul_nonneg {} {}", premise_names[0], premise_names[1])
            }
            LitexToLeanArithmeticBuiltinRuleIr::MulPositive => {
                format!("mul_pos {} {}", premise_names[0], premise_names[1])
            }
            LitexToLeanArithmeticBuiltinRuleIr::DivNonnegative => format!(
                "div_nonneg {} (le_of_lt {})",
                premise_names[0], premise_names[1]
            ),
            LitexToLeanArithmeticBuiltinRuleIr::DivPositive => {
                format!("div_pos {} {}", premise_names[0], premise_names[1])
            }
            _ => format!("linarith only [{}]", premise_names.join(", ")),
        };
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact_with_context(proposition, &context.type_context)?
        ));
        if proof.starts_with("linarith") {
            lines.push(format!("    {}", proof));
        } else {
            lines.push(format!("    exact {}", proof));
        }
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_div_not_equal_zero_builtin(
        &mut self,
        proposition: &Fact,
        evidence: &LitexToLeanDivNotEqualZeroIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 2 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "div-nonzero builtin evidence expected 2 premises but received {}",
                    premises.len()
                ),
            ));
        }

        let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "div-nonzero builtin evidence was attached to a non-inequality",
            ));
        };
        let (quotient, zero) = match evidence.orientation {
            LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnLeft => {
                let Obj::Div(quotient) = &target.left else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "div-nonzero evidence expected a quotient on the left",
                    ));
                };
                (quotient, &target.right)
            }
            LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnRight => {
                let Obj::Div(quotient) = &target.right else {
                    return Err(litex_to_lean_error(
                        &proposition.line_file(),
                        "div-nonzero evidence expected a quotient on the right",
                    ));
                };
                (quotient, &target.left)
            }
        };
        if !matches!(zero, Obj::Number(number) if number.normalized_value == "0") {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "div-nonzero evidence requires a literal zero target",
            ));
        }
        if obj_equality_key(quotient.left.as_ref()) != obj_equality_key(&evidence.numerator)
            || obj_equality_key(quotient.right.as_ref()) != obj_equality_key(&evidence.denominator)
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "div-nonzero evidence bindings disagree with the target quotient",
            ));
        }

        let expected_operands = [&evidence.numerator, &evidence.denominator];
        for (index, premise) in premises.iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = &premise.proposition else {
                return Err(litex_to_lean_error(
                    &premise.proposition.line_file(),
                    format!("div-nonzero premise {} is not an inequality", index + 1),
                ));
            };
            if obj_equality_key(&nonzero.left) != obj_equality_key(expected_operands[index])
                || !matches!(
                    &nonzero.right,
                    Obj::Number(number) if number.normalized_value == "0"
                )
            {
                return Err(litex_to_lean_error(
                    &premise.proposition.line_file(),
                    format!(
                        "div-nonzero premise {} disagrees with its recorded binding",
                        index + 1
                    ),
                ));
            }
        }

        let mut lines = vec!["by".to_string()];
        let mut premise_names = Vec::with_capacity(premises.len());
        for premise in premises {
            let (local_name, local_lines) = self.lean_named_local_fact(premise, context)?;
            lines.extend(local_lines);
            premise_names.push(local_name);
        }
        let forward_proof = format!("div_ne_zero {} {}", premise_names[0], premise_names[1]);
        let proof = match evidence.orientation {
            LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnLeft => forward_proof,
            LitexToLeanNonzeroExpressionOrientationIr::ExpressionOnRight => {
                format!("Ne.symm ({})", forward_proof)
            }
        };
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact_with_context(proposition, &context.type_context)?
        ));
        lines.push(format!("    exact {}", proof));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_known_forall_instantiation(
        &mut self,
        proposition: &Fact,
        source_fact_id: FactId,
        arguments: &[LitexToLeanKnownForallArgumentIr],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if arguments.len() != parameter_requirements.len() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "known-forall application received {} arguments but {} parameter requirements",
                    arguments.len(),
                    parameter_requirements.len()
                ),
            ));
        }

        let source = self.available_fact_name(source_fact_id, proposition, context)?;
        let mut lines = vec!["by".to_string()];
        let mut argument_names = Vec::with_capacity(arguments.len());
        let mut parameter_requirement_names = Vec::new();
        for (argument, requirement) in arguments.iter().zip(parameter_requirements.iter()) {
            let local_name = self.next_proof_arg_name(context);
            let argument_ir = LitexToLeanObjectIr::lower(&argument.argument)
                .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
            let expected = param_type_object_carrier(&argument.param_type)?;
            let lean_argument =
                lean_obj_ir_with_expected(&argument_ir, &expected, &context.type_context, false)?;
            let lean_param_type = lean_ir_param_type(&argument.param_type, &context.type_context)?;
            lines.push(format!(
                "  -- Litex parameter requirement for `{}`: {} : {}",
                argument.param, lean_argument, lean_param_type
            ));
            lines.push(format!(
                "  let {} : {} := {}",
                local_name, lean_param_type, lean_argument
            ));
            argument_names.push(local_name);
            if !matches!(argument.param_type, LitexToLeanParameterTypeIr::Set { .. }) {
                let (requirement_name, requirement_lines) =
                    self.lean_named_local_fact(requirement, context)?;
                lines.extend(requirement_lines);
                parameter_requirement_names.push(requirement_name);
            }
        }

        let mut premise_names = Vec::with_capacity(premises.len());
        for premise in premises {
            let (local_name, local_lines) = self.lean_named_local_fact(premise, context)?;
            lines.extend(local_lines);
            premise_names.push(local_name);
        }

        let result_name = self.next_proof_fact_name(context);
        let mut terms = vec![source];
        terms.extend(argument_names);
        terms.extend(parameter_requirement_names);
        terms.extend(premise_names);
        lines.push(format!(
            "  have {} : {} := {}",
            result_name,
            lean_fact_with_context(proposition, &context.type_context)?,
            terms.join(" ")
        ));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_normalization_from_premise(
        &mut self,
        proposition: &Fact,
        premise: &LitexToLeanFactIr,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let mut lines = vec!["by".to_string()];
        let (source_name, source_lines) = self.lean_named_local_fact(premise, context)?;
        lines.extend(source_lines);
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact_with_context(proposition, &context.type_context)?
        ));
        lines.push(format!(
            "    convert {} using 1 <;> {}",
            source_name,
            rational_fact_normalization_tactic(&premise.proposition, proposition, context)?
        ));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_definition_projection(
        &mut self,
        proposition: &Fact,
        definition: &str,
        expected_source: &Fact,
        expected_target: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection evidence requires no parameter requirements and exactly one source premise",
            ));
        }
        if proposition.to_string() != expected_target.to_string() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection target disagrees with its retained expected proposition",
            ));
        }
        if premises[0].proposition.to_string() != expected_source.to_string() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection source disagrees with its retained expected proposition",
            ));
        }
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(source)) = expected_source else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection source must be a positive proposition fact",
            ));
        };
        let Fact::ExistFact(target) = expected_target else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection target must be an existential fact",
            ));
        };
        if !target.is_plain_exist() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection target must be a positive `exist` fact",
            ));
        }
        let predicate_name = source.predicate.to_string();
        let local_predicate_name = predicate_name
            .rsplit_once(MOD_SIGN)
            .map(|(_, local_name)| local_name)
            .unwrap_or(predicate_name.as_str());
        if local_predicate_name != definition {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-projection rule names a different definition from its source proposition",
            ));
        }
        lean_fact(expected_source)?;
        lean_fact(expected_target)?;

        let mut lines = vec!["by".to_string()];
        let (source_name, source_lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.extend(source_lines);
        lines.push(format!(
            "  simpa only [{}] using {}",
            lean_name(definition),
            source_name
        ));
        Ok(lines.join("\n"))
    }

    fn lean_definition_introduction(
        &mut self,
        proposition: &Fact,
        definition: &str,
        expected_source: &Fact,
        expected_target: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction evidence requires no parameter requirements and exactly one source premise",
            ));
        }
        if proposition.to_string() != expected_target.to_string() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction target disagrees with its retained expected proposition",
            ));
        }
        if premises[0].proposition.to_string() != expected_source.to_string() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction source disagrees with its retained expected proposition",
            ));
        }
        let Fact::ExistFact(source) = expected_source else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction source must be an existential fact",
            ));
        };
        if !source.is_plain_exist() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction source must be a positive `exist` fact",
            ));
        }
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target)) = expected_target else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction target must be a positive proposition fact",
            ));
        };
        let predicate_name = target.predicate.to_string();
        let local_predicate_name = predicate_name
            .rsplit_once(MOD_SIGN)
            .map(|(_, local_name)| local_name)
            .unwrap_or(predicate_name.as_str());
        if local_predicate_name != definition {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "definition-introduction rule names a different definition from its target proposition",
            ));
        }
        lean_fact(expected_source)?;
        lean_fact(expected_target)?;

        let mut lines = vec!["by".to_string()];
        let (source_name, source_lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.extend(source_lines);
        lines.push(format!(
            "  simpa only [{}] using {}",
            lean_name(definition),
            source_name
        ));
        Ok(lines.join("\n"))
    }

    fn lean_comparison_notation_duality(
        &mut self,
        proposition: &Fact,
        expected_source: &Fact,
        expected_target: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "comparison-notation duality requires no parameter requirements and exactly one cited premise",
            ));
        }
        if proposition.to_string() != expected_target.to_string()
            || premises[0].proposition.to_string() != expected_source.to_string()
            || !crate::litex_to_lean_ir::facts_are_comparison_notation_duals(
                expected_source,
                expected_target,
            )
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "comparison-notation duality evidence does not match its retained source and target",
            ));
        }
        let (source_name, source_lines) = self.lean_named_local_fact(&premises[0], context)?;
        let mut lines = vec!["by".to_string()];
        lines.extend(source_lines);
        lines.push(format!("  exact {source_name}"));
        Ok(lines.join("\n"))
    }

    #[allow(clippy::too_many_arguments)]
    fn lean_checked_function_definition_replay(
        &self,
        proposition: &Fact,
        definition: &LitexToLeanObjectIr,
        defining_equality_fact_id: FactId,
        defining_equality: &Fact,
        expected_target: &Fact,
        application_side: &Obj,
        reduced: &Obj,
        other_side: &Obj,
        application_is_left: bool,
        reduced_matches_other_by_alpha: bool,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || !premises.is_empty() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay must not carry additional premises",
            ));
        }
        if proposition.to_string() != expected_target.to_string() {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay target disagrees with its retained target",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay target must be an equality",
            ));
        };
        let (target_application, target_other) = if application_is_left {
            (&target.left, &target.right)
        } else {
            (&target.right, &target.left)
        };
        if obj_equality_key(target_application) != obj_equality_key(application_side)
            || obj_equality_key(target_other) != obj_equality_key(other_side)
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay orientation disagrees with its retained target",
            ));
        }
        if !reduced_matches_other_by_alpha
            || !objs_equal_with_nested_binder_alpha_equivalence(reduced, other_side)
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay requires the retained reduction to be alpha-equivalent to the other equality side",
            ));
        }

        let Fact::AtomicFact(AtomicFact::EqualFact(source)) = defining_equality else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay source must be a defining equality",
            ));
        };
        let lowered_source_definition = LitexToLeanObjectIr::lower(&source.left)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        if &lowered_source_definition != definition || !matches!(&source.right, Obj::AnonymousFn(_))
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay source does not define the retained function symbol",
            ));
        }
        let Some(emitted_source) = self
            .emitted_function_definition_equalities
            .get(&defining_equality_fact_id)
        else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "checked function-definition replay cites unemitted defining equality {}",
                    defining_equality_fact_id
                ),
            ));
        };
        if emitted_source != &defining_equality.to_string()
            || !self
                .emitted_fact_names
                .contains_key(&defining_equality_fact_id)
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay defining equality disagrees with the emitted source fact",
            ));
        }

        let lowered_application = LitexToLeanObjectIr::lower(application_side)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        let LitexToLeanObjectIr::FunctionApplication(application) = &lowered_application else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay application side is not a function application",
            ));
        };
        if application.head.as_ref() != definition {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "checked function-definition replay application uses a different function symbol",
            ));
        }
        let lowered_reduced = LitexToLeanObjectIr::lower(reduced)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        let lowered_other = LitexToLeanObjectIr::lower(other_side)
            .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
        // Rendering all three retained objects is an additional closed-world
        // check that this adapter is not accepting syntax unsupported by Lean.
        lean_obj_ir_with_context(&lowered_application, &context.type_context)?;
        lean_obj_ir_with_context(&lowered_reduced, &context.type_context)?;
        lean_obj_ir_with_context(&lowered_other, &context.type_context)?;
        let definition_name = lean_obj_ir_with_context(definition, &context.type_context)?;
        Ok(format!("by\n  simpa only [{definition_name}]"))
    }

    fn available_fact_name(
        &self,
        fact_id: FactId,
        proposition: &Fact,
        context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if let Some(local_name) = context.proof_fact_names.get(&fact_id) {
            return Ok(local_name.clone());
        }
        if let Some(name) = self.emitted_fact_names.get(&fact_id) {
            return Ok(name.clone());
        }
        if let Some(local_name) = context.type_context.well_definedness_proof(proposition) {
            // Litex may check a forall once in a preflight scope and again in
            // its stored proof scope. Those scopes allocate different FactIds
            // for the same exact proposition. The certificate keeps the
            // preflight ID; the Lean binder map keeps the stored ID. Reuse is
            // allowed only by the full retained proposition, never by name or
            // by a looser logical implication.
            return Ok(local_name.to_string());
        }
        Err(litex_to_lean_error(
            &proposition.line_file(),
            format!(
                "Litex-to-Lean proof references {} for `{}` before that fact has a Lean declaration",
                fact_id, proposition
            ),
        ))
    }

    fn lean_equality_rewrite(
        &mut self,
        proposition: &Fact,
        rewrite: &LitexToLeanEqualityRewriteIr,
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != rewrite.steps.len() + 1 {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                format!(
                    "equality rewrite expected {} premises but received {}",
                    rewrite.steps.len() + 1,
                    premises.len()
                ),
            ));
        }

        let source = &premises[0];
        let mut lines = vec!["by".to_string()];
        let (source_name, source_lines) = self.lean_named_local_fact(source, context)?;
        lines.extend(source_lines);
        let mut rewrite_terms = Vec::with_capacity(rewrite.steps.len());
        let mut seen_equalities = HashSet::new();
        for (step, equality_premise) in rewrite.steps.iter().zip(premises[1..].iter()) {
            let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &equality_premise.proposition
            else {
                return Err(litex_to_lean_error(
                    &equality_premise.proposition.line_file(),
                    "an equality-rewrite premise is not an equality fact",
                ));
            };
            let left_key = obj_equality_key(&equality.left);
            let right_key = obj_equality_key(&equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let orientation_matches = match step.direction {
                LitexToLeanEqualityRewriteDirectionIr::Forward => {
                    from_key == left_key && to_key == right_key
                }
                LitexToLeanEqualityRewriteDirectionIr::Backward => {
                    from_key == right_key && to_key == left_key
                }
            };
            if !orientation_matches {
                return Err(litex_to_lean_error(
                    &equality_premise.proposition.line_file(),
                    format!(
                        "equality rewrite step `{}` -> `{}` disagrees with premise `{}`",
                        step.from, step.to, equality_premise.proposition
                    ),
                ));
            }
            if !seen_equalities.insert(equality_premise.proposition.to_string()) {
                continue;
            }
            let (local_name, local_lines) =
                self.lean_named_local_fact(equality_premise, context)?;
            lines.extend(local_lines);
            // Normalize both the cited proposition and the target toward one
            // deterministic representative. This also handles one equality
            // being used in opposite directions at different occurrences.
            rewrite_terms.push(if left_key <= right_key {
                local_name
            } else {
                format!("← {}", local_name)
            });
        }
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact_with_context(proposition, &context.type_context)?
        ));
        lines.push(format!(
            "    simpa only [{}] using {}",
            rewrite_terms.join(", "),
            source_name
        ));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_set_builder_membership(
        &mut self,
        proposition: &Fact,
        set_builder: &LitexToLeanObjectIr,
        expected_target: &Fact,
        expected_premises: &[Fact],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || proposition.to_string() != expected_target.to_string()
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "set-builder membership certificate has target requirements or a retargeted conclusion",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "set-builder membership certificate is attached to a non-membership fact",
            ));
        };
        let Obj::SetBuilder(source_builder) = &membership.set else {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "literal set-builder membership certificate targets a non-builder set",
            ));
        };
        let rebuilt = LitexToLeanObjectIr::lower(&membership.set)
            .map_err(|message| litex_to_lean_error(&membership.line_file, message))?;
        if &rebuilt != set_builder {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "set-builder membership certificate does not match the target builder",
            ));
        }

        let mut calculated = vec![Fact::from(InFact::new(
            membership.element.clone(),
            source_builder.param_set.as_ref().clone(),
            membership.line_file.clone(),
        ))];
        let mut substitutions = HashMap::new();
        insert_symbol_substitution(
            &mut substitutions,
            &source_builder.param_binding,
            membership.element.clone(),
        );
        let instantiator = Runtime::new();
        for fact in source_builder.facts.iter() {
            calculated.push(
                instantiator
                    .inst_exist_body_fact(
                        fact,
                        &substitutions,
                        ParamObjType::SetBuilder,
                        Some(&membership.line_file),
                    )?
                    .to_fact(),
            );
        }
        if calculated.len() != expected_premises.len()
            || calculated
                .iter()
                .zip(expected_premises.iter())
                .any(|(actual, expected)| actual.to_string() != expected.to_string())
            || premises.len() != expected_premises.len()
            || premises
                .iter()
                .zip(expected_premises.iter())
                .any(|(actual, expected)| actual.proposition.to_string() != expected.to_string())
        {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "set-builder membership certificate premises do not match the instantiated base and predicates",
            ));
        }

        let mut lines = vec!["by".to_string()];
        let mut names = Vec::with_capacity(premises.len());
        for premise in premises {
            let (name, premise_lines) = self.lean_named_local_fact(premise, context)?;
            lines.extend(premise_lines);
            names.push(name);
        }
        let proof = right_associated_conjunction_proof(&names);
        lines.push(format!("  exact {proof}"));
        Ok(lines.join("\n"))
    }

    fn lean_function_set_membership(
        &mut self,
        proposition: &Fact,
        element: &LitexToLeanObjectIr,
        function_set: &LitexToLeanObjectIr,
        expected_target: &Fact,
        expected_pointwise: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || proposition.to_string() != expected_target.to_string()
            || premises.len() != 1
            || premises[0].proposition.to_string() != expected_pointwise.to_string()
            || !matches!(expected_pointwise, Fact::ForallFact(_))
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "function-set membership certificate lost its exact target or pointwise forall premise",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "function-set membership certificate is attached to a non-membership fact",
            ));
        };
        let rebuilt_element = LitexToLeanObjectIr::lower(&membership.element)
            .map_err(|message| litex_to_lean_error(&membership.line_file, message))?;
        let rebuilt_set = LitexToLeanObjectIr::lower(&membership.set)
            .map_err(|message| litex_to_lean_error(&membership.line_file, message))?;
        if &rebuilt_element != element || &rebuilt_set != function_set {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "function-set membership certificate does not match the target objects",
            ));
        }
        let LitexToLeanObjectIr::FunctionSet { function } = function_set else {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "function-set membership certificate targets a non-function-space object",
            ));
        };

        // A universal result set contributes no semantic refinement beyond the
        // native dependent function type. The verifier still retained and
        // validated the pointwise child above.
        if function.return_set.is_universal_native_set() {
            return Ok("by\n  change True\n  trivial".to_string());
        }

        let (pointwise_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
        let (function_context, _, target_arguments) =
            lean_function_value_binders_with_context(function, &context.type_context)?;
        let mut pointwise_arguments = Vec::new();
        let mut universal_membership_lines = Vec::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let parameter_name = lean_name(&parameter.name);
            pointwise_arguments.push(parameter_name.clone());
            if parameter.requires_membership_proof {
                pointwise_arguments.push(format!("litex_fn_parameter_membership_{}", index + 1));
                continue;
            }

            // Litex forall facts retain a typing premise for every object
            // parameter. Native Lean function types erase that proof exactly
            // when the source set lowers to `Set.univ`, so reconstruct the
            // erased argument before specializing the checked pointwise fact.
            let proof_name = format!("litex_fn_universal_membership_{}", index + 1);
            let requirement: Fact = InFact::new(
                obj_for_bound_param_from_function_parameter(parameter),
                parameter.source_set.clone(),
                membership.line_file.clone(),
            )
            .into();
            universal_membership_lines.push(format!(
                "  have {proof_name} : {} := by",
                lean_fact_with_context(&requirement, &function_context)?
            ));
            universal_membership_lines.push("    change True".to_string());
            universal_membership_lines.push("    trivial".to_string());
            pointwise_arguments.push(proof_name);
        }
        pointwise_arguments.extend(
            function
                .domain_facts
                .iter()
                .enumerate()
                .map(|(index, _)| format!("litex_fn_domain_{}", index + 1)),
        );

        lines.insert(0, "by".to_string());
        if !target_arguments.is_empty() {
            lines.push(format!("  intro {}", target_arguments.join(" ")));
        }
        lines.extend(universal_membership_lines);
        let pointwise_application = if pointwise_arguments.is_empty() {
            pointwise_name
        } else {
            format!("{} {}", pointwise_name, pointwise_arguments.join(" "))
        };
        lines.push(format!("  exact {pointwise_application}"));
        Ok(lines.join("\n"))
    }

    fn lean_refined_numeric_membership(
        &mut self,
        proposition: &Fact,
        target_set: &StandardSet,
        expected_target: &Fact,
        expected_premises: &[Fact],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || proposition.to_string() != expected_target.to_string()
            || premises.len() != 2
            || expected_premises.len() != 2
            || premises
                .iter()
                .zip(expected_premises.iter())
                .any(|(actual, expected)| actual.proposition.to_string() != expected.to_string())
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "refined numeric membership certificate lost its exact target or constructor premises",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "refined numeric membership certificate is attached to a non-membership fact",
            ));
        };
        if !matches!(&membership.set, Obj::StandardSet(actual) if actual == target_set) {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "refined numeric membership certificate changed its target standard set",
            ));
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let element = membership.element.clone();
        let (base, condition): (StandardSet, Fact) = match target_set {
            StandardSet::QPos => (
                StandardSet::Q,
                LessFact::new(zero, element.clone(), membership.line_file.clone()).into(),
            ),
            StandardSet::RPos => (
                StandardSet::R,
                LessFact::new(zero, element.clone(), membership.line_file.clone()).into(),
            ),
            StandardSet::QNeg => (
                StandardSet::Q,
                LessFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            StandardSet::ZNeg => (
                StandardSet::Z,
                LessFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            StandardSet::RNeg => (
                StandardSet::R,
                LessFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            StandardSet::QStar => (
                StandardSet::Q,
                NotEqualFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            StandardSet::ZStar => (
                StandardSet::Z,
                NotEqualFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            StandardSet::RStar => (
                StandardSet::R,
                NotEqualFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            StandardSet::CStar => (
                StandardSet::C,
                NotEqualFact::new(element.clone(), zero, membership.line_file.clone()).into(),
            ),
            _ => {
                return Err(litex_to_lean_error(
                    &membership.line_file,
                    "refined numeric membership certificate names a non-refined standard set",
                ))
            }
        };
        let base: Fact = InFact::new(element, base.into(), membership.line_file.clone()).into();
        if expected_premises[0].to_string() != base.to_string()
            || expected_premises[1].to_string() != condition.to_string()
        {
            return Err(litex_to_lean_error(
                &membership.line_file,
                "refined numeric membership premises do not reconstruct the target set definition",
            ));
        }

        // The base-carrier child is represented by the native Lean type and
        // its universal set membership reduces to True. The second child is
        // exactly the predicate defining the refined set.
        let (condition_name, mut lines) = self.lean_named_local_fact(&premises[1], context)?;
        lines.insert(0, "by".to_string());
        lines.push(format!("  simpa using {condition_name}"));
        Ok(lines.join("\n"))
    }

    fn lean_function_application_return_membership(
        &mut self,
        proposition: &Fact,
        source_application: &LitexToLeanObjectIr,
        function_set: &LitexToLeanObjectIr,
        typed_return_set: &LitexToLeanObjectIr,
        expected_target: &Fact,
        expected_head_membership: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || proposition.to_string() != expected_target.to_string()
            || premises.len() != 1
            || premises[0].proposition.to_string() != expected_head_membership.to_string()
        {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "function-application return certificate lost its target or head-membership premise",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "function-application return certificate is attached to a non-membership fact",
            ));
        };
        let rebuilt_application = LitexToLeanObjectIr::lower(&target.element)
            .map_err(|message| litex_to_lean_error(&target.line_file, message))?;
        let rebuilt_return_set = LitexToLeanObjectIr::lower(&target.set)
            .map_err(|message| litex_to_lean_error(&target.line_file, message))?;
        if &rebuilt_application != source_application || &rebuilt_return_set != typed_return_set {
            return Err(litex_to_lean_error(
                &target.line_file,
                "function-application return certificate does not match its source application or instantiated return set",
            ));
        }
        let LitexToLeanObjectIr::FunctionApplication(application) = source_application else {
            return Err(litex_to_lean_error(
                &target.line_file,
                "function-application return certificate contains a non-application object",
            ));
        };
        let LitexToLeanObjectIr::FunctionSet { function } = function_set else {
            return Err(litex_to_lean_error(
                &target.line_file,
                "function-application return certificate contains a non-function-space signature",
            ));
        };
        let Fact::AtomicFact(AtomicFact::InFact(head_membership)) = expected_head_membership else {
            return Err(litex_to_lean_error(
                &expected_head_membership.line_file(),
                "function-application return certificate head premise is not a membership fact",
            ));
        };
        let rebuilt_head = LitexToLeanObjectIr::lower(&head_membership.element)
            .map_err(|message| litex_to_lean_error(&head_membership.line_file, message))?;
        let rebuilt_head_set = LitexToLeanObjectIr::lower(&head_membership.set)
            .map_err(|message| litex_to_lean_error(&head_membership.line_file, message))?;
        if rebuilt_head != *application.head || rebuilt_head_set != *function_set {
            return Err(litex_to_lean_error(
                &head_membership.line_file,
                "function-application return certificate head premise does not match the application signature",
            ));
        }

        // A universal final carrier has no remaining predicate after native
        // Lean typing. Refined and nested-refined returns eliminate the exact
        // head membership proof across every retained source application layer.
        if typed_return_set.is_universal_native_set() {
            return Ok("by\n  change True\n  trivial".to_string());
        }
        let (head_proof, mut lines) = if let Some(proof) = context
            .type_context
            .alpha_equivalent_membership_proof(&head_membership.element, &head_membership.set)
        {
            (proof.to_string(), Vec::new())
        } else {
            self.lean_named_local_fact(&premises[0], context)?
        };
        let eliminated = lean_function_membership_elimination_with_context(
            &head_proof,
            application,
            function,
            &context.type_context,
        )?;
        lines.insert(0, "by".to_string());
        lines.push(format!("  exact {eliminated}"));
        Ok(lines.join("\n"))
    }

    fn lean_forall_introduction(
        &mut self,
        proposition: &Fact,
        parameter_premises: &[LitexToLeanLocalPremiseIr],
        premises: &[LitexToLeanLocalPremiseIr],
        inferred_premises: &[LitexToLeanFactIr],
        conclusions: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        self.lean_forall_introduction_with_steps(
            proposition,
            parameter_premises,
            premises,
            inferred_premises,
            &[],
            conclusions,
            context,
        )
    }

    fn lean_forall_introduction_with_steps(
        &mut self,
        proposition: &Fact,
        parameter_premises: &[LitexToLeanLocalPremiseIr],
        premises: &[LitexToLeanLocalPremiseIr],
        inferred_premises: &[LitexToLeanFactIr],
        proof_steps: &[LitexToLeanStatementIr],
        conclusions: &[LitexToLeanFactIr],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::ForallFact(forall) = proposition else {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "forall-introduction evidence was attached to a non-forall proposition",
            ));
        };
        if conclusions.is_empty() || conclusions.len() != forall.then_facts.len() {
            return Err(litex_to_lean_error(
                &forall.line_file,
                format!(
                    "forall-introduction source has {} conclusions but its evidence retained {}",
                    forall.then_facts.len(),
                    conclusions.len()
                ),
            ));
        }
        for (source_conclusion, conclusion) in forall.then_facts.iter().zip(conclusions.iter()) {
            if source_conclusion.clone().to_fact().to_string() != conclusion.proposition.to_string()
            {
                return Err(litex_to_lean_error(
                    &forall.line_file,
                    "forall-introduction conclusions are not in source order",
                ));
            }
        }

        let parameter_count = forall
            .params_def_with_type
            .groups
            .iter()
            .map(|group| group.params.len())
            .sum::<usize>();
        if parameter_count != parameter_premises.len() {
            return Err(litex_to_lean_error(
                &forall.line_file,
                "forall-introduction parameter binders and retained typing premises have different arities",
            ));
        }
        let mut intro_names = Vec::new();
        let mut parameter_premises = parameter_premises.iter();
        let mut emitted_generic_carriers = HashSet::new();
        let mut flat_parameter_index = 0usize;
        for group in forall.params_def_with_type.groups.iter() {
            let param_type = build_litex_to_lean_ir_source_parameter_type(group)?;
            if lean_generic_param_binder(
                &param_type,
                &mut emitted_generic_carriers,
                &context.type_context,
            )?
            .is_some()
            {
                intro_names.push("_".to_string());
                intro_names.push("_".to_string());
            }
            for binding in group.params.iter() {
                flat_parameter_index += 1;
                context.type_context.insert_param(binding.id(), &param_type);
                context.bound_symbol_ids.insert(binding.id());
                intro_names.push(lean_name(binding.name()));
                let premise = parameter_premises.next().ok_or_else(|| {
                    litex_to_lean_error(
                        &forall.line_file,
                        "forall-introduction lost a parameter typing premise",
                    )
                })?;
                if matches!(premise.fact, Fact::AtomicFact(AtomicFact::IsSetFact(_))) {
                    context
                        .proof_fact_names
                        .insert(premise.fact_id, "(by trivial)".to_string());
                    continue;
                }
                let local_name = lean_forall_parameter_proof_name(flat_parameter_index);
                context
                    .proof_fact_names
                    .insert(premise.fact_id, local_name.clone());
                context
                    .type_context
                    .insert_parameter_well_definedness_proof(&premise.fact, local_name.clone());
                intro_names.push(local_name);
            }
        }
        for (index, premise) in premises.iter().enumerate() {
            let local_name = lean_forall_domain_proof_name(index + 1);
            context
                .proof_fact_names
                .insert(premise.fact_id, local_name.clone());
            context
                .type_context
                .insert_well_definedness_proof(&premise.fact, local_name.clone());
            if is_nonzero_fact(&premise.fact) {
                context.nonzero_names.push(local_name.clone());
            }
            intro_names.push(local_name);
        }
        // Carrier evidence for forall-bound symbols exists only after the
        // binders above have entered this proof context. Re-run proof-tree
        // propagation here so closed intermediate terms inherit the target
        // carrier instead of elaborating independently (usually as `ℕ`).
        for fact in inferred_premises.iter().chain(conclusions.iter()) {
            apply_fact_proof_type_hints(fact, &mut context.type_context)?;
        }
        for step in proof_steps {
            apply_statement_type_hints(step, &mut context.type_context)?;
        }
        let mut inferred_lines = Vec::new();
        for inferred in inferred_premises {
            let fact_id = required_fact_id(inferred)?;
            let (local_name, local_lines) = self.lean_named_local_fact(inferred, context)?;
            inferred_lines.extend(local_lines);
            register_local_fact(fact_id, &inferred.proposition, &local_name, context);
        }
        // Litex installs parameter/domain inferences in the temporary forall
        // environment before checking source-object well-definedness. Emit
        // and register those exact FactIds first, so a WD certificate can cite
        // (for example) positivity inferred from an `R+` binder.
        let scoped_well_definedness = std::mem::take(&mut context.scoped_well_definedness);
        let scoped_well_definedness_lines =
            self.lean_scoped_well_definedness_lines(&scoped_well_definedness, context)?;
        let mut lines = vec![
            "by".to_string(),
            format!("  intro {}", intro_names.join(" ")),
        ];
        lines.extend(inferred_lines);
        lines.extend(scoped_well_definedness_lines);
        for step in proof_steps {
            lines.extend(self.lean_local_statement(step, context)?);
        }
        if conclusions.len() == 1 {
            let conclusion = &conclusions[0];
            let inner = self.lean_proof_in_current_space(
                &conclusion.proposition,
                &conclusion.proof,
                context,
            )?;
            let inner = inner.strip_prefix("by\n").unwrap_or(inner.as_str());
            lines.push(inner.to_string());
        } else {
            let mut conclusion_names = Vec::with_capacity(conclusions.len());
            for conclusion in conclusions {
                let (name, conclusion_lines) = self.lean_named_local_fact(conclusion, context)?;
                lines.extend(conclusion_lines);
                conclusion_names.push(name);
            }
            lines.push(format!("  exact ⟨{}⟩", conclusion_names.join(", ")));
        }
        Ok(lines.join("\n"))
    }

    fn next_proof_fact_name(&mut self, context: &mut LeanProofContext) -> String {
        let (local_space_id, local_index) = self.next_local_coordinate(context);
        lean_proof_fact_name(local_space_id, local_index)
    }

    fn next_proof_arg_name(&mut self, context: &mut LeanProofContext) -> String {
        let (local_space_id, local_index) = self.next_local_coordinate(context);
        lean_proof_arg_name(local_space_id, local_index)
    }

    fn next_well_defined_fact_name(&mut self, context: &mut LeanProofContext) -> String {
        let (local_space_id, local_index) = self.next_local_coordinate(context);
        format!("well_defined_fact_{}_{}", local_space_id, local_index)
    }

    fn next_local_coordinate(&mut self, context: &mut LeanProofContext) -> (usize, usize) {
        let local_space_id = match context.local_space_id {
            Some(local_space_id) => local_space_id,
            None => {
                let local_space_id = self.next_local_space_id;
                self.next_local_space_id += 1;
                context.local_space_id = Some(local_space_id);
                local_space_id
            }
        };
        context.next_local_index += 1;
        (local_space_id, context.next_local_index)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LeanFactClass {
    Equality,
    WeakOrder,
    StrictOrder,
}

fn lean_prime_u64_reflection(
    proposition: &Fact,
    premises: &[LitexToLeanFactIr],
) -> Result<String, RuntimeError> {
    if !premises.is_empty() {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "prime reflection evidence must not contain premises",
        ));
    }
    let (predicate, body) = match proposition {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(fact)) => (&fact.predicate, &fact.body),
        Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(fact)) => (&fact.predicate, &fact.body),
        _ => {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "prime reflection evidence requires `$prime(n)` or `not $prime(n)`",
            ));
        }
    };
    if !matches!(predicate, AtomicName::WithoutMod(name) if name == PRIME)
        || body.len() != 1
        || !matches!(&body[0], Obj::Number(number) if number.normalized_value.parse::<u64>().is_ok())
    {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "prime reflection evidence requires one literal u64 argument",
        ));
    }
    Ok("by\n  norm_num".to_string())
}

fn lean_coprime_natural_reflection(
    proposition: &Fact,
    premises: &[LitexToLeanFactIr],
) -> Result<String, RuntimeError> {
    if !premises.is_empty() {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "coprime reflection evidence must not contain premises",
        ));
    }
    let (predicate, body) = match proposition {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(fact)) => (&fact.predicate, &fact.body),
        Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(fact)) => (&fact.predicate, &fact.body),
        _ => {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "coprime reflection evidence requires `$coprime(a, b)` or its negation",
            ));
        }
    };
    if !matches!(predicate, AtomicName::WithoutMod(name) if name == COPRIME)
        || body.len() != 2
        || body.iter().any(|argument| {
            !matches!(argument, Obj::Number(number)
                if !number.normalized_value.starts_with('-')
                    && !number.normalized_value.contains('.'))
        })
    {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "coprime reflection evidence requires two natural-number literals",
        ));
    }
    Ok("by\n  norm_num [Nat.Coprime]".to_string())
}

fn arithmetic_builtin_contract(
    rule: LitexToLeanArithmeticBuiltinRuleIr,
) -> (LeanFactClass, &'static [LeanFactClass]) {
    use LeanFactClass::*;
    use LitexToLeanArithmeticBuiltinRuleIr::*;

    match rule {
        LessEqualFromStrictOrder | GreaterEqualFromStrictOrder => (WeakOrder, &[StrictOrder]),
        SubNonnegativeFromLessEqual | AddCommonLeftLessEqual => (WeakOrder, &[WeakOrder]),
        SubPositiveFromLess | AddCommonLeftLess => (StrictOrder, &[StrictOrder]),
        AddNonnegative | MulNonnegative | AddComponentwiseLessEqual => {
            (WeakOrder, &[WeakOrder, WeakOrder])
        }
        DivNonnegative => (WeakOrder, &[WeakOrder, StrictOrder]),
        AddPositive | MulPositive | DivPositive | AddComponentwiseLess => {
            (StrictOrder, &[StrictOrder, StrictOrder])
        }
        AddPositiveLeftStrict | AddComponentwiseLessLessEqual => {
            (StrictOrder, &[StrictOrder, WeakOrder])
        }
        AddPositiveRightStrict | AddComponentwiseLessEqualLess => {
            (StrictOrder, &[WeakOrder, StrictOrder])
        }
        SubRightNonnegativeLessEqual => (WeakOrder, &[WeakOrder, WeakOrder]),
        AddRightNonnegativeLessEqual => (WeakOrder, &[WeakOrder]),
    }
}

fn lean_fact_class(fact: &Fact) -> Option<LeanFactClass> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(_)) => Some(LeanFactClass::Equality),
        Fact::AtomicFact(AtomicFact::LessEqualFact(_) | AtomicFact::GreaterEqualFact(_)) => {
            Some(LeanFactClass::WeakOrder)
        }
        Fact::AtomicFact(AtomicFact::LessFact(_) | AtomicFact::GreaterFact(_)) => {
            Some(LeanFactClass::StrictOrder)
        }
        _ => None,
    }
}

fn lean_abstract_prop(ir: &LitexToLeanAbstractPropIr) -> String {
    let name = lean_name(&ir.name);
    if ir.params.is_empty() {
        return format!("opaque {} : Prop", name);
    }
    let binders = ir
        .params
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let carrier = lean_generic_carrier_name(index as u64);
            lean_generic_object_binder(&carrier)
        })
        .collect::<Vec<_>>()
        .join(" ");
    let arguments = (0..ir.params.len())
        .map(|index| format!("{} → ", lean_generic_carrier_name(index as u64)))
        .collect::<String>();
    format!("opaque {} {} : {}Prop", name, binders, arguments)
}

fn lean_prop(ir: &LitexToLeanPropIr) -> Result<String, RuntimeError> {
    let mut type_context = LeanTypeContext::default();
    for group in ir.params.iter() {
        for symbol_id in group.symbol_ids.iter() {
            type_context.insert_param(*symbol_id, &group.param_type);
        }
    }
    for fact in ir.iff_facts.iter() {
        unify_generic_carriers_in_fact(fact, &mut type_context)?;
    }
    let mut binders = Vec::new();
    let mut emitted_generic_carriers = HashSet::new();
    for group in ir.params.iter() {
        if group.symbol_ids.len() != group.names.len() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                "Litex-to-Lean proposition parameter names and SymbolIds have different arities",
            ));
        }
        if let Some(generic_binder) = lean_generic_param_binder(
            &group.param_type,
            &mut emitted_generic_carriers,
            &type_context,
        )? {
            binders.push(generic_binder);
        }
        let lean_type = lean_ir_param_type(&group.param_type, &type_context)?;
        binders.push(format!(
            "({} : {})",
            group
                .names
                .iter()
                .map(|name| lean_name(name))
                .collect::<Vec<_>>()
                .join(" "),
            lean_type
        ));
    }
    let binder_text = if binders.is_empty() {
        String::new()
    } else {
        format!(" {}", binders.join(" "))
    };
    if ir.iff_facts.is_empty() {
        return Ok(format!(
            "opaque {}{} : Prop",
            lean_name(&ir.name),
            binder_text
        ));
    }
    let body = ir
        .iff_facts
        .iter()
        .map(|fact| lean_fact_with_context(fact, &type_context))
        .collect::<Result<Vec<_>, RuntimeError>>()?
        .join(" ∧ ");
    Ok(format!(
        "def {}{} : Prop := {}",
        lean_name(&ir.name),
        binder_text,
        parenthesize_if_many(&body, ir.iff_facts.len())
    ))
}

fn lean_ir_param_type(
    param_type: &LitexToLeanParameterTypeIr,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let carrier = match param_type {
        LitexToLeanParameterTypeIr::Set { element_carrier }
        | LitexToLeanParameterTypeIr::NonemptySet { element_carrier }
        | LitexToLeanParameterTypeIr::FiniteSet { element_carrier } => LitexToLeanCarrierIr::Set {
            element_carrier: Box::new(element_carrier.clone()),
        },
        LitexToLeanParameterTypeIr::MemberOf {
            element_carrier, ..
        } => element_carrier.clone(),
        LitexToLeanParameterTypeIr::Unsupported(_) => Err(litex_to_lean_error(
            &default_line_file(),
            format!(
                "Litex-to-Lean does not support parameter type {:?}",
                param_type
            ),
        ))?,
    };
    type_context
        .lean_type(&carrier)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))
}

fn param_type_object_carrier(
    param_type: &LitexToLeanParameterTypeIr,
) -> Result<LitexToLeanCarrierIr, RuntimeError> {
    Ok(match param_type {
        LitexToLeanParameterTypeIr::Set { element_carrier }
        | LitexToLeanParameterTypeIr::NonemptySet { element_carrier }
        | LitexToLeanParameterTypeIr::FiniteSet { element_carrier } => LitexToLeanCarrierIr::Set {
            element_carrier: Box::new(element_carrier.clone()),
        },
        LitexToLeanParameterTypeIr::MemberOf {
            element_carrier, ..
        } => element_carrier.clone(),
        LitexToLeanParameterTypeIr::Unsupported(reason) => {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!("unsupported parameter type: {reason}"),
            ));
        }
    })
}

fn lean_generic_param_binder(
    param_type: &LitexToLeanParameterTypeIr,
    emitted: &mut HashSet<SymbolId>,
    type_context: &LeanTypeContext,
) -> Result<Option<String>, RuntimeError> {
    let element_carrier = match param_type {
        LitexToLeanParameterTypeIr::Set { element_carrier }
        | LitexToLeanParameterTypeIr::NonemptySet { element_carrier }
        | LitexToLeanParameterTypeIr::FiniteSet { element_carrier } => element_carrier,
        LitexToLeanParameterTypeIr::MemberOf {
            element_carrier, ..
        } => element_carrier,
        LitexToLeanParameterTypeIr::Unsupported(_) => return Ok(None),
    };
    let resolved = type_context
        .resolve_carrier(element_carrier)
        .unwrap_or_else(|_| element_carrier.clone());
    let LitexToLeanCarrierIr::Generic { anchor } = resolved else {
        return Ok(None);
    };
    if !emitted.insert(anchor) {
        return Ok(None);
    }
    let carrier = type_context
        .lean_type(&LitexToLeanCarrierIr::Generic { anchor })
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    Ok(Some(lean_generic_object_binder(&carrier)))
}

fn apply_fact_proof_type_hints(
    fact: &LitexToLeanFactIr,
    type_context: &mut LeanTypeContext,
) -> Result<(), RuntimeError> {
    apply_proof_type_hints(&fact.proposition, &fact.proof, type_context)
}

fn apply_proof_type_hints(
    proposition: &Fact,
    proof: &LitexToLeanFactProofIr,
    type_context: &mut LeanTypeContext,
) -> Result<(), RuntimeError> {
    match proof {
        LitexToLeanFactProofIr::RuleApplication {
            rule,
            parameter_requirements,
            premises,
        } => {
            let is_positive_real_membership = matches!(
                rule,
                LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::PositiveRealMembership)
            );
            if matches!(
                rule,
                LitexToLeanProofRuleIr::Normalization {
                    kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                }
            ) {
                expect_unconstrained_binary_fact_carrier(
                    proposition,
                    &LitexToLeanCarrierIr::Rational,
                    type_context,
                );
            }
            if matches!(
                rule,
                LitexToLeanProofRuleIr::Normalization {
                    kind: LitexToLeanNormalizationKindIr::IntegerExpressionSimplification,
                }
            ) {
                expect_unconstrained_binary_fact_carrier(
                    proposition,
                    &LitexToLeanCarrierIr::Integer,
                    type_context,
                );
            }
            if let LitexToLeanProofRuleIr::ClosedNumericReflection { carrier } = rule {
                expect_unconstrained_binary_fact_carrier(proposition, carrier, type_context);
            }
            // Universal native membership carries its expectation locally in
            // the target set.  Do not persist that expectation by object key:
            // one Litex numeral may legitimately appear in both `R` and `C`
            // well-definedness certificates, while each Lean occurrence is
            // typed by its own membership proposition.
            if is_positive_real_membership {
                expect_unconstrained_binary_fact_carrier(
                    proposition,
                    &LitexToLeanCarrierIr::Real,
                    type_context,
                );
            }
            if matches!(
                rule,
                LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::PrimeU64Reflection)
            ) {
                expect_normal_predicate_arguments(
                    proposition,
                    &LitexToLeanCarrierIr::Natural,
                    type_context,
                );
            }
            if matches!(
                rule,
                LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::CoprimeNaturalReflection)
            ) {
                expect_normal_predicate_arguments(
                    proposition,
                    &LitexToLeanCarrierIr::Natural,
                    type_context,
                );
            }
            if let LitexToLeanProofRuleIr::KnownForallInstantiation { arguments, .. } = rule {
                let mut common_carrier = None;
                let mut common_carrier_conflict = false;
                for argument in arguments {
                    let carrier = param_type_object_carrier(&argument.param_type)?;
                    type_context.expect_object(&argument.argument, carrier.clone());
                    let carrier = type_context.resolve_carrier(&carrier).unwrap_or(carrier);
                    common_carrier = match common_carrier.take() {
                        None if !common_carrier_conflict => Some(carrier),
                        Some(current) if current == carrier => Some(current),
                        Some(_) => {
                            common_carrier_conflict = true;
                            None
                        }
                        None => None,
                    };
                }
                if let Some(carrier) = common_carrier {
                    expect_normal_predicate_arguments(proposition, &carrier, type_context);
                }
            }
            if !is_positive_real_membership {
                for premise in premises {
                    propagate_fact_argument_expectations(
                        &premise.proposition,
                        proposition,
                        type_context,
                    );
                }
            }
            for premise in parameter_requirements.iter().chain(premises.iter()) {
                apply_fact_proof_type_hints(premise, type_context)?;
            }
            if !is_positive_real_membership {
                for premise in premises {
                    propagate_fact_argument_expectations(
                        &premise.proposition,
                        proposition,
                        type_context,
                    );
                }
            }
        }
        LitexToLeanFactProofIr::Memo { proof } => {
            apply_proof_type_hints(proposition, proof, type_context)?;
        }
        LitexToLeanFactProofIr::ForallIntroduction {
            inferred_premises,
            conclusions,
            ..
        } => {
            let Fact::ForallFact(forall) = proposition else {
                return Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "forall-introduction type hints require a forall proposition",
                ));
            };
            for group in &forall.params_def_with_type.groups {
                let param_type = build_litex_to_lean_ir_source_parameter_type(group)?;
                for binding in &group.params {
                    type_context.insert_param(binding.id(), &param_type);
                }
            }
            constrain_forall_generic_carriers(forall, type_context)?;
            for fact in inferred_premises.iter().chain(conclusions.iter()) {
                apply_fact_proof_type_hints(fact, type_context)?;
            }
        }
        LitexToLeanFactProofIr::ObjectDefinition {
            value_check: Some(value_check),
            ..
        } => apply_fact_proof_type_hints(value_check, type_context)?,
        LitexToLeanFactProofIr::CaseSplit { coverage, branches } => {
            apply_fact_proof_type_hints(coverage, type_context)?;
            for branch in branches {
                for step in branch.steps.iter() {
                    apply_statement_type_hints(step, type_context)?;
                }
            }
        }
        LitexToLeanFactProofIr::ByContradiction { steps, .. } => {
            for step in steps {
                apply_statement_type_hints(step, type_context)?;
            }
        }
        LitexToLeanFactProofIr::Composite { steps } => {
            for step in steps {
                apply_fact_proof_type_hints(step, type_context)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn apply_statement_type_hints(
    statement: &LitexToLeanStatementIr,
    type_context: &mut LeanTypeContext,
) -> Result<(), RuntimeError> {
    match statement {
        LitexToLeanStatementIr::Fact(ir) => apply_fact_proof_type_hints(&ir.fact, type_context),
        LitexToLeanStatementIr::ProjectedForall(ir) => {
            for fact in ir.facts.iter().chain(ir.inferred_facts.iter()) {
                apply_fact_proof_type_hints(fact, type_context)?;
            }
            Ok(())
        }
        LitexToLeanStatementIr::NamedTheorem(ir) => {
            apply_fact_proof_type_hints(&ir.theorem, type_context)?;
            for step in ir.proof_steps.iter() {
                apply_statement_type_hints(&step.statement, type_context)?;
            }
            for fact in ir.stored_projections.iter().chain(ir.inferred_facts.iter()) {
                apply_fact_proof_type_hints(fact, type_context)?;
            }
            Ok(())
        }
        LitexToLeanStatementIr::Proof(ir) => {
            for fact in ir.facts.iter().chain(ir.inferred_facts.iter()) {
                apply_fact_proof_type_hints(fact, type_context)?;
            }
            Ok(())
        }
        LitexToLeanStatementIr::Trust(ir) => {
            for fact in ir.facts.iter().chain(ir.inferred_facts.iter()) {
                apply_fact_proof_type_hints(fact, type_context)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn expect_normal_predicate_arguments(
    proposition: &Fact,
    carrier: &LitexToLeanCarrierIr,
    type_context: &mut LeanTypeContext,
) {
    let arguments = match proposition {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(fact)) => &fact.body,
        Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(fact)) => &fact.body,
        _ => return,
    };
    for argument in arguments.iter() {
        type_context.expect_object(argument, carrier.clone());
    }
}

fn expect_unconstrained_binary_fact_carrier(
    proposition: &Fact,
    carrier: &LitexToLeanCarrierIr,
    type_context: &mut LeanTypeContext,
) {
    let Fact::AtomicFact(atomic) = proposition else {
        return;
    };
    let (left, right) = match atomic {
        AtomicFact::EqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotLessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotLessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotGreaterFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotGreaterEqualFact(fact) => (&fact.left, &fact.right),
        _ => return,
    };
    if type_context.expected_object(left).is_none()
        && type_context.expected_object(right).is_none()
        && known_object_carrier(left, type_context).is_none()
        && known_object_carrier(right, type_context).is_none()
    {
        type_context.expect_object(left, carrier.clone());
        type_context.expect_object(right, carrier.clone());
    }
}

fn expect_binary_fact_carrier(
    proposition: &Fact,
    carrier: &LitexToLeanCarrierIr,
    type_context: &mut LeanTypeContext,
) {
    let Fact::AtomicFact(atomic) = proposition else {
        return;
    };
    let (left, right) = match atomic {
        AtomicFact::EqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotLessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotLessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotGreaterFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotGreaterEqualFact(fact) => (&fact.left, &fact.right),
        _ => return,
    };
    type_context.expect_object(left, carrier.clone());
    type_context.expect_object(right, carrier.clone());
}

fn propagate_fact_argument_expectations(
    source: &Fact,
    target: &Fact,
    type_context: &mut LeanTypeContext,
) {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return;
    };
    let source_arguments = source.args_ref();
    let target_arguments = target.args_ref();
    if source_arguments.len() != target_arguments.len() {
        return;
    }
    for (source, target) in source_arguments.iter().zip(target_arguments.iter()) {
        let source_carrier = known_object_carrier(source, type_context);
        let target_carrier = known_object_carrier(target, type_context);
        match (source_carrier, target_carrier) {
            (Some(source_carrier), None) => {
                type_context.expect_object(target, source_carrier);
            }
            (None, Some(target_carrier)) => {
                type_context.expect_object(source, target_carrier);
            }
            _ => {}
        }
    }
}

fn known_object_carrier(
    object: &Obj,
    type_context: &LeanTypeContext,
) -> Option<LitexToLeanCarrierIr> {
    if let Some(carrier) = type_context.expected_object(object) {
        return type_context
            .resolve_carrier(carrier)
            .ok()
            .or_else(|| Some(carrier.clone()));
    }
    let object = LitexToLeanObjectIr::lower(object).ok()?;
    let carrier = type_context.object_carrier(&object).ok()??;
    type_context
        .resolve_carrier(&carrier)
        .ok()
        .or(Some(carrier))
}

fn lean_fact(fact: &Fact) -> Result<String, RuntimeError> {
    lean_fact_with_context(fact, &LeanTypeContext::default())
}

pub(super) fn lean_fact_with_context(
    fact: &Fact,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic) => lean_atomic_fact_with_context(atomic, type_context),
        Fact::AndFact(and_fact) => Ok(parenthesized_join(
            and_fact
                .facts
                .iter()
                .map(|fact| lean_atomic_fact_with_context(fact, type_context))
                .collect::<Result<Vec<_>, RuntimeError>>()?,
            " ∧ ",
        )),
        Fact::OrFact(or_fact) => Ok(parenthesized_join(
            or_fact
                .facts
                .iter()
                .map(|branch| lean_fact_with_context(&branch.clone().into(), type_context))
                .collect::<Result<Vec<_>, RuntimeError>>()?,
            " ∨ ",
        )),
        Fact::ForallFact(forall) => lean_forall_fact_with_context(forall, type_context),
        Fact::ExistFact(exist) => lean_exist_fact_with_context(exist, type_context),
        other => Err(litex_to_lean_error(
            &other.line_file(),
            format!(
                "Litex-to-Lean proposition backend does not support `{}`",
                other.fact_type_string()
            ),
        )),
    }
}

fn lean_exist_fact_with_context(
    exist: &ExistFactEnum,
    outer_type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let ExistFactEnum::ExistFact(body) = exist else {
        return Err(litex_to_lean_error(
            &exist.line_file(),
            "Litex-to-Lean proposition backend currently supports positive `exist`, not `exist!` or `not exist`",
        ));
    };
    ensure_lean_binders_are_capture_free(
        body.params_def_with_type.groups.iter(),
        body.get_args_from_fact_ref(),
        &body.line_file,
        "existential",
    )?;
    let mut type_context = outer_type_context.clone();
    let mut param_types = Vec::new();
    for group in body.params_def_with_type.groups.iter() {
        let param_type = build_litex_to_lean_ir_source_parameter_type(group)?;
        for binding in group.params.iter() {
            type_context.insert_param(binding.id(), &param_type);
        }
        param_types.push(param_type);
    }
    let body_parts = body
        .facts
        .iter()
        .map(|fact| lean_exist_body_fact_with_context(fact, &type_context))
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let mut tail = lean_right_associated_conjunction(&body_parts);
    for (group, param_type) in body
        .params_def_with_type
        .groups
        .iter()
        .zip(param_types.iter())
        .rev()
    {
        for binding in group.params.iter().rev() {
            let name = lean_name(binding.name());
            tail = lean_exist_param_binder(&name, param_type, &tail, &type_context)?;
        }
    }
    Ok(tail)
}

fn lean_exist_body_fact_with_context(
    fact: &ExistBodyFact,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    lean_fact_with_context(&fact.from_ref_to_cloned_fact(), type_context)
}

fn lean_exist_param_binder(
    name: &str,
    param_type: &LitexToLeanParameterTypeIr,
    tail: &str,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    match param_type {
        LitexToLeanParameterTypeIr::MemberOf {
            set,
            element_carrier,
        } => {
            let set = lean_obj_ir_with_context(set, type_context)?;
            let element_type = type_context
                .lean_type(element_carrier)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
            Ok(format!(
                "∃ {} : {}, {} ∈ {} ∧ {}",
                name, element_type, name, set, tail
            ))
        }
        LitexToLeanParameterTypeIr::Set { .. }
        | LitexToLeanParameterTypeIr::NonemptySet { .. }
        | LitexToLeanParameterTypeIr::FiniteSet { .. } => Err(litex_to_lean_error(
            &default_line_file(),
            "Litex-to-Lean native ABI does not yet support existential generic-set binders",
        )),
        LitexToLeanParameterTypeIr::Unsupported(reason) => Err(litex_to_lean_error(
            &default_line_file(),
            format!("unsupported existential parameter type: {reason}"),
        )),
    }
}

fn lean_right_associated_conjunction(parts: &[String]) -> String {
    match parts {
        [] => "True".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}) ∧ {}", first, lean_right_associated_conjunction(rest)),
    }
}

fn right_associated_conjunction_proof(parts: &[String]) -> String {
    match parts {
        [] => "True.intro".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("⟨{}, {}⟩", first, right_associated_conjunction_proof(rest)),
    }
}

fn lean_classical_excluded_middle(
    proposition: &Fact,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let Fact::OrFact(or_fact) = proposition else {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle evidence requires a disjunction",
        ));
    };
    if or_fact.facts.len() != 2 {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle evidence requires exactly two branches",
        ));
    }
    let (AndChainAtomicFact::AtomicFact(first), AndChainAtomicFact::AtomicFact(second)) =
        (&or_fact.facts[0], &or_fact.facts[1])
    else {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle branches must be atomic",
        ));
    };
    let branches_are_complements = first
        .logical_negation()
        .is_ok_and(|negation| negation.to_string() == second.to_string());
    if !branches_are_complements {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle branches are not logical complements",
        ));
    }
    let first_text = lean_fact_with_context(&Fact::from(first.clone()), type_context)?;
    let second_text = lean_fact_with_context(&Fact::from(second.clone()), type_context)?;
    if first.is_true() {
        return Ok(format!(
            "by\n  classical\n  exact Classical.em ({})",
            first_text
        ));
    }
    Ok(format!(
        "by\n  classical\n  by_cases proof_case : {}\n  · exact Or.inr proof_case\n  · exact Or.inl proof_case",
        second_text
    ))
}

fn lean_atomic_fact_with_context(
    fact: &AtomicFact,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    match fact {
        AtomicFact::NormalAtomicFact(normal) => lean_normal_atomic_fact_with_context(
            &normal.predicate,
            &normal.body,
            &normal.line_file,
            false,
            type_context,
        ),
        AtomicFact::NotNormalAtomicFact(normal) => lean_normal_atomic_fact_with_context(
            &normal.predicate,
            &normal.body,
            &normal.line_file,
            true,
            type_context,
        ),
        AtomicFact::EqualFact(fact) => {
            lean_binary_fact_with_context(&fact.left, "=", &fact.right, type_context)
        }
        AtomicFact::NotEqualFact(fact) => {
            lean_binary_fact_with_context(&fact.left, "≠", &fact.right, type_context)
        }
        AtomicFact::LessFact(fact) => {
            lean_binary_fact_with_context(&fact.left, "<", &fact.right, type_context)
        }
        AtomicFact::LessEqualFact(fact) => {
            lean_binary_fact_with_context(&fact.left, "≤", &fact.right, type_context)
        }
        AtomicFact::GreaterFact(fact) => {
            lean_binary_fact_with_context(&fact.left, ">", &fact.right, type_context)
        }
        AtomicFact::GreaterEqualFact(fact) => {
            lean_binary_fact_with_context(&fact.left, "≥", &fact.right, type_context)
        }
        AtomicFact::NotLessFact(fact) => {
            lean_negated_binary_fact_with_context(&fact.left, "<", &fact.right, type_context)
        }
        AtomicFact::NotLessEqualFact(fact) => {
            lean_negated_binary_fact_with_context(&fact.left, "≤", &fact.right, type_context)
        }
        AtomicFact::NotGreaterFact(fact) => {
            lean_negated_binary_fact_with_context(&fact.left, ">", &fact.right, type_context)
        }
        AtomicFact::NotGreaterEqualFact(fact) => {
            lean_negated_binary_fact_with_context(&fact.left, "≥", &fact.right, type_context)
        }
        AtomicFact::IsSetFact(fact) => Ok(format!(
            "{} {}",
            TO_LEAN_IS_SET,
            lean_obj_with_context(&fact.set, type_context)?
        )),
        AtomicFact::IsNonemptySetFact(fact) => Ok(format!(
            "{} {}",
            TO_LEAN_IS_NONEMPTY_SET,
            lean_obj_with_context(&fact.set, type_context)?
        )),
        AtomicFact::IsFiniteSetFact(fact) => Ok(format!(
            "{} {}",
            TO_LEAN_IS_FINITE_SET,
            lean_obj_with_context(&fact.set, type_context)?
        )),
        AtomicFact::InFact(fact) => {
            lean_membership_fact(&fact.element, &fact.set, false, type_context)
        }
        AtomicFact::SubsetFact(fact) => Ok(format!(
            "{} ⊆ {}",
            lean_obj_with_context(&fact.left, type_context)?,
            lean_obj_with_context(&fact.right, type_context)?
        )),
        AtomicFact::SupersetFact(fact) => Ok(format!(
            "{} ⊆ {}",
            lean_obj_with_context(&fact.right, type_context)?,
            lean_obj_with_context(&fact.left, type_context)?
        )),
        AtomicFact::NotIsSetFact(fact) => Ok(format!(
            "¬ {} {}",
            TO_LEAN_IS_SET,
            lean_obj_with_context(&fact.set, type_context)?
        )),
        AtomicFact::NotIsNonemptySetFact(fact) => Ok(format!(
            "¬ {} {}",
            TO_LEAN_IS_NONEMPTY_SET,
            lean_obj_with_context(&fact.set, type_context)?
        )),
        AtomicFact::NotIsFiniteSetFact(fact) => Ok(format!(
            "¬ {} {}",
            TO_LEAN_IS_FINITE_SET,
            lean_obj_with_context(&fact.set, type_context)?
        )),
        AtomicFact::NotInFact(fact) => {
            lean_membership_fact(&fact.element, &fact.set, true, type_context)
        }
        AtomicFact::NotSubsetFact(fact) => Ok(format!(
            "¬ ({} ⊆ {})",
            lean_obj_with_context(&fact.left, type_context)?,
            lean_obj_with_context(&fact.right, type_context)?
        )),
        AtomicFact::NotSupersetFact(fact) => Ok(format!(
            "¬ ({} ⊆ {})",
            lean_obj_with_context(&fact.right, type_context)?,
            lean_obj_with_context(&fact.left, type_context)?
        )),
        other => Err(litex_to_lean_error(
            &other.line_file(),
            format!(
                "Litex-to-Lean does not support atomic proposition `{}`",
                other
            ),
        )),
    }
}

fn lean_normal_atomic_fact_with_context(
    predicate: &AtomicName,
    body: &[Obj],
    line_file: &LineFile,
    negated: bool,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    if matches!(predicate, AtomicName::WithoutMod(name) if name == PRIME) {
        if body.len() != 1 {
            return Err(litex_to_lean_error(
                line_file,
                "`$prime` requires exactly one argument",
            ));
        }
        let argument = LitexToLeanObjectIr::lower(&body[0])
            .map_err(|message| litex_to_lean_error(line_file, message))?;
        let argument = lean_obj_ir_with_expected(
            &argument,
            &LitexToLeanCarrierIr::Natural,
            type_context,
            false,
        )?;
        if negated {
            return Ok(format!("¬ Nat.Prime {}", argument));
        }
        return Ok(format!("Nat.Prime {}", argument));
    }

    if matches!(predicate, AtomicName::WithoutMod(name) if name == COPRIME) {
        if body.len() != 2 {
            return Err(litex_to_lean_error(
                line_file,
                "`$coprime` requires exactly two arguments",
            ));
        }
        let left = LitexToLeanObjectIr::lower(&body[0])
            .map_err(|message| litex_to_lean_error(line_file, message))?;
        let right = LitexToLeanObjectIr::lower(&body[1])
            .map_err(|message| litex_to_lean_error(line_file, message))?;
        let left =
            lean_obj_ir_with_expected(&left, &LitexToLeanCarrierIr::Natural, type_context, false)?;
        let right =
            lean_obj_ir_with_expected(&right, &LitexToLeanCarrierIr::Natural, type_context, false)?;
        let coprime = format!("Nat.Coprime {} {}", left, right);
        if negated {
            return Ok(format!("¬ {}", coprime));
        }
        return Ok(coprime);
    }

    let proper_relation = match predicate {
        AtomicName::WithoutMod(name) if name == PROPER_SUBSET => Some(false),
        AtomicName::WithoutMod(name) if name == PROPER_SUPERSET => Some(true),
        _ => None,
    };
    if let Some(reversed) = proper_relation {
        if body.len() != 2 {
            return Err(litex_to_lean_error(
                line_file,
                "proper set relations require exactly two arguments",
            ));
        }
        let left = lean_obj_with_context(&body[0], type_context)?;
        let right = lean_obj_with_context(&body[1], type_context)?;
        let containment = if reversed {
            format!("{} ⊆ {}", right, left)
        } else {
            format!("{} ⊆ {}", left, right)
        };
        if negated {
            return Ok(format!("¬ ({}) ∨ {} = {}", containment, left, right));
        }
        return Ok(format!("({}) ∧ {} ≠ {}", containment, left, right));
    }

    lean_prop_application_with_context(&predicate.to_string(), body, negated, type_context)
}

fn lean_prop_application_with_context(
    name: &str,
    args: &[Obj],
    negated: bool,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let mut application = lean_name(name);
    for arg in args {
        application.push(' ');
        application.push_str(&lean_obj_with_context(arg, type_context)?);
    }
    if negated {
        Ok(format!("¬ ({})", application))
    } else {
        Ok(application)
    }
}

fn lean_binary_fact_with_context(
    left: &Obj,
    operator: &str,
    right: &Obj,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let left_ir = LitexToLeanObjectIr::lower(left)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    let right_ir = LitexToLeanObjectIr::lower(right)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    let left_hint = type_context.expected_object(left).cloned();
    let right_hint = type_context.expected_object(right).cloned();
    let hinted = match (left_hint, right_hint) {
        (Some(left), Some(right)) if left != right => {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean fact assigns incompatible target carriers {:?} and {:?}",
                    left, right
                ),
            ));
        }
        (Some(carrier), _) | (_, Some(carrier)) => Some(carrier),
        (None, None) => None,
    };
    // A carrier derived from a bound symbol or a typed expression is stronger
    // than the fallback expectation retained for an otherwise ambiguous
    // literal. The expectation map is shared across one proof tree, so the
    // same source literal can legitimately occur in several target types.
    let inferred = type_context
        .joined_numeric_carrier(&[&left_ir, &right_ir])
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?
        .or_else(|| hinted.clone());
    if inferred.is_none()
        && (requires_checked_closed_numeric_carrier(left)
            || requires_checked_closed_numeric_carrier(right))
    {
        return Err(litex_to_lean_error(
            &default_line_file(),
            format!(
                "Litex-to-Lean has no checked target carrier for closed numeric judgment `{}` {} `{}`",
                left, operator, right
            ),
        ));
    }
    let expected = inferred;
    let (left_text, right_text) = if let Some(expected) = expected {
        let hinted_untyped_left = hinted.is_some()
            && type_context
                .object_carrier(&left_ir)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?
                .is_none();
        (
            lean_obj_ir_with_expected(&left_ir, &expected, type_context, hinted_untyped_left)?,
            lean_obj_ir_with_expected(&right_ir, &expected, type_context, false)?,
        )
    } else {
        (
            lean_obj_ir_with_context(&left_ir, type_context)?,
            lean_obj_ir_with_context(&right_ir, type_context)?,
        )
    };
    Ok(format!("{} {} {}", left_text, operator, right_text))
}

fn lean_negated_binary_fact_with_context(
    left: &Obj,
    operator: &str,
    right: &Obj,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    Ok(format!(
        "¬ ({})",
        lean_binary_fact_with_context(left, operator, right, type_context)?
    ))
}

fn lean_membership_fact(
    element: &Obj,
    set: &Obj,
    negated: bool,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let element_ir = LitexToLeanObjectIr::lower(element)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    let set_ir = LitexToLeanObjectIr::lower(set)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    let element_carrier = type_context
        .membership_element_carrier(&set_ir)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    let element_text =
        lean_obj_ir_with_expected(&element_ir, &element_carrier, type_context, false)?;
    let set_text = lean_obj_ir_with_context(&set_ir, type_context)?;
    Ok(if negated {
        format!("{} ∉ {}", element_text, set_text)
    } else {
        format!("{} ∈ {}", element_text, set_text)
    })
}

fn lean_forall_fact_with_context(
    forall: &ForallFact,
    outer_type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let mut objects = Vec::new();
    collect_forall_objects_for_lean_name_check(forall, &mut objects);
    ensure_lean_binders_are_capture_free(
        forall.params_def_with_type.groups.iter(),
        objects,
        &forall.line_file,
        "universal",
    )?;
    let mut type_context = outer_type_context.clone();
    let mut param_types = Vec::new();
    let mut parameter_proof_names = HashMap::new();
    let mut flat_parameter_index = 0usize;
    for group in forall.params_def_with_type.groups.iter() {
        let param_type = build_litex_to_lean_ir_source_parameter_type(group)?;
        for binding in group.params.iter() {
            flat_parameter_index += 1;
            type_context.insert_param(binding.id(), &param_type);
            if let Some(requirement) = forall_parameter_requirement_fact(binding, &group.param_type)
            {
                let proof_name = lean_forall_parameter_proof_name(flat_parameter_index);
                type_context
                    .insert_parameter_well_definedness_proof(&requirement, proof_name.clone());
                parameter_proof_names.insert(binding.id(), proof_name);
            }
        }
        param_types.push(param_type);
    }
    for (index, fact) in forall.dom_facts.iter().enumerate() {
        type_context.insert_well_definedness_proof(fact, lean_forall_domain_proof_name(index + 1));
    }
    constrain_forall_generic_carriers(forall, &mut type_context)?;
    let conclusions = forall
        .then_facts
        .iter()
        .map(|fact| lean_fact_with_context(&fact.clone().to_fact(), &type_context))
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let mut body = parenthesized_join(conclusions, " ∧ ");
    let requirements = forall
        .dom_facts
        .iter()
        .enumerate()
        .map(|(index, fact)| {
            Ok((
                lean_forall_domain_proof_name(index + 1),
                lean_fact_with_context(fact, &type_context)?,
            ))
        })
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    for (proof_name, premise) in requirements.iter().rev() {
        body = format!("∀ ({} : {}), {}", proof_name, premise, body);
    }
    let mut emitted_generic_carriers = HashSet::new();
    for (index, (group, param_type)) in forall
        .params_def_with_type
        .groups
        .iter()
        .zip(param_types.iter())
        .enumerate()
        .rev()
    {
        for binding in group.params.iter().rev() {
            let name = lean_name(binding.name());
            body = lean_forall_param_binder(
                &name,
                param_type,
                parameter_proof_names.get(&binding.id()).map(String::as_str),
                &body,
                &type_context,
            )?;
        }
        if let Some(anchor) = generic_param_anchor(param_type, &type_context)? {
            let mut has_outer_binder = false;
            for outer_param_type in &param_types[..index] {
                if generic_param_anchor(outer_param_type, &type_context)? == Some(anchor) {
                    has_outer_binder = true;
                    break;
                }
            }
            if !has_outer_binder {
                if let Some(generic_binder) = lean_generic_param_binder(
                    param_type,
                    &mut emitted_generic_carriers,
                    &type_context,
                )? {
                    body = format!("∀ {}, {}", generic_binder, body);
                }
            }
        }
    }
    Ok(body)
}

fn build_litex_to_lean_ir_source_parameter_type(
    group: &ParamGroupWithParamType,
) -> Result<LitexToLeanParameterTypeIr, RuntimeError> {
    let Some(anchor) = group.params.first().map(|binding| binding.id()) else {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "Litex-to-Lean cannot render an empty parameter group",
        ));
    };
    let generic = || LitexToLeanCarrierIr::Generic { anchor };
    match &group.param_type {
        ParamType::Set(_) => Ok(LitexToLeanParameterTypeIr::Set {
            element_carrier: generic(),
        }),
        ParamType::NonemptySet(_) => Ok(LitexToLeanParameterTypeIr::NonemptySet {
            element_carrier: generic(),
        }),
        ParamType::FiniteSet(_) => Ok(LitexToLeanParameterTypeIr::FiniteSet {
            element_carrier: generic(),
        }),
        ParamType::Obj(set) => {
            let set = LitexToLeanObjectIr::lower(set)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
            Ok(LitexToLeanParameterTypeIr::MemberOf {
                element_carrier: LitexToLeanCarrierIr::for_membership_set(&set),
                set,
            })
        }
    }
}

fn constrain_forall_generic_carriers(
    forall: &ForallFact,
    type_context: &mut LeanTypeContext,
) -> Result<(), RuntimeError> {
    for fact in forall.dom_facts.iter() {
        unify_generic_carriers_in_fact(fact, type_context)?;
    }
    for fact in forall.then_facts.iter() {
        unify_generic_carriers_in_fact(&fact.clone().to_fact(), type_context)?;
    }
    Ok(())
}

fn unify_generic_carriers_in_fact(
    fact: &Fact,
    type_context: &mut LeanTypeContext,
) -> Result<(), RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic) => unify_generic_carriers_in_atomic_fact(atomic, type_context),
        Fact::AndFact(fact) => {
            for atomic in fact.facts.iter() {
                unify_generic_carriers_in_atomic_fact(atomic, type_context)?;
            }
            Ok(())
        }
        Fact::ChainFact(fact) => {
            for atomic in fact.facts()? {
                unify_generic_carriers_in_atomic_fact(&atomic, type_context)?;
            }
            Ok(())
        }
        Fact::OrFact(fact) => {
            for branch in fact.facts.iter() {
                match branch {
                    AndChainAtomicFact::AtomicFact(atomic) => {
                        unify_generic_carriers_in_atomic_fact(atomic, type_context)?;
                    }
                    AndChainAtomicFact::AndFact(fact) => {
                        for atomic in fact.facts.iter() {
                            unify_generic_carriers_in_atomic_fact(atomic, type_context)?;
                        }
                    }
                    AndChainAtomicFact::ChainFact(fact) => {
                        for atomic in fact.facts()? {
                            unify_generic_carriers_in_atomic_fact(&atomic, type_context)?;
                        }
                    }
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn unify_generic_carriers_in_atomic_fact(
    atomic: &AtomicFact,
    type_context: &mut LeanTypeContext,
) -> Result<(), RuntimeError> {
    let (left, right) = match atomic {
        AtomicFact::EqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::SubsetFact(fact) => (&fact.left, &fact.right),
        AtomicFact::SupersetFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotSubsetFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotSupersetFact(fact) => (&fact.left, &fact.right),
        AtomicFact::FnEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NormalAtomicFact(fact)
            if fact.body.len() == 2
                && matches!(
                    &fact.predicate,
                    AtomicName::WithoutMod(name)
                        if matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET)
                ) =>
        {
            (&fact.body[0], &fact.body[1])
        }
        AtomicFact::NotNormalAtomicFact(fact)
            if fact.body.len() == 2
                && matches!(
                    &fact.predicate,
                    AtomicName::WithoutMod(name)
                        if matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET)
                ) =>
        {
            (&fact.body[0], &fact.body[1])
        }
        _ => return Ok(()),
    };
    let (Some(left_carrier), Some(right_carrier)) = (
        known_object_carrier(left, type_context),
        known_object_carrier(right, type_context),
    ) else {
        return Ok(());
    };
    type_context
        .unify_generic_carriers(&left_carrier, &right_carrier)
        .map_err(|message| litex_to_lean_error(&atomic.line_file(), message))
}

fn generic_param_anchor(
    param_type: &LitexToLeanParameterTypeIr,
    type_context: &LeanTypeContext,
) -> Result<Option<SymbolId>, RuntimeError> {
    let element_carrier = match param_type {
        LitexToLeanParameterTypeIr::Set { element_carrier }
        | LitexToLeanParameterTypeIr::NonemptySet { element_carrier }
        | LitexToLeanParameterTypeIr::FiniteSet { element_carrier } => element_carrier,
        LitexToLeanParameterTypeIr::MemberOf {
            element_carrier, ..
        } => element_carrier,
        LitexToLeanParameterTypeIr::Unsupported(_) => return Ok(None),
    };
    let resolved = type_context
        .resolve_carrier(element_carrier)
        .unwrap_or_else(|_| element_carrier.clone());
    let LitexToLeanCarrierIr::Generic { anchor } = resolved else {
        return Ok(None);
    };
    Ok(Some(anchor))
}

fn lean_forall_param_binder(
    name: &str,
    param_type: &LitexToLeanParameterTypeIr,
    proof_name: Option<&str>,
    body: &str,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    match param_type {
        LitexToLeanParameterTypeIr::MemberOf {
            set,
            element_carrier,
        } => Ok(format!(
            "∀ ({} : {}) ({} : {} ∈ {}), {}",
            name,
            type_context
                .lean_type(element_carrier)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?,
            proof_name.ok_or_else(|| {
                litex_to_lean_error(
                    &default_line_file(),
                    "universal object parameter lost its membership proof name",
                )
            })?,
            name,
            lean_obj_ir_with_context(set, type_context)?,
            body
        )),
        LitexToLeanParameterTypeIr::Set { element_carrier } => Ok(format!(
            "∀ ({} : Set {}), {}",
            name,
            type_context
                .lean_type(element_carrier)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?,
            body
        )),
        LitexToLeanParameterTypeIr::NonemptySet { element_carrier } => Ok(format!(
            "∀ ({} : Set {}) ({} : {} {}), {}",
            name,
            type_context
                .lean_type(element_carrier)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?,
            proof_name.ok_or_else(|| {
                litex_to_lean_error(
                    &default_line_file(),
                    "universal nonempty-set parameter lost its proof name",
                )
            })?,
            TO_LEAN_IS_NONEMPTY_SET,
            name,
            body
        )),
        LitexToLeanParameterTypeIr::FiniteSet { element_carrier } => Ok(format!(
            "∀ ({} : Set {}) ({} : {} {}), {}",
            name,
            type_context
                .lean_type(element_carrier)
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?,
            proof_name.ok_or_else(|| {
                litex_to_lean_error(
                    &default_line_file(),
                    "universal finite-set parameter lost its proof name",
                )
            })?,
            TO_LEAN_IS_FINITE_SET,
            name,
            body
        )),
        LitexToLeanParameterTypeIr::Unsupported(reason) => Err(litex_to_lean_error(
            &default_line_file(),
            format!("unsupported universal parameter type: {reason}"),
        )),
    }
}

fn lean_forall_parameter_proof_name(index: usize) -> String {
    format!("litex_param_fact_{}", index)
}

fn lean_forall_domain_proof_name(index: usize) -> String {
    format!("litex_domain_fact_{}", index)
}

fn forall_parameter_requirement_fact(
    binding: &SymbolBinding,
    param_type: &ParamType,
) -> Option<Fact> {
    let parameter = obj_for_bound_param_in_scope(binding, ParamObjType::Forall);
    Some(match param_type {
        ParamType::Set(_) => return None,
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(parameter, default_line_file()).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(parameter, default_line_file()).into(),
        ParamType::Obj(set) => InFact::new(parameter, set.clone(), default_line_file()).into(),
    })
}

fn ensure_lean_binders_are_capture_free<'a>(
    groups: impl Iterator<Item = &'a ParamGroupWithParamType>,
    objects: Vec<&Obj>,
    line_file: &LineFile,
    context: &str,
) -> Result<(), RuntimeError> {
    let mut binders_by_id: HashMap<SymbolId, (String, String)> = HashMap::new();
    let mut binders_by_lean_name: HashMap<String, (SymbolId, String)> = HashMap::new();
    for group in groups {
        for binding in group.params.iter() {
            let emitted_name = lean_name(binding.name());
            if let Some((other_id, other_name)) = binders_by_lean_name.get(&emitted_name) {
                if *other_id != binding.id() {
                    return Err(lean_binder_name_collision_error(
                        line_file,
                        context,
                        other_name,
                        binding.name(),
                        &emitted_name,
                    ));
                }
            }
            binders_by_id.insert(
                binding.id(),
                (emitted_name.clone(), binding.name().to_string()),
            );
            binders_by_lean_name.insert(emitted_name, (binding.id(), binding.name().to_string()));
        }
    }

    for object in objects {
        let object_ir = LitexToLeanObjectIr::lower(object)
            .map_err(|message| litex_to_lean_error(line_file, message))?;
        ensure_obj_uses_capture_free_lean_names(
            &object_ir,
            &binders_by_id,
            &binders_by_lean_name,
            line_file,
            context,
        )?;
    }
    Ok(())
}

fn ensure_obj_uses_capture_free_lean_names(
    object: &LitexToLeanObjectIr,
    binders_by_id: &HashMap<SymbolId, (String, String)>,
    binders_by_lean_name: &HashMap<String, (SymbolId, String)>,
    line_file: &LineFile,
    context: &str,
) -> Result<(), RuntimeError> {
    match object {
        LitexToLeanObjectIr::Symbol { symbol_id, name } => {
            let emitted_name = lean_name(name);
            if let Some((binder_name, source_name)) = binders_by_id.get(symbol_id) {
                if emitted_name != *binder_name {
                    return Err(litex_to_lean_error(
                        line_file,
                        format!(
                            "Litex-to-Lean cannot safely emit the {context} binder `{source_name}` because one occurrence is named `{name}` after SymbolId resolution; preserve one binder spelling before compilation"
                        ),
                    ));
                }
            }
            if let Some((binder_id, binder_source_name)) = binders_by_lean_name.get(&emitted_name) {
                if symbol_id != binder_id {
                    return Err(lean_binder_name_collision_error(
                        line_file,
                        context,
                        binder_source_name,
                        name,
                        &emitted_name,
                    ));
                }
            }
        }
        LitexToLeanObjectIr::BuiltinApp { arguments, .. } => {
            for argument in arguments {
                ensure_obj_uses_capture_free_lean_names(
                    argument,
                    binders_by_id,
                    binders_by_lean_name,
                    line_file,
                    context,
                )?;
            }
        }
        LitexToLeanObjectIr::FunctionSet { function } => {
            for parameter in function.parameters.iter() {
                ensure_obj_uses_capture_free_lean_names(
                    &parameter.set,
                    binders_by_id,
                    binders_by_lean_name,
                    line_file,
                    context,
                )?;
            }
            ensure_obj_uses_capture_free_lean_names(
                &function.return_set,
                binders_by_id,
                binders_by_lean_name,
                line_file,
                context,
            )?;
        }
        LitexToLeanObjectIr::SetBuilder(builder) => {
            ensure_obj_uses_capture_free_lean_names(
                &builder.set,
                binders_by_id,
                binders_by_lean_name,
                line_file,
                context,
            )?;
            for fact in builder.facts.iter() {
                let mut objects = Vec::new();
                collect_fact_objects_for_lean_name_check(fact, &mut objects);
                for object in objects {
                    let lowered = LitexToLeanObjectIr::lower(object)
                        .map_err(|message| litex_to_lean_error(line_file, message))?;
                    ensure_obj_uses_capture_free_lean_names(
                        &lowered,
                        binders_by_id,
                        binders_by_lean_name,
                        line_file,
                        context,
                    )?;
                }
            }
        }
        LitexToLeanObjectIr::AnonymousFunction(function) => {
            for parameter in function.function.parameters.iter() {
                ensure_obj_uses_capture_free_lean_names(
                    &parameter.set,
                    binders_by_id,
                    binders_by_lean_name,
                    line_file,
                    context,
                )?;
            }
            ensure_obj_uses_capture_free_lean_names(
                &function.function.return_set,
                binders_by_id,
                binders_by_lean_name,
                line_file,
                context,
            )?;
            ensure_obj_uses_capture_free_lean_names(
                &function.body,
                binders_by_id,
                binders_by_lean_name,
                line_file,
                context,
            )?;
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            ensure_obj_uses_capture_free_lean_names(
                &application.head,
                binders_by_id,
                binders_by_lean_name,
                line_file,
                context,
            )?;
            for layer in application.argument_layers.iter() {
                for argument in layer {
                    ensure_obj_uses_capture_free_lean_names(
                        argument,
                        binders_by_id,
                        binders_by_lean_name,
                        line_file,
                        context,
                    )?;
                }
            }
        }
        LitexToLeanObjectIr::Collection { items, .. } => {
            for item in items {
                ensure_obj_uses_capture_free_lean_names(
                    item,
                    binders_by_id,
                    binders_by_lean_name,
                    line_file,
                    context,
                )?;
            }
        }
        LitexToLeanObjectIr::Number { .. }
        | LitexToLeanObjectIr::Constant(_)
        | LitexToLeanObjectIr::StandardSet(_) => {}
    }
    Ok(())
}

fn lean_binder_name_collision_error(
    line_file: &LineFile,
    context: &str,
    binder_name: &str,
    conflicting_name: &str,
    emitted_name: &str,
) -> RuntimeError {
    litex_to_lean_error(
        line_file,
        format!(
            "Litex-to-Lean cannot safely emit the {context} binder `{binder_name}` because Litex name `{conflicting_name}` also becomes Lean identifier `{emitted_name}`; rename one identifier"
        ),
    )
}

fn collect_forall_objects_for_lean_name_check<'a>(
    forall: &'a ForallFact,
    objects: &mut Vec<&'a Obj>,
) {
    for group in forall.params_def_with_type.groups.iter() {
        if let ParamType::Obj(carrier) = &group.param_type {
            objects.push(carrier);
        }
    }
    for premise in forall.dom_facts.iter() {
        collect_fact_objects_for_lean_name_check(premise, objects);
    }
    for conclusion in forall.then_facts.iter() {
        collect_forall_conclusion_objects_for_lean_name_check(conclusion, objects);
    }
}

fn collect_fact_objects_for_lean_name_check<'a>(fact: &'a Fact, objects: &mut Vec<&'a Obj>) {
    match fact {
        Fact::AtomicFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        Fact::ForallFact(fact) => collect_forall_objects_for_lean_name_check(fact, objects),
        Fact::ForallFactWithIff(fact) => {
            collect_forall_objects_for_lean_name_check(&fact.forall_fact, objects);
            for iff_fact in fact.iff_facts.iter() {
                collect_forall_conclusion_objects_for_lean_name_check(iff_fact, objects);
            }
        }
        Fact::NotForall(fact) => {
            collect_forall_objects_for_lean_name_check(&fact.forall_fact, objects)
        }
    }
}

fn collect_forall_conclusion_objects_for_lean_name_check<'a>(
    fact: &'a ExistOrAndChainAtomicFact,
    objects: &mut Vec<&'a Obj>,
) {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(fact) => {
            objects.extend(fact.get_args_from_fact_ref())
        }
        ExistOrAndChainAtomicFact::AndFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::ChainFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::OrFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
        ExistOrAndChainAtomicFact::ExistFact(fact) => objects.extend(fact.get_args_from_fact_ref()),
    }
}

fn lean_obj_with_context(
    obj: &Obj,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let ir = LitexToLeanObjectIr::lower(obj)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    if let Some(expected) = type_context.expected_object(obj) {
        let force_expectation = type_context
            .object_carrier(&ir)
            .map_err(|message| litex_to_lean_error(&default_line_file(), message))?
            .is_none();
        return lean_obj_ir_with_expected(&ir, expected, type_context, force_expectation);
    }
    lean_obj_ir_with_context(&ir, type_context)
}

fn lean_obj_ir_with_expected(
    obj: &LitexToLeanObjectIr,
    expected: &LitexToLeanCarrierIr,
    type_context: &LeanTypeContext,
    force_expectation: bool,
) -> Result<String, RuntimeError> {
    let text = lean_obj_ir_with_context(obj, type_context)?;
    let needs_expectation = type_context
        .needs_numeric_expectation(obj, expected)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    if !force_expectation && !needs_expectation {
        return Ok(text);
    }
    let lean_type = type_context
        .lean_type(expected)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    let annotated = text
        .strip_prefix('(')
        .and_then(|text| text.strip_suffix(')'))
        .unwrap_or(text.as_str());
    Ok(format!("({} : {})", annotated, lean_type))
}

pub(super) fn lean_function_type_with_context(
    function: &LitexToLeanFunctionTypeIr,
    outer_type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let mut type_context = outer_type_context.clone();
    for parameter in function.parameters.iter() {
        type_context.insert(parameter.symbol_id, parameter.element_carrier.clone());
    }

    let mut tail = type_context
        .lean_type(&function.return_carrier)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;

    for fact in function.domain_facts.iter().rev() {
        tail = format!(
            "{} → {}",
            lean_fact_with_context(fact, &type_context)?,
            tail
        );
    }
    for parameter in function.parameters.iter().rev() {
        if !parameter.requires_membership_proof {
            continue;
        }
        let parameter_obj = LitexToLeanObjectIr::Symbol {
            symbol_id: parameter.symbol_id,
            name: parameter.name.clone(),
        };
        let element = lean_obj_ir_with_expected(
            &parameter_obj,
            &parameter.element_carrier,
            &type_context,
            false,
        )?;
        let set = lean_obj_ir_with_context(&parameter.set, &type_context)?;
        tail = format!("{} ∈ {} → {}", element, set, tail);
    }
    for parameter in function.parameters.iter().rev() {
        let parameter_type = type_context
            .lean_type(&parameter.element_carrier)
            .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
        tail = format!(
            "({} : {}) → {}",
            lean_name(&parameter.name),
            parameter_type,
            tail
        );
    }
    Ok(tail)
}

fn lean_function_value_binders_with_context(
    function: &LitexToLeanFunctionTypeIr,
    outer_type_context: &LeanTypeContext,
) -> Result<(LeanTypeContext, Vec<String>, Vec<String>), RuntimeError> {
    let mut type_context = outer_type_context.clone();
    for parameter in function.parameters.iter() {
        type_context.insert(parameter.symbol_id, parameter.element_carrier.clone());
    }

    let mut binders = Vec::new();
    let mut arguments = Vec::new();
    for parameter in function.parameters.iter() {
        let name = lean_name(&parameter.name);
        let parameter_type = type_context
            .lean_type(&parameter.element_carrier)
            .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
        binders.push(format!("({name} : {parameter_type})"));
        arguments.push(name);
    }
    for (index, parameter) in function.parameters.iter().enumerate() {
        if !parameter.requires_membership_proof {
            continue;
        }
        let proof_name = format!("litex_fn_parameter_membership_{}", index + 1);
        let parameter_obj = LitexToLeanObjectIr::Symbol {
            symbol_id: parameter.symbol_id,
            name: parameter.name.clone(),
        };
        let proposition = format!(
            "{} ∈ {}",
            lean_obj_ir_with_expected(
                &parameter_obj,
                &parameter.element_carrier,
                &type_context,
                false,
            )?,
            lean_obj_ir_with_context(&parameter.set, &type_context)?,
        );
        binders.push(format!("({proof_name} : {proposition})"));
        arguments.push(proof_name.clone());
        let source_fact: Fact = InFact::new(
            obj_for_bound_param_from_function_parameter(parameter),
            parameter.source_set.clone(),
            default_line_file(),
        )
        .into();
        type_context.insert_parameter_well_definedness_proof(&source_fact, proof_name);
    }
    for (index, fact) in function.domain_facts.iter().enumerate() {
        let proof_name = format!("litex_fn_domain_{}", index + 1);
        binders.push(format!(
            "({proof_name} : {})",
            lean_fact_with_context(fact, &type_context)?
        ));
        arguments.push(proof_name.clone());
        type_context.insert_well_definedness_proof(fact, proof_name);
    }
    Ok((type_context, binders, arguments))
}

fn obj_for_bound_param_from_function_parameter(parameter: &LitexToLeanFunctionParameterIr) -> Obj {
    let binding = SymbolBinding::new(
        parameter.symbol_id,
        parameter.name.clone(),
        parameter.name.clone(),
    );
    obj_for_bound_param_in_scope(&binding, ParamObjType::FnSet)
}

fn lean_function_set_with_context(
    function: &LitexToLeanFunctionTypeIr,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let function_type = lean_function_type_with_context(function, type_context)?;
    if function.return_set.is_universal_native_set() {
        return Ok(format!("(Set.univ : Set ({function_type}))"));
    }

    let function_name = if function
        .parameters
        .iter()
        .any(|parameter| lean_name(&parameter.name) == "litex_function_value")
    {
        "litex_function_value_"
    } else {
        "litex_function_value"
    };
    let (local_context, binders, arguments) =
        lean_function_value_binders_with_context(function, type_context)?;
    let application = if arguments.is_empty() {
        function_name.to_string()
    } else {
        format!("{} {}", function_name, arguments.join(" "))
    };
    let return_set = lean_obj_ir_with_context(&function.return_set, &local_context)?;
    let predicate = format!("({application}) ∈ {return_set}");
    let predicate = if binders.is_empty() {
        predicate
    } else {
        format!("∀ {}, {predicate}", binders.join(" "))
    };
    Ok(format!(
        "{{{function_name} : ({function_type}) | {predicate}}}"
    ))
}

fn lean_set_builder_with_context(
    builder: &LitexToLeanSetBuilderIr,
    outer_type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let mut type_context = outer_type_context.clone();
    type_context.insert(builder.symbol_id, builder.element_carrier.clone());
    let parameter = LitexToLeanObjectIr::Symbol {
        symbol_id: builder.symbol_id,
        name: builder.name.clone(),
    };
    let parameter_text =
        lean_obj_ir_with_expected(&parameter, &builder.element_carrier, &type_context, false)?;
    let set_text = lean_obj_ir_with_context(&builder.set, &type_context)?;
    let mut predicates = vec![format!("{parameter_text} ∈ {set_text}")];
    predicates.extend(
        builder
            .facts
            .iter()
            .map(|fact| lean_fact_with_context(fact, &type_context))
            .collect::<Result<Vec<_>, RuntimeError>>()?,
    );
    let element_type = type_context
        .lean_type(&builder.element_carrier)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
    Ok(format!(
        "{{{} : {} | {}}}",
        lean_name(&builder.name),
        element_type,
        lean_right_associated_conjunction(&predicates)
    ))
}

fn lean_anonymous_function_with_context(
    anonymous: &LitexToLeanAnonymousFunctionIr,
    outer_type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let (type_context, binders, _) =
        lean_function_value_binders_with_context(&anonymous.function, outer_type_context)?;
    let body = lean_obj_ir_with_expected(
        &anonymous.body,
        &anonymous.function.return_carrier,
        &type_context,
        false,
    )?;
    if binders.is_empty() {
        Ok(body)
    } else {
        Ok(format!("(fun {} => {})", binders.join(" "), body))
    }
}

fn lean_function_application_with_context(
    application: &LitexToLeanFunctionApplicationIr,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let mut rendered = lean_obj_ir_with_context(&application.head, type_context)?;
    let Some(mut carrier) = type_context
        .object_carrier(&application.head)
        .map_err(|message| litex_to_lean_error(&default_line_file(), message))?
    else {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "Litex-to-Lean cannot determine the retained function signature for an application head",
        ));
    };

    for (layer_index, arguments) in application.argument_layers.iter().enumerate() {
        let resolved = type_context
            .resolve_carrier(&carrier)
            .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
        let LitexToLeanCarrierIr::Function { function } = resolved else {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean function application layer {} has a non-function retained carrier",
                    layer_index + 1
                ),
            ));
        };
        if arguments.len() != function.parameters.len() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean function application layer {} has {} arguments but its retained signature requires {}",
                    layer_index + 1,
                    arguments.len(),
                    function.parameters.len()
                ),
            ));
        }
        let Some(source_arguments) = application.source_argument_layers.get(layer_index) else {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean function application layer {} lost its source arguments",
                    layer_index + 1
                ),
            ));
        };
        if source_arguments.len() != arguments.len() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean function application layer {} has mismatched structural and source argument arities",
                    layer_index + 1
                ),
            ));
        }
        for (argument, parameter) in arguments.iter().zip(function.parameters.iter()) {
            rendered.push(' ');
            rendered.push_str(&lean_obj_ir_with_expected(
                argument,
                &parameter.element_carrier,
                type_context,
                false,
            )?);
        }
        let mut substitutions = HashMap::new();
        for (parameter, source_argument) in function.parameters.iter().zip(source_arguments.iter())
        {
            substitutions.insert(parameter.name.clone(), source_argument.clone());
            substitutions.insert(parameter.substitution_key.clone(), source_argument.clone());
        }
        let instantiator = Runtime::new();
        for (parameter_index, (parameter, source_argument)) in function
            .parameters
            .iter()
            .zip(source_arguments.iter())
            .enumerate()
        {
            if !parameter.requires_membership_proof {
                continue;
            }
            let instantiated_set = instantiator
                .inst_obj(&parameter.source_set, &substitutions, ParamObjType::FnSet)
                .map_err(|error| {
                    litex_to_lean_error(
                        &default_line_file(),
                        format!(
                            "failed to instantiate function parameter membership for Litex-to-Lean: {}",
                            error.trace_message()
                        ),
                    )
                })?;
            let requirement: Fact = InFact::new(
                source_argument.clone(),
                instantiated_set,
                default_line_file(),
            )
            .into();
            let (_, proof_name) = type_context
                .function_requirement_proof(
                    &application.source_application,
                    WellDefinednessRequirementRole::FunctionArgumentMembership {
                        layer_index,
                        parameter_index,
                    },
                    &requirement,
                )
                .map_err(|message| {
                    litex_to_lean_error(
                        &default_line_file(),
                        format!(
                            "Litex-to-Lean function application layer {} cannot use membership proof `{}`: {}",
                            layer_index + 1,
                            requirement,
                            message,
                        ),
                    )
                })?;
            rendered.push(' ');
            rendered.push_str(proof_name);
        }
        for (domain_index, source_domain) in function.domain_facts.iter().enumerate() {
            let requirement = instantiator
                .inst_fact(source_domain, &substitutions, ParamObjType::FnSet, None)
                .map_err(|error| {
                    litex_to_lean_error(
                        &source_domain.line_file(),
                        format!(
                            "failed to instantiate function-domain evidence for Litex-to-Lean: {}",
                            error.trace_message()
                        ),
                    )
                })?;
            let (_, proof_name) = type_context
                .function_requirement_proof(
                    &application.source_application,
                    WellDefinednessRequirementRole::FunctionDomain {
                        layer_index,
                        domain_index,
                    },
                    &requirement,
                )
                .map_err(|message| {
                    litex_to_lean_error(
                        &requirement.line_file(),
                        format!(
                            "Litex-to-Lean function application layer {} cannot use domain proof `{}`: {}",
                            layer_index + 1,
                            requirement,
                            message,
                        ),
                    )
                })?;
            rendered.push(' ');
            rendered.push_str(proof_name);
        }
        carrier = (*function.return_carrier).clone();
    }
    Ok(format!("({})", rendered))
}

/// Apply an extensional function-space membership proof through the same exact
/// source layers and WD proof slots used by the corresponding value term.
/// Values precede membership proofs, which precede domain proofs in every
/// layer; no currying or argument regrouping is inferred here.
fn lean_function_membership_elimination_with_context(
    head_proof: &str,
    application: &LitexToLeanFunctionApplicationIr,
    initial_function: &LitexToLeanFunctionTypeIr,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let mut rendered = head_proof.to_string();
    let mut current_function = initial_function.clone();
    let instantiator = Runtime::new();

    for (layer_index, arguments) in application.argument_layers.iter().enumerate() {
        let function = &current_function;
        if arguments.len() != function.parameters.len() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "function-membership elimination layer {} has {} arguments but its retained signature requires {}",
                    layer_index + 1,
                    arguments.len(),
                    function.parameters.len()
                ),
            ));
        }
        let Some(source_arguments) = application.source_argument_layers.get(layer_index) else {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "function-membership elimination layer {} lost its source arguments",
                    layer_index + 1
                ),
            ));
        };
        if source_arguments.len() != arguments.len() {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "function-membership elimination layer {} has mismatched source and structural arities",
                    layer_index + 1
                ),
            ));
        }

        for (argument, parameter) in arguments.iter().zip(function.parameters.iter()) {
            rendered.push(' ');
            rendered.push_str(&lean_obj_ir_with_expected(
                argument,
                &parameter.element_carrier,
                type_context,
                false,
            )?);
        }

        let mut substitutions = HashMap::new();
        for (parameter, source_argument) in function.parameters.iter().zip(source_arguments.iter())
        {
            substitutions.insert(parameter.name.clone(), source_argument.clone());
            substitutions.insert(parameter.substitution_key.clone(), source_argument.clone());
        }
        for (parameter_index, (parameter, source_argument)) in function
            .parameters
            .iter()
            .zip(source_arguments.iter())
            .enumerate()
        {
            if !parameter.requires_membership_proof {
                continue;
            }
            let instantiated_set = instantiator
                .inst_obj(&parameter.source_set, &substitutions, ParamObjType::FnSet)
                .map_err(|error| {
                    litex_to_lean_error(
                        &default_line_file(),
                        format!(
                            "failed to instantiate function-membership elimination parameter: {}",
                            error.trace_message()
                        ),
                    )
                })?;
            let requirement: Fact = InFact::new(
                source_argument.clone(),
                instantiated_set,
                default_line_file(),
            )
            .into();
            let (_, proof_name) = type_context
                .function_requirement_proof(
                    &application.source_application,
                    WellDefinednessRequirementRole::FunctionArgumentMembership {
                        layer_index,
                        parameter_index,
                    },
                    &requirement,
                )
                .map_err(|message| {
                    litex_to_lean_error(
                        &requirement.line_file(),
                        format!(
                            "function-membership elimination layer {} cannot use membership proof `{}`: {}",
                            layer_index + 1,
                            requirement,
                            message
                        ),
                    )
                })?;
            rendered.push(' ');
            rendered.push_str(proof_name);
        }
        for (domain_index, source_domain) in function.domain_facts.iter().enumerate() {
            let requirement = instantiator
                .inst_fact(source_domain, &substitutions, ParamObjType::FnSet, None)
                .map_err(|error| {
                    litex_to_lean_error(
                        &source_domain.line_file(),
                        format!(
                            "failed to instantiate function-membership elimination domain: {}",
                            error.trace_message()
                        ),
                    )
                })?;
            let (_, proof_name) = type_context
                .function_requirement_proof(
                    &application.source_application,
                    WellDefinednessRequirementRole::FunctionDomain {
                        layer_index,
                        domain_index,
                    },
                    &requirement,
                )
                .map_err(|message| {
                    litex_to_lean_error(
                        &requirement.line_file(),
                        format!(
                            "function-membership elimination layer {} cannot use domain proof `{}`: {}",
                            layer_index + 1,
                            requirement,
                            message
                        ),
                    )
                })?;
            rendered.push(' ');
            rendered.push_str(proof_name);
        }

        if layer_index + 1 < application.argument_layers.len() {
            let resolved = type_context
                .resolve_carrier(function.return_carrier.as_ref())
                .map_err(|message| litex_to_lean_error(&default_line_file(), message))?;
            let LitexToLeanCarrierIr::Function { function: next } = resolved else {
                return Err(litex_to_lean_error(
                    &default_line_file(),
                    format!(
                        "function-membership elimination layer {} has a non-function intermediate return carrier",
                        layer_index + 1
                    ),
                ));
            };
            current_function = (*next).clone();
        }
    }

    Ok(format!("({rendered})"))
}

pub(super) fn lean_obj_ir_with_context(
    obj: &LitexToLeanObjectIr,
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    match obj {
        LitexToLeanObjectIr::Symbol { name, .. } => Ok(lean_name(name)),
        LitexToLeanObjectIr::Number { normalized_value } => {
            if is_safe_lean_decimal_literal(normalized_value) {
                Ok(normalized_value.clone())
            } else {
                Err(litex_to_lean_error(
                    &default_line_file(),
                    format!(
                        "Litex-to-Lean cannot emit nonnumeric normalized literal `{normalized_value}`"
                    ),
                ))
            }
        }
        LitexToLeanObjectIr::Constant(constant) => Ok(match constant {
            LitexToLeanConstantObjectIr::ImaginaryUnit => "Complex.I",
            LitexToLeanConstantObjectIr::EulerNumber => "Real.exp 1",
            LitexToLeanConstantObjectIr::Pi => "Real.pi",
        }
        .to_string()),
        LitexToLeanObjectIr::StandardSet(set) => Ok(lean_standard_set_name(*set).to_string()),
        LitexToLeanObjectIr::FunctionSet { function } => {
            lean_function_set_with_context(function, type_context)
        }
        LitexToLeanObjectIr::SetBuilder(builder) => {
            lean_set_builder_with_context(builder, type_context)
        }
        LitexToLeanObjectIr::AnonymousFunction(function) => {
            lean_anonymous_function_with_context(function, type_context)
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            lean_function_application_with_context(application, type_context)
        }
        LitexToLeanObjectIr::BuiltinApp {
            operator,
            arguments,
        } => lean_builtin_obj_application(*operator, arguments, type_context),
        LitexToLeanObjectIr::Collection {
            constructor: LitexToLeanCollectionObjectIr::ListSet,
            items,
        } => {
            if items.is_empty() {
                return Ok("∅".to_string());
            }
            Ok(format!(
                "{{{}}}",
                items
                    .iter()
                    .map(|item| lean_obj_ir_with_context(item, type_context))
                    .collect::<Result<Vec<_>, RuntimeError>>()?
                    .join(", ")
            ))
        }
    }
}

fn is_safe_lean_decimal_literal(value: &str) -> bool {
    let magnitude = value.strip_prefix('-').unwrap_or(value);
    if magnitude.is_empty() {
        return false;
    }
    let mut parts = magnitude.split('.');
    let Some(integer) = parts.next() else {
        return false;
    };
    if integer.is_empty() || !integer.chars().all(|character| character.is_ascii_digit()) {
        return false;
    }
    match (parts.next(), parts.next()) {
        (None, None) => true,
        (Some(fraction), None) => {
            !fraction.is_empty() && fraction.chars().all(|character| character.is_ascii_digit())
        }
        _ => false,
    }
}

fn lean_builtin_obj_application(
    operator: LitexToLeanBuiltinObjectOperatorIr,
    arguments: &[LitexToLeanObjectIr],
    type_context: &LeanTypeContext,
) -> Result<String, RuntimeError> {
    let rendered = arguments
        .iter()
        .enumerate()
        .map(|(argument_index, argument)| {
            if let Some(carrier) = operator.intrinsic_argument_carrier(argument_index) {
                // This expectation is part of the Litex operator contract, not
                // merely a coercion hint. In particular, bare numerals in `%`
                // must elaborate as integers even when the surrounding fact
                // supplies no carrier information.
                lean_obj_ir_with_expected(argument, &carrier, type_context, true)
            } else {
                lean_obj_ir_with_context(argument, type_context)
            }
        })
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let expected_arity = match operator {
        LitexToLeanBuiltinObjectOperatorIr::Floor
        | LitexToLeanBuiltinObjectOperatorIr::Ceil
        | LitexToLeanBuiltinObjectOperatorIr::Exp
        | LitexToLeanBuiltinObjectOperatorIr::Ln
        | LitexToLeanBuiltinObjectOperatorIr::Sign
        | LitexToLeanBuiltinObjectOperatorIr::Factorial
        | LitexToLeanBuiltinObjectOperatorIr::Abs
        | LitexToLeanBuiltinObjectOperatorIr::Sin
        | LitexToLeanBuiltinObjectOperatorIr::Cos
        | LitexToLeanBuiltinObjectOperatorIr::Tan
        | LitexToLeanBuiltinObjectOperatorIr::Cot
        | LitexToLeanBuiltinObjectOperatorIr::RealPart
        | LitexToLeanBuiltinObjectOperatorIr::ImaginaryPart
        | LitexToLeanBuiltinObjectOperatorIr::ComplexAbs
        | LitexToLeanBuiltinObjectOperatorIr::Sqrt
        | LitexToLeanBuiltinObjectOperatorIr::BigUnion
        | LitexToLeanBuiltinObjectOperatorIr::BigIntersect
        | LitexToLeanBuiltinObjectOperatorIr::PowerSet => 1,
        _ => 2,
    };
    if rendered.len() != expected_arity {
        return Err(litex_to_lean_error(
            &default_line_file(),
            format!(
                "Litex-to-Lean Obj IR operator {:?} expects {} arguments but received {}",
                operator,
                expected_arity,
                rendered.len()
            ),
        ));
    }

    let result = match operator {
        LitexToLeanBuiltinObjectOperatorIr::Add => format!("({} + {})", rendered[0], rendered[1]),
        LitexToLeanBuiltinObjectOperatorIr::Sub => format!("({} - {})", rendered[0], rendered[1]),
        LitexToLeanBuiltinObjectOperatorIr::Mul => format!("({} * {})", rendered[0], rendered[1]),
        LitexToLeanBuiltinObjectOperatorIr::Div => format!("({} / {})", rendered[0], rendered[1]),
        LitexToLeanBuiltinObjectOperatorIr::Pow => format!("({} ^ {})", rendered[0], rendered[1]),
        LitexToLeanBuiltinObjectOperatorIr::Mod => format!("({} % {})", rendered[0], rendered[1]),
        LitexToLeanBuiltinObjectOperatorIr::Min => named_binary("min", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Max => named_binary("max", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Exp => named_unary("Real.exp", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Ln => named_unary("Real.log", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Abs => named_unary("abs", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Sin => named_unary("Real.sin", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Cos => named_unary("Real.cos", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Tan => named_unary("Real.tan", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::RealPart => named_unary("Complex.re", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::ImaginaryPart => named_unary("Complex.im", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::ComplexAbs => named_unary("Complex.abs", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Sqrt => named_unary("Real.sqrt", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Union => {
            format!("({} ∪ {})", rendered[0], rendered[1])
        }
        LitexToLeanBuiltinObjectOperatorIr::Intersect => {
            format!("({} ∩ {})", rendered[0], rendered[1])
        }
        LitexToLeanBuiltinObjectOperatorIr::SetMinus => {
            format!("({} \\ {})", rendered[0], rendered[1])
        }
        LitexToLeanBuiltinObjectOperatorIr::BigUnion => named_unary("Set.sUnion", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::BigIntersect => named_unary("Set.sInter", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::PowerSet => named_unary("Set.powerset", &rendered),
        LitexToLeanBuiltinObjectOperatorIr::Gcd
        | LitexToLeanBuiltinObjectOperatorIr::Lcm
        | LitexToLeanBuiltinObjectOperatorIr::Floor
        | LitexToLeanBuiltinObjectOperatorIr::Ceil
        | LitexToLeanBuiltinObjectOperatorIr::Sign
        | LitexToLeanBuiltinObjectOperatorIr::Factorial
        | LitexToLeanBuiltinObjectOperatorIr::Cot
        | LitexToLeanBuiltinObjectOperatorIr::Log => {
            return Err(litex_to_lean_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean native object ABI has no checked Mathlib lowering for {:?}",
                    operator
                ),
            ));
        }
    };
    Ok(result)
}

fn set_equality_matches_builtin_rule(
    proposition: &Fact,
    rule: LitexToLeanSetBuiltinRuleIr,
) -> bool {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
        return false;
    };
    use LitexToLeanSetBuiltinRuleIr::*;
    let same = |left: &Obj, right: &Obj| obj_equality_key(left) == obj_equality_key(right);
    let empty = |obj: &Obj| matches!(obj, Obj::ListSet(set) if set.list.is_empty());
    let union_assoc = |left: &Obj, right: &Obj| {
        let Obj::Union(outer) = left else {
            return false;
        };
        let Obj::Union(left_inner) = outer.left.as_ref() else {
            return false;
        };
        let Obj::Union(right_outer) = right else {
            return false;
        };
        let Obj::Union(right_inner) = right_outer.right.as_ref() else {
            return false;
        };
        same(left_inner.left.as_ref(), right_outer.left.as_ref())
            && same(left_inner.right.as_ref(), right_inner.left.as_ref())
            && same(outer.right.as_ref(), right_inner.right.as_ref())
    };
    let intersect_assoc = |left: &Obj, right: &Obj| {
        let Obj::Intersect(outer) = left else {
            return false;
        };
        let Obj::Intersect(left_inner) = outer.left.as_ref() else {
            return false;
        };
        let Obj::Intersect(right_outer) = right else {
            return false;
        };
        let Obj::Intersect(right_inner) = right_outer.right.as_ref() else {
            return false;
        };
        same(left_inner.left.as_ref(), right_outer.left.as_ref())
            && same(left_inner.right.as_ref(), right_inner.left.as_ref())
            && same(outer.right.as_ref(), right_inner.right.as_ref())
    };
    match rule {
        UnionCommutative => match (&equality.left, &equality.right) {
            (Obj::Union(left), Obj::Union(right)) => {
                same(left.left.as_ref(), right.right.as_ref())
                    && same(left.right.as_ref(), right.left.as_ref())
            }
            _ => false,
        },
        UnionAssociative => {
            union_assoc(&equality.left, &equality.right)
                || union_assoc(&equality.right, &equality.left)
        }
        UnionIdempotent => match (&equality.left, &equality.right) {
            (Obj::Union(union), other) | (other, Obj::Union(union)) => {
                same(union.left.as_ref(), union.right.as_ref()) && same(union.left.as_ref(), other)
            }
            _ => false,
        },
        UnionEmptyIdentity => match (&equality.left, &equality.right) {
            (Obj::Union(union), other) | (other, Obj::Union(union)) => {
                (empty(union.left.as_ref()) && same(union.right.as_ref(), other))
                    || (empty(union.right.as_ref()) && same(union.left.as_ref(), other))
            }
            _ => false,
        },
        IntersectCommutative => match (&equality.left, &equality.right) {
            (Obj::Intersect(left), Obj::Intersect(right)) => {
                same(left.left.as_ref(), right.right.as_ref())
                    && same(left.right.as_ref(), right.left.as_ref())
            }
            _ => false,
        },
        IntersectAssociative => {
            intersect_assoc(&equality.left, &equality.right)
                || intersect_assoc(&equality.right, &equality.left)
        }
        _ => false,
    }
}

fn is_negation_of_obj(obj: &Obj, expected: &Obj) -> bool {
    let Obj::Mul(mul) = obj else { return false };
    let is_neg_one =
        |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "-1");
    (is_neg_one(mul.left.as_ref())
        && obj_equality_key(mul.right.as_ref()) == obj_equality_key(expected))
        || (is_neg_one(mul.right.as_ref())
            && obj_equality_key(mul.left.as_ref()) == obj_equality_key(expected))
}

fn abs_identity_target(
    target: &EqualFact,
    rule: LitexToLeanAbsoluteValueBuiltinRuleIr,
) -> Result<(&Obj, bool), RuntimeError> {
    for (abs_side, other, reversed) in [
        (&target.left, &target.right, false),
        (&target.right, &target.left, true),
    ] {
        let Obj::Abs(abs) = abs_side else { continue };
        let matches = match rule {
            LitexToLeanAbsoluteValueBuiltinRuleIr::NonnegativeIdentity => {
                obj_equality_key(abs.arg.as_ref()) == obj_equality_key(other)
            }
            LitexToLeanAbsoluteValueBuiltinRuleIr::NonpositiveNegation => {
                is_negation_of_obj(other, abs.arg.as_ref())
            }
            _ => false,
        };
        if matches {
            return Ok((abs.arg.as_ref(), reversed));
        }
    }
    Err(litex_to_lean_error(
        &target.line_file,
        "absolute-value equality target has the wrong shape",
    ))
}

fn abs_product_equality_shape(proposition: &Fact) -> bool {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
        return false;
    };
    let matches = |abs_side: &Obj, product_side: &Obj| {
        let Obj::Abs(abs) = abs_side else {
            return false;
        };
        let Obj::Mul(inner) = abs.arg.as_ref() else {
            return false;
        };
        let Obj::Mul(product) = product_side else {
            return false;
        };
        let (Obj::Abs(left_abs), Obj::Abs(right_abs)) =
            (product.left.as_ref(), product.right.as_ref())
        else {
            return false;
        };
        obj_equality_key(inner.left.as_ref()) == obj_equality_key(left_abs.arg.as_ref())
            && obj_equality_key(inner.right.as_ref()) == obj_equality_key(right_abs.arg.as_ref())
    };
    matches(&equality.left, &equality.right) || matches(&equality.right, &equality.left)
}

fn abs_positive_target(proposition: &Fact) -> Result<(&Obj, bool), RuntimeError> {
    match proposition {
        Fact::AtomicFact(AtomicFact::LessFact(fact)) if fact.left.to_string() == "0" => {
            match &fact.right {
                Obj::Abs(abs) => Ok((abs.arg.as_ref(), false)),
                _ => Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "absolute-value positivity target has the wrong shape",
                )),
            }
        }
        Fact::AtomicFact(AtomicFact::GreaterFact(fact)) if fact.right.to_string() == "0" => {
            match &fact.left {
                Obj::Abs(abs) => Ok((abs.arg.as_ref(), false)),
                _ => Err(litex_to_lean_error(
                    &proposition.line_file(),
                    "absolute-value positivity target has the wrong shape",
                )),
            }
        }
        _ => Err(litex_to_lean_error(
            &proposition.line_file(),
            "absolute-value positivity target has the wrong shape",
        )),
    }
}

fn named_unary(name: &str, arguments: &[String]) -> String {
    format!("({} {})", name, arguments[0])
}

fn named_binary(name: &str, arguments: &[String]) -> String {
    format!("({} {} {})", name, arguments[0], arguments[1])
}

fn lean_rational_builtin_proof(
    proposition: &Fact,
    context: &LeanProofContext,
) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "rational-expression evidence was attached to a non-equality",
        ));
    };
    let left = LeanRationalExpression::from_obj(&equality.left)?;
    let right = LeanRationalExpression::from_obj(&equality.right)?;
    let closed_numeric =
        closed_rational_expression(&equality.left) && closed_rational_expression(&equality.right);
    let tactic = rational_tactic(&left, &right, closed_numeric, &context.nonzero_names);
    let mut lines = vec![
        "by".to_string(),
        format!("  -- native proof view, left fraction: {}", left.fraction()),
        format!(
            "  -- native proof view, right fraction: {}",
            right.fraction()
        ),
    ];
    lines.push(format!("  {}", tactic.replace('\n', "\n  ")));
    Ok(lines.join("\n"))
}

fn rational_tactic(
    left: &LeanRationalExpression,
    right: &LeanRationalExpression,
    closed_numeric: bool,
    nonzero_names: &[String],
) -> String {
    if closed_numeric {
        return "norm_num".to_string();
    }
    if !left.has_denominator() && !right.has_denominator() {
        return "ring".to_string();
    }
    let field_simp = if nonzero_names.is_empty() {
        "field_simp".to_string()
    } else {
        format!("field_simp [{}]", nonzero_names.join(", "))
    };
    format!("{} <;> ring", field_simp)
}

fn rational_fact_normalization_tactic(
    source: &Fact,
    goal: &Fact,
    context: &LeanProofContext,
) -> Result<String, RuntimeError> {
    let (Fact::AtomicFact(source), Fact::AtomicFact(goal)) = (source, goal) else {
        return Err(litex_to_lean_error(
            &goal.line_file(),
            "fact normalization currently requires atomic source and target facts",
        ));
    };
    if source.key() != goal.key() || source.is_true() != goal.is_true() {
        return Err(litex_to_lean_error(
            &goal.line_file(),
            "fact normalization source and target have different proposition shapes",
        ));
    }

    let source_args = source.args_ref();
    let goal_args = goal.args_ref();
    if source_args.len() != goal_args.len() {
        return Err(litex_to_lean_error(
            &goal.line_file(),
            "fact normalization source and target have different arities",
        ));
    }

    let mut changed = false;
    let mut all_closed = true;
    let mut has_denominator = false;
    for (source_arg, goal_arg) in source_args.iter().zip(goal_args.iter()) {
        if obj_equality_key(source_arg) == obj_equality_key(goal_arg) {
            continue;
        }
        let Some(stats) = nested_rational_normalization_stats(source_arg, goal_arg)? else {
            return Err(litex_to_lean_error(
                &goal.line_file(),
                format!(
                    "fact normalization argument `{}` is not rationally equal to `{}`",
                    source_arg, goal_arg
                ),
            ));
        };
        changed = true;
        all_closed &= stats.all_closed;
        has_denominator |= stats.has_denominator;
    }

    if !changed {
        return Ok("rfl".to_string());
    }
    if all_closed {
        return Ok("norm_num".to_string());
    }
    if !has_denominator {
        return Ok("ring".to_string());
    }
    if context.nonzero_names.is_empty() {
        return Ok("field_simp <;> ring".to_string());
    }
    Ok(format!(
        "field_simp [{}] <;> ring",
        context.nonzero_names.join(", ")
    ))
}

#[derive(Clone, Copy)]
struct NestedRationalNormalizationStats {
    all_closed: bool,
    has_denominator: bool,
}

fn nested_rational_normalization_stats(
    source: &Obj,
    goal: &Obj,
) -> Result<Option<NestedRationalNormalizationStats>, RuntimeError> {
    if obj_equality_key(source) == obj_equality_key(goal) {
        return Ok(Some(NestedRationalNormalizationStats {
            all_closed: true,
            has_denominator: false,
        }));
    }
    if objs_equal_by_rational_expression_evaluation(source, goal) {
        return Ok(Some(NestedRationalNormalizationStats {
            all_closed: closed_rational_expression(source) && closed_rational_expression(goal),
            has_denominator: LeanRationalExpression::from_obj(source)?.has_denominator()
                || LeanRationalExpression::from_obj(goal)?.has_denominator(),
        }));
    }

    let mut aggregate = NestedRationalNormalizationStats {
        all_closed: true,
        has_denominator: false,
    };
    let result: Result<bool, RuntimeError> = Runtime::same_shape_and_corresponding_args_match(
        source,
        goal,
        &mut |source_arg, goal_arg| {
            let Some(stats) = nested_rational_normalization_stats(source_arg, goal_arg)? else {
                return Ok(false);
            };
            aggregate.all_closed &= stats.all_closed;
            aggregate.has_denominator |= stats.has_denominator;
            Ok(true)
        },
    );
    if result? {
        Ok(Some(aggregate))
    } else {
        Ok(None)
    }
}

fn lean_real_set_nonempty(proposition: &Fact) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) = proposition else {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "real-set nonemptiness evidence was attached to a different fact family",
        ));
    };
    if !matches!(fact.set, Obj::StandardSet(StandardSet::R)) {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "real-set nonemptiness evidence was attached to a non-real carrier",
        ));
    }
    Ok("by\n  refine ⟨0, ?_⟩\n  exact Set.mem_univ 0".to_string())
}

fn lean_standard_set_nonempty(proposition: &Fact) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) = proposition else {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "standard-set nonemptiness evidence was attached to a different fact family",
        ));
    };
    let Obj::StandardSet(set) = &fact.set else {
        return Err(litex_to_lean_error(
            &proposition.line_file(),
            "standard-set nonemptiness evidence requires a standard set",
        ));
    };
    let witness = match set {
        StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::C => "0",
        StandardSet::NPos | StandardSet::QPos | StandardSet::RPos => "1",
        StandardSet::QNeg | StandardSet::ZNeg | StandardSet::RNeg => "-1",
        StandardSet::QStar | StandardSet::ZStar | StandardSet::RStar | StandardSet::CStar => "1",
        StandardSet::R => {
            return Err(litex_to_lean_error(
                &proposition.line_file(),
                "real standard-set nonemptiness should use the dedicated backend",
            ))
        }
    };
    if matches!(
        set,
        StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::C
    ) {
        Ok(format!(
            "by\n  refine ⟨{}, ?_⟩\n  exact Set.mem_univ {}",
            witness, witness
        ))
    } else {
        Ok(format!("by\n  refine ⟨{}, ?_⟩\n  norm_num", witness))
    }
}

fn validate_object_choice(choice: &LitexToLeanObjectChoiceIr) -> Result<FactId, RuntimeError> {
    if choice.nonempty_proof.fact_id.is_some() {
        return Err(litex_to_lean_error(
            &choice.nonempty_proof.proposition.line_file(),
            "object-choice nonemptiness proof must be a verification-only node",
        ));
    }
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) =
        &choice.nonempty_proof.proposition
    else {
        return Err(litex_to_lean_error(
            &choice.nonempty_proof.proposition.line_file(),
            "object-choice source is not a nonempty-set fact",
        ));
    };
    let nonempty_carrier = LitexToLeanObjectIr::lower(&nonempty.set).map_err(|message| {
        litex_to_lean_error(&choice.nonempty_proof.proposition.line_file(), message)
    })?;
    if nonempty_carrier != choice.carrier {
        return Err(litex_to_lean_error(
            &choice.nonempty_proof.proposition.line_file(),
            "object-choice nonemptiness proof does not match its selected carrier",
        ));
    }

    let LitexToLeanFactProofIr::ObjectChoice {
        definition,
        carrier,
    } = &choice.membership.proof
    else {
        return Err(litex_to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership has no choice-introduction evidence",
        ));
    };
    if definition != &choice.name || carrier != &choice.carrier {
        return Err(litex_to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership evidence does not match its definition",
        ));
    }
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = &choice.membership.proposition else {
        return Err(litex_to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice stored fact is not a membership fact",
        ));
    };
    let membership_carrier = LitexToLeanObjectIr::lower(&membership.set).map_err(|message| {
        litex_to_lean_error(&choice.membership.proposition.line_file(), message)
    })?;
    if membership_carrier != choice.carrier {
        return Err(litex_to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership uses a different carrier",
        ));
    }
    let selected = LitexToLeanObjectIr::lower(&membership.element).map_err(|message| {
        litex_to_lean_error(&choice.membership.proposition.line_file(), message)
    })?;
    if !matches!(
        selected,
        LitexToLeanObjectIr::Symbol { symbol_id, .. } if symbol_id == choice.symbol_id
    ) {
        return Err(litex_to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership uses a different selected symbol",
        ));
    }
    required_fact_id(&choice.membership)
}

const EXIST_SOURCE_PLACEHOLDER: &str = "__litex_checked_exist_source__";

struct ExistentialEliminationLayout {
    witness_terms: Vec<String>,
    proof_terms: Vec<String>,
}

fn validate_existential_elimination(
    ir: &LitexToLeanHaveExistentialWitnessIr,
) -> Result<ExistentialEliminationLayout, RuntimeError> {
    if ir.source.fact_id.is_some() {
        return Err(litex_to_lean_error(
            &ir.source.proposition.line_file(),
            "existential-elimination source must be a verification-only node",
        ));
    }
    let Fact::ExistFact(ExistFactEnum::ExistFact(body)) = &ir.source.proposition else {
        return Err(litex_to_lean_error(
            &ir.source.proposition.line_file(),
            "existential-elimination source is not a positive `exist` fact",
        ));
    };
    lean_fact(&ir.source.proposition)?;
    let param_types = flattened_exist_param_types(&body);
    if ir.witnesses.is_empty()
        || ir.witnesses.len() != param_types.len()
        || ir.projections.len() != ir.witnesses.len() + body.facts.len()
    {
        return Err(litex_to_lean_error(
            &ir.source.proposition.line_file(),
            "existential-elimination witness or projection count does not match its source",
        ));
    }

    let mut symbol_ids = HashSet::new();
    for (witness, source_type) in ir.witnesses.iter().zip(param_types.iter()) {
        if !symbol_ids.insert(witness.symbol_id) {
            return Err(litex_to_lean_error(
                &ir.source.proposition.line_file(),
                "existential-elimination witness symbols must be distinct",
            ));
        }
        let family_matches = matches!(
            (source_type, &witness.param_type),
            (ParamType::Set(_), LitexToLeanParameterTypeIr::Set { .. })
                | (
                    ParamType::NonemptySet(_),
                    LitexToLeanParameterTypeIr::NonemptySet { .. }
                )
                | (
                    ParamType::FiniteSet(_),
                    LitexToLeanParameterTypeIr::FiniteSet { .. }
                )
                | (
                    ParamType::Obj(_),
                    LitexToLeanParameterTypeIr::MemberOf { .. }
                )
        );
        if !family_matches {
            return Err(litex_to_lean_error(
                &ir.source.proposition.line_file(),
                "existential-elimination witness type family does not match its source binder",
            ));
        }
    }

    let mut fact_ids = HashSet::new();
    for (index, projection) in ir.projections.iter().enumerate() {
        let fact_id = required_fact_id(projection)?;
        if !fact_ids.insert(fact_id) {
            return Err(litex_to_lean_error(
                &projection.proposition.line_file(),
                "existential-elimination projection FactIds must be distinct",
            ));
        }
        let LitexToLeanFactProofIr::ExistentialElimination {
            source_proposition,
            role,
            expected_proposition,
        } = &projection.proof
        else {
            return Err(litex_to_lean_error(
                &projection.proposition.line_file(),
                "existential projection has no elimination evidence",
            ));
        };
        if source_proposition.to_string() != ir.source.proposition.to_string() {
            return Err(litex_to_lean_error(
                &projection.proposition.line_file(),
                "existential projection cites a different source proposition",
            ));
        }
        if expected_proposition.to_string() != projection.proposition.to_string() {
            return Err(litex_to_lean_error(
                &projection.proposition.line_file(),
                "existential projection disagrees with its retained expected proposition",
            ));
        }
        if index < ir.witnesses.len() {
            let expected_role = LitexToLeanExistentialProjectionRoleIr::ParameterType {
                witness_index: index,
            };
            if *role != expected_role {
                return Err(litex_to_lean_error(
                    &projection.proposition.line_file(),
                    "existential type projections are not in witness order",
                ));
            }
            validate_existential_type_projection(&ir.witnesses[index], &projection.proposition)?;
        } else {
            let body_index = index - ir.witnesses.len();
            let expected_role = LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index };
            if *role != expected_role {
                return Err(litex_to_lean_error(
                    &projection.proposition.line_file(),
                    "existential body projections are not in source-body order",
                ));
            }
        }
        lean_fact(&projection.proposition)?;
    }

    let mut tail = EXIST_SOURCE_PLACEHOLDER.to_string();
    let mut witness_terms = Vec::with_capacity(ir.witnesses.len());
    let mut type_terms = Vec::with_capacity(ir.witnesses.len());
    for param_type in param_types.iter() {
        witness_terms.push(format!("Exists.choose ({})", tail));
        let spec = format!("Exists.choose_spec ({})", tail);
        if matches!(param_type, ParamType::Set(_)) {
            type_terms.push("(by change True; trivial)".to_string());
            tail = spec;
        } else {
            type_terms.push(format!("({}).1", spec));
            tail = format!("({}).2", spec);
        }
    }
    let mut proof_terms = type_terms;
    for body_index in 0..body.facts.len() {
        proof_terms.push(lean_and_projection(&tail, body_index, body.facts.len()));
    }
    Ok(ExistentialEliminationLayout {
        witness_terms,
        proof_terms,
    })
}

fn validate_existential_alpha_rename(source: &Fact, target: &Fact) -> Result<(), RuntimeError> {
    let (
        Fact::ExistFact(ExistFactEnum::ExistFact(source_body)),
        Fact::ExistFact(ExistFactEnum::ExistFact(target_body)),
    ) = (source, target)
    else {
        return Err(litex_to_lean_error(
            &target.line_file(),
            "existential alpha-renaming evidence requires two positive `exist` facts",
        ));
    };
    let source_types = flattened_exist_param_types(source_body);
    let target_types = flattened_exist_param_types(target_body);
    let same_type_families = source_types.len() == target_types.len()
        && source_types
            .iter()
            .zip(target_types.iter())
            .all(|(source_type, target_type)| {
                matches!(
                    (source_type, target_type),
                    (ParamType::Set(_), ParamType::Set(_))
                        | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
                        | (ParamType::FiniteSet(_), ParamType::FiniteSet(_))
                        | (ParamType::Obj(_), ParamType::Obj(_))
                )
            });
    let same_body_families = source_body.facts.len() == target_body.facts.len()
        && source_body.facts.iter().zip(target_body.facts.iter()).all(
            |(source_fact, target_fact)| {
                matches!(
                    (source_fact, target_fact),
                    (ExistBodyFact::AtomicFact(_), ExistBodyFact::AtomicFact(_))
                        | (ExistBodyFact::AndFact(_), ExistBodyFact::AndFact(_))
                        | (ExistBodyFact::ChainFact(_), ExistBodyFact::ChainFact(_))
                        | (ExistBodyFact::OrFact(_), ExistBodyFact::OrFact(_))
                        | (
                            ExistBodyFact::InlineForall(_),
                            ExistBodyFact::InlineForall(_)
                        )
                )
            },
        );
    if !same_type_families || !same_body_families {
        return Err(litex_to_lean_error(
            &target.line_file(),
            "existential alpha-renaming evidence changes binder or body shape",
        ));
    }
    let canonicalizer = Runtime::new();
    let source_exist = ExistFactEnum::ExistFact(source_body.clone());
    let target_exist = ExistFactEnum::ExistFact(target_body.clone());
    if !source_exist.can_be_used_to_verify_goal(&target_exist)
        || Runtime::exist_fact_normalized_body_string(&canonicalizer, &source_exist)?
            != Runtime::exist_fact_normalized_body_string(&canonicalizer, &target_exist)?
    {
        return Err(litex_to_lean_error(
            &target.line_file(),
            "existential alpha-renaming evidence changes the canonical proposition",
        ));
    }
    lean_fact(source)?;
    lean_fact(target)?;
    Ok(())
}

fn flattened_exist_param_types(body: &ExistFactBody) -> Vec<ParamType> {
    body.params_def_with_type
        .groups
        .iter()
        .flat_map(|group| {
            group
                .params
                .iter()
                .map(|_| group.param_type.clone())
                .collect::<Vec<_>>()
        })
        .collect()
}

fn lean_and_projection(root: &str, index: usize, count: usize) -> String {
    if count <= 1 {
        return root.to_string();
    }
    let mut projection = format!("({})", root);
    for _ in 0..index {
        projection.push_str(".2");
    }
    if index + 1 < count {
        projection.push_str(".1");
    }
    projection
}

fn validate_existential_type_projection(
    witness: &LitexToLeanExistentialWitnessIr,
    proposition: &Fact,
) -> Result<(), RuntimeError> {
    let selected_matches = |obj: &Obj| {
        matches!(
            LitexToLeanObjectIr::lower(obj),
            Ok(LitexToLeanObjectIr::Symbol { symbol_id, .. }) if symbol_id == witness.symbol_id
        )
    };
    let valid = match (&witness.param_type, proposition) {
        (LitexToLeanParameterTypeIr::Set { .. }, Fact::AtomicFact(AtomicFact::IsSetFact(fact))) => {
            selected_matches(&fact.set)
        }
        (
            LitexToLeanParameterTypeIr::NonemptySet { .. },
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)),
        ) => selected_matches(&fact.set),
        (
            LitexToLeanParameterTypeIr::FiniteSet { .. },
            Fact::AtomicFact(AtomicFact::IsFiniteSetFact(fact)),
        ) => selected_matches(&fact.set),
        (
            LitexToLeanParameterTypeIr::MemberOf { set: carrier, .. },
            Fact::AtomicFact(AtomicFact::InFact(fact)),
        ) => {
            selected_matches(&fact.element)
                && LitexToLeanObjectIr::lower(&fact.set)
                    .is_ok_and(|actual| actual == carrier.clone())
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(litex_to_lean_error(
            &proposition.line_file(),
            "existential type projection does not match its selected witness and instantiated type",
        ))
    }
}

fn validate_exist_introduction_requirement(
    witness: &Obj,
    param_type: &ParamType,
    proposition: &Fact,
) -> Result<(), RuntimeError> {
    let witness_ir = LitexToLeanObjectIr::lower(witness)
        .map_err(|message| litex_to_lean_error(&proposition.line_file(), message))?;
    let object_matches =
        |obj: &Obj| LitexToLeanObjectIr::lower(obj).is_ok_and(|candidate| candidate == witness_ir);
    let valid = match (param_type, proposition) {
        (ParamType::Obj(_), Fact::AtomicFact(AtomicFact::InFact(fact))) => {
            object_matches(&fact.element)
        }
        (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact))) => {
            object_matches(&fact.set)
        }
        (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(fact))) => {
            object_matches(&fact.set)
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(litex_to_lean_error(
            &proposition.line_file(),
            "existential-introduction parameter proof has the wrong fact family or witness",
        ))
    }
}

fn validate_projected_forall_ir(ir: &LitexToLeanProjectedForallIr) -> Result<(), RuntimeError> {
    let Fact::ForallFact(source) = &ir.source else {
        return Err(litex_to_lean_error(
            &ir.source.line_file(),
            "projected-forall IR source is not a forall fact",
        ));
    };
    if ir.facts.is_empty() {
        return Err(litex_to_lean_error(
            &source.line_file,
            "projected-forall IR contains no stored projection",
        ));
    }

    let source_binding_ids = source
        .params_def_with_type
        .collect_param_bindings()
        .into_iter()
        .map(|binding| binding.id())
        .collect::<HashSet<_>>();
    let source_conclusions = source
        .then_facts
        .iter()
        .map(|fact| fact.clone().to_fact().to_string())
        .collect::<HashSet<_>>();
    let source_premises = source
        .dom_facts
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let mut fact_ids = HashSet::new();
    for fact in ir.facts.iter() {
        let fact_id = required_fact_id(fact)?;
        if !fact_ids.insert(fact_id) {
            return Err(litex_to_lean_error(
                &fact.proposition.line_file(),
                "projected-forall IR repeats a stored FactId",
            ));
        }
        let Fact::ForallFact(projected) = &fact.proposition else {
            return Err(litex_to_lean_error(
                &fact.proposition.line_file(),
                "projected-forall IR contains a non-forall stored fact",
            ));
        };
        let has_foreign_binding = projected
            .params_def_with_type
            .collect_param_bindings()
            .iter()
            .any(|binding| !source_binding_ids.contains(&binding.id()));
        let has_foreign_conclusion = projected.then_facts.iter().any(|conclusion| {
            !source_conclusions.contains(&conclusion.clone().to_fact().to_string())
        });
        let premises_changed = projected
            .dom_facts
            .iter()
            .map(ToString::to_string)
            .ne(source_premises.iter().cloned());
        if has_foreign_binding || has_foreign_conclusion || premises_changed {
            return Err(litex_to_lean_error(
                &projected.line_file,
                "projected-forall IR is not a binder-and-conclusion subset of its source",
            ));
        }
        if !matches!(
            fact.proof,
            LitexToLeanFactProofIr::ForallIntroduction { .. }
        ) {
            return Err(litex_to_lean_error(
                &projected.line_file,
                "a stored forall projection has no forall-introduction proof",
            ));
        }
    }
    Ok(())
}

fn validate_named_theorem_ir(ir: &LitexToLeanNamedTheoremIr) -> Result<(), RuntimeError> {
    let Fact::ForallFact(source) = &ir.theorem.proposition else {
        return Err(litex_to_lean_error(
            &ir.theorem.proposition.line_file(),
            "named-theorem IR proposition is not a forall fact",
        ));
    };
    if ir.name.trim().is_empty() {
        return Err(litex_to_lean_error(
            &source.line_file,
            "named-theorem IR has an empty source name",
        ));
    }
    if !matches!(
        ir.theorem.proof,
        LitexToLeanFactProofIr::ForallIntroduction { .. }
    ) {
        return Err(litex_to_lean_error(
            &source.line_file,
            "named-theorem IR has no forall-introduction proof",
        ));
    }
    if ir.theorem.fact_id.is_none() && ir.stored_projections.is_empty() {
        return Err(litex_to_lean_error(
            &source.line_file,
            "named-theorem IR has neither a primary FactId nor a stored projection",
        ));
    }
    if ir.proof_steps.len() != ir.expected_proof_step_count {
        return Err(litex_to_lean_error(
            &source.line_file,
            "named-theorem IR is missing retained proof steps",
        ));
    }
    for (index, step) in ir.proof_steps.iter().enumerate() {
        if step.position != index + 1 {
            return Err(litex_to_lean_error(
                &statement_ir_line_file(&step.statement),
                "named-theorem proof steps are out of verifier order",
            ));
        }
    }
    if !ir.stored_projections.is_empty() {
        validate_projected_forall_ir(&LitexToLeanProjectedForallIr {
            source: ir.theorem.proposition.clone(),
            facts: ir.stored_projections.clone(),
            inferred_facts: Vec::new(),
            well_definedness: ir.well_definedness.clone(),
        })?;
    }
    let mut fact_ids = HashSet::new();
    if let Some(fact_id) = ir.theorem.fact_id {
        fact_ids.insert(fact_id);
    }
    for fact in ir.stored_projections.iter().chain(ir.inferred_facts.iter()) {
        let fact_id = required_fact_id(fact)?;
        if !fact_ids.insert(fact_id) {
            return Err(litex_to_lean_error(
                &fact.proposition.line_file(),
                "named-theorem IR repeats a stored FactId",
            ));
        }
    }
    Ok(())
}

fn required_fact_id(fact: &LitexToLeanFactIr) -> Result<FactId, RuntimeError> {
    fact.fact_id.ok_or_else(|| {
        litex_to_lean_error(
            &fact.proposition.line_file(),
            "a top-level stored fact reached Litex-to-Lean without a FactId",
        )
    })
}

fn lean_stored_fact_name(fact_id: FactId) -> String {
    format!("fact{}", fact_id.value())
}

fn lean_choice_source_name(symbol_id: SymbolId) -> String {
    format!("litex_choice_source_{}", symbol_id.value())
}

fn lean_exist_source_name(symbol_id: SymbolId) -> String {
    format!("litex_exist_source_{}", symbol_id.value())
}

fn lean_proof_fact_name(local_space_id: usize, proof_fact_index: usize) -> String {
    format!("proof_fact_{}_{}", local_space_id, proof_fact_index)
}

fn lean_proof_arg_name(local_space_id: usize, local_index: usize) -> String {
    format!("proof_arg_{}_{}", local_space_id, local_index)
}

fn is_nonzero_fact(fact: &Fact) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::NotEqualFact(_)))
}

fn is_universal_native_membership_fact(fact: &Fact) -> bool {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = fact else {
        return false;
    };
    matches!(
        membership.set,
        Obj::FnSet(_)
            | Obj::StandardSet(
                StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C
            )
    )
}

fn register_local_fact(fact_id: FactId, fact: &Fact, name: &str, context: &mut LeanProofContext) {
    context.proof_fact_names.insert(fact_id, name.to_string());
    if is_nonzero_fact(fact) && !context.nonzero_names.iter().any(|known| known == name) {
        context.nonzero_names.push(name.to_string());
    }
}

fn push_lean_bullet(lines: &mut Vec<String>, body: &[String]) -> Result<(), RuntimeError> {
    let Some((first, rest)) = body.split_first() else {
        return Err(litex_to_lean_error(
            &default_line_file(),
            "case-split branch emitted an empty Lean proof",
        ));
    };
    lines.push(format!(
        "  · {}",
        first.strip_prefix("  ").unwrap_or(first.as_str())
    ));
    for line in rest {
        lines.push(format!(
            "    {}",
            line.strip_prefix("  ").unwrap_or(line.as_str())
        ));
    }
    Ok(())
}

fn parenthesized_join(items: Vec<String>, separator: &str) -> String {
    if items.len() == 1 {
        return items
            .into_iter()
            .next()
            .unwrap_or_else(|| "True".to_string());
    }
    format!("({})", items.join(separator))
}

fn parenthesize_if_many(body: &str, count: usize) -> String {
    if count > 1 {
        format!("({})", body)
    } else {
        body.to_string()
    }
}

fn lean_namespace_for_runtime(runtime: &Runtime) -> Option<String> {
    runtime
        .current_parse_namespace()
        .and_then(lean_namespace)
        .or_else(|| {
            let source_path = runtime.current_file_path_rc();
            lean_namespace_from_lit_path(source_path.as_ref())
        })
}

fn lean_namespace_from_lit_path(source_path: &str) -> Option<String> {
    let path = Path::new(source_path);
    path.extension()
        .and_then(|extension| extension.to_str())
        .filter(|extension| *extension == "lit")
        .and_then(|_| path.file_stem())
        .and_then(|stem| stem.to_str())
        .map(lean_namespace_segment)
}

fn lean_namespace(name: &str) -> Option<String> {
    let segments = name
        .split(MOD_SIGN)
        .filter(|segment| !segment.is_empty())
        .map(lean_namespace_segment)
        .collect::<Vec<_>>();
    (!segments.is_empty()).then(|| segments.join("."))
}

fn lean_namespace_segment(segment: &str) -> String {
    let mut name = lean_name(segment);
    if name.chars().all(|character| character == '_') {
        name.insert_str(0, "litex");
    }
    name
}

fn litex_to_lean_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}

fn statement_ir_display(statement: &LitexToLeanStatementIr) -> String {
    match statement {
        LitexToLeanStatementIr::AbstractProp(ir) => format!("abstract_prop {}", ir.name),
        LitexToLeanStatementIr::Prop(ir) => format!("prop {}", ir.name),
        LitexToLeanStatementIr::HaveObjChoice(ir) => format!(
            "have {} <by checked choice>",
            ir.choices
                .iter()
                .map(|choice| choice.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        LitexToLeanStatementIr::HaveObjEqual(ir) => format!(
            "have {} = <value>",
            ir.definitions
                .iter()
                .map(|definition| definition.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        LitexToLeanStatementIr::HaveFnEqual(ir) => {
            format!("have fn {} = {}", ir.name, ir.source_body)
        }
        LitexToLeanStatementIr::HaveExistentialWitness(ir) => format!(
            "obtain {} from {}",
            ir.witnesses
                .iter()
                .map(|witness| witness.name.as_str())
                .collect::<Vec<_>>()
                .join(", "),
            ir.source.proposition
        ),
        LitexToLeanStatementIr::Proof(ir) => match ir.facts.first() {
            Some(fact) if ir.facts.len() == 1 => fact.proposition.to_string(),
            Some(_) => format!("proof <{} facts>", ir.facts.len()),
            None => "proof <empty>".to_string(),
        },
        LitexToLeanStatementIr::Trust(ir) => match ir.facts.first() {
            Some(fact) if ir.facts.len() == 1 => format!("trust {}", fact.proposition),
            Some(_) => format!("trust <{} facts>", ir.facts.len()),
            None => "trust <empty>".to_string(),
        },
        LitexToLeanStatementIr::Fact(ir) => ir.fact.proposition.to_string(),
        LitexToLeanStatementIr::NamedTheorem(ir) => {
            format!("thm {}: ? {}", ir.name, ir.theorem.proposition)
        }
        LitexToLeanStatementIr::ProjectedForall(ir) => ir.source.to_string(),
    }
}

fn statement_ir_line_file(statement: &LitexToLeanStatementIr) -> LineFile {
    match statement {
        LitexToLeanStatementIr::AbstractProp(_) => default_line_file(),
        LitexToLeanStatementIr::Prop(ir) => ir
            .iff_facts
            .first()
            .map(Fact::line_file)
            .unwrap_or_else(default_line_file),
        LitexToLeanStatementIr::HaveObjChoice(ir) => ir
            .choices
            .first()
            .map(|choice| choice.membership.proposition.line_file())
            .unwrap_or_else(default_line_file),
        LitexToLeanStatementIr::HaveObjEqual(ir) => ir
            .facts
            .first()
            .map(|fact| fact.proposition.line_file())
            .unwrap_or_else(default_line_file),
        LitexToLeanStatementIr::HaveFnEqual(ir) => ir.return_check.proposition.line_file(),
        LitexToLeanStatementIr::HaveExistentialWitness(ir) => ir.source.proposition.line_file(),
        LitexToLeanStatementIr::Proof(ir) => ir
            .facts
            .first()
            .map(|fact| fact.proposition.line_file())
            .unwrap_or_else(default_line_file),
        LitexToLeanStatementIr::Trust(ir) => ir
            .facts
            .first()
            .map(|fact| fact.proposition.line_file())
            .unwrap_or_else(default_line_file),
        LitexToLeanStatementIr::Fact(ir) => ir.fact.proposition.line_file(),
        LitexToLeanStatementIr::NamedTheorem(ir) => ir.theorem.proposition.line_file(),
        LitexToLeanStatementIr::ProjectedForall(ir) => ir.source.line_file(),
    }
}

fn lean_comment_text(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn closed_rational_equality_with_target_expectation(
    fact: &Fact,
    type_context: &LeanTypeContext,
) -> bool {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = fact else {
        return false;
    };
    closed_rational_expression(&equality.left)
        && closed_rational_expression(&equality.right)
        && (type_context.expected_object(&equality.left).is_some()
            || type_context.expected_object(&equality.right).is_some())
}

fn closed_rational_expression(obj: &Obj) -> bool {
    match obj {
        Obj::Number(_) => true,
        Obj::Add(add) => {
            closed_rational_expression(&add.left) && closed_rational_expression(&add.right)
        }
        Obj::Sub(sub) => {
            closed_rational_expression(&sub.left) && closed_rational_expression(&sub.right)
        }
        Obj::Mul(mul) => {
            closed_rational_expression(&mul.left) && closed_rational_expression(&mul.right)
        }
        Obj::Div(div) => {
            closed_rational_expression(&div.left) && closed_rational_expression(&div.right)
        }
        Obj::Pow(pow) => {
            closed_rational_expression(&pow.base) && matches!(pow.exponent.as_ref(), Obj::Number(_))
        }
        _ => false,
    }
}

fn requires_checked_closed_numeric_carrier(obj: &Obj) -> bool {
    match obj {
        Obj::Sub(_) | Obj::Div(_) => true,
        Obj::Add(add) => {
            requires_checked_closed_numeric_carrier(&add.left)
                || requires_checked_closed_numeric_carrier(&add.right)
        }
        Obj::Mul(mul) => {
            requires_checked_closed_numeric_carrier(&mul.left)
                || requires_checked_closed_numeric_carrier(&mul.right)
        }
        Obj::Pow(pow) => {
            requires_checked_closed_numeric_carrier(&pow.base)
                || requires_checked_closed_numeric_carrier(&pow.exponent)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn lean_decimal_literal_validation_accepts_signed_canonical_decimals_only() {
        for accepted in ["0", "1", "-1", "0.5", "-12.25"] {
            assert!(is_safe_lean_decimal_literal(accepted), "{accepted}");
        }
        for rejected in ["", "-", ".", ".5", "1.", "1.2.3", "+1", "1e3"] {
            assert!(!is_safe_lean_decimal_literal(rejected), "{rejected}");
        }
    }

    #[test]
    fn ordinary_runtime_does_not_return_litex_to_lean_ir() {
        run_with_large_stack("ordinary_runtime_does_not_return_litex_to_lean_ir", || {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("ordinary-runtime-ir-boundary");
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(
                    "1 + 1 = 2\n\n1 + 1 = 2\n\n2 + 2 = 4",
                    runtime.current_file_path_rc(),
                )
                .unwrap();
            let mut results = Vec::new();
            for mut block in blocks {
                let stmt = runtime.parse_stmt(&mut block).unwrap();
                results.push(run_stmt_at_global_env(&stmt, &mut runtime).unwrap());
            }

            let first_id = results[0].fact_id().expect("stored fact should have an ID");
            assert_eq!(results[1].fact_id(), Some(first_id));
            let VerifiedByResult::Fact(citation) =
                &results[1].factual_success().unwrap().verified_by
            else {
                panic!("repeated fact should cite the stored fact");
            };
            assert_eq!(citation.source_fact_id, Some(first_id));
            assert!(results[2].fact_id().expect("new fact should have an ID") > first_id);
            assert!(results
                .iter()
                .all(|result| result.litex_to_lean_ir().is_none()));
            assert!(!runtime.litex_to_lean_ir_mode());
        });
    }

    #[test]
    fn restricted_function_application_replays_captured_well_definedness() {
        run_with_large_stack(
            "restricted_function_application_replays_captured_well_definedness",
            || {
                let lean = compile_to_lean_from_source(
                    "forall f fn(x R: x > 0) R:\n    f(2) = f(2)",
                    "restricted-function-wd.lit",
                )
                .expect("restricted function application should compile");
                assert!(lean.contains("Set ((x : ℝ) → x > 0 → ℝ)"));
                assert!(lean.contains("Litex well-definedness certificate"));
                assert!(lean.contains("f 2 well_defined_fact_"), "{lean}");
                assert!(!lean.contains("by assumption"), "{lean}");
                assert!(!lean.contains("sorry"), "{lean}");
            },
        );
    }

    #[test]
    fn stable_wd_fact_id_emits_one_lean_helper_across_statements() {
        run_with_large_stack(
            "stable_wd_fact_id_emits_one_lean_helper_across_statements",
            || {
                let source = "have fn f(x R: x > 0) R = x\n\nf(2) = f(2)\n\nf(2) = 2";
                let ir = test_litex_to_lean_ir(source, "stable-wd-helper.lit");
                assert_eq!(ir.len(), 3);

                let application_proof_id = |statement: &LitexToLeanStatementIr| {
                    let LitexToLeanStatementIr::Fact(statement) = statement else {
                        panic!("expected a fact after the named function definition")
                    };
                    statement
                        .well_definedness
                        .objects
                        .iter()
                        .find(|evidence| evidence.source_object.to_string().ends_with("f(2)"))
                        .expect("the statement should retain the application proof")
                        .well_defined_obj_proof_id
                };
                assert_eq!(
                    application_proof_id(&ir[1]),
                    application_proof_id(&ir[2]),
                    "a later statement should cite the environment's exact application proof"
                );

                let domain_fact_id = |statement: &LitexToLeanStatementIr| {
                    let LitexToLeanStatementIr::Fact(statement) = statement else {
                        unreachable!()
                    };
                    statement
                        .well_definedness
                        .facts
                        .iter()
                        .find(|evidence| evidence.fact.proposition.to_string() == "2 > 0")
                        .expect("the application should retain its checked domain fact")
                        .well_defined_fact_id
                };
                let first_fact_id = domain_fact_id(&ir[1]);
                assert_eq!(first_fact_id, domain_fact_id(&ir[2]));

                let lean = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect("the stable environment proof identity should lower to Lean");
                let helper_name = format!("well_defined_fact_{}", first_fact_id.value());
                assert_eq!(
                    lean.matches(&format!("theorem {helper_name} :")).count(),
                    1,
                    "one stable WD fact must produce at most one global Lean helper\n{lean}"
                );
                assert!(
                    lean.matches(&format!("f 2 {helper_name}")).count() >= 3,
                    "both repeated propositions should cite the same helper\n{lean}"
                );
            },
        );
    }

    #[test]
    fn generalized_wd_helpers_are_indexed_by_stable_fact_id() {
        run_with_large_stack(
            "generalized_wd_helpers_are_indexed_by_stable_fact_id",
            || {
                let source = "forall f fn(x R: x > 0) R:\n    f(2) = f(2)";
                let ir = test_litex_to_lean_ir(source, "exact-generalized-wd-id.lit");
                let LitexToLeanStatementIr::Fact(statement) = &ir[0] else {
                    panic!("expected one forall fact")
                };
                let stable_ids_by_certificate = statement
                    .well_definedness
                    .facts
                    .iter()
                    .map(|evidence| {
                        (
                            evidence.certificate_id.value(),
                            evidence.well_defined_fact_id.value(),
                        )
                    })
                    .collect::<HashMap<_, _>>();
                let lean = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect("generalized WD facts should lower with exact identities");

                let mut checked = 0;
                for line in lean.lines().filter(|line| {
                    line.contains("replayed by generalized helper well_defined_fact_")
                }) {
                    let words = line.split_whitespace().collect::<Vec<_>>();
                    let certificate_id = words[4]
                        .parse::<u64>()
                        .expect("certificate comment should contain a numeric local ID");
                    let helper_id = words[9]
                        .strip_prefix("well_defined_fact_")
                        .and_then(|value| value.parse::<u64>().ok())
                        .expect("generalized helper should carry its stable WD fact ID");
                    assert_eq!(
                        stable_ids_by_certificate.get(&certificate_id),
                        Some(&helper_id),
                        "a proposition-equal WD fact was linked to another stable helper: {line}"
                    );
                    checked += 1;
                }
                assert!(
                    checked > 1,
                    "the tracer should exercise repeated generalized facts"
                );
            },
        );
    }

    #[test]
    fn restricted_function_application_uses_the_exact_named_local_premise() {
        run_with_large_stack(
            "restricted_function_application_uses_the_exact_named_local_premise",
            || {
                let lean = compile_to_lean_from_source(
                    "forall f fn(x R: x > 0) R, a R:\n    a > 0\n    =>:\n        f(a) = f(a)",
                    "restricted-function-local-wd.lit",
                )
                .expect("local domain proof should remain in the theorem scope");
                assert!(lean.contains("(litex_domain_fact_1 : a > 0)"), "{lean}");
                assert!(lean.contains("f a litex_domain_fact_1"), "{lean}");
                assert!(!lean.contains("by assumption"), "{lean}");
            },
        );
    }

    #[test]
    fn source_only_division_well_definedness_is_replayed_without_a_term_argument() {
        run_with_large_stack(
            "source_only_division_well_definedness_is_replayed_without_a_term_argument",
            || {
                let lean = compile_to_lean_from_source(
                    "forall a R:\n    a / 2 = a / 2",
                    "source-only-division-wd.lit",
                )
                .expect("division source-only WD evidence should compile");
                assert!(
                    lean.contains("Litex well-definedness certificate"),
                    "{lean}"
                );
                assert!(lean.contains("well_defined_fact_"), "{lean}");
                assert!(lean.contains("a / 2"), "{lean}");
                assert!(!lean.contains("by assumption"), "{lean}");
            },
        );
    }

    #[test]
    fn comparison_notation_duality_retains_its_exact_local_source() {
        run_with_large_stack(
            "comparison_notation_duality_retains_its_exact_local_source",
            || {
                let source = "forall b R+:\n    b > 0";
                let mut ir = test_litex_to_lean_ir(source, "comparison-notation-duality.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                    panic!("expected one forall fact")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut statement.fact.proof
                else {
                    panic!("expected forall-introduction evidence")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::ComparisonNotationDuality {
                            expected_source,
                            expected_target,
                        },
                    premises,
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("comparison spelling should retain an explicit duality rule")
                };
                assert!(expected_source.to_string().starts_with("0 < "));
                assert!(expected_target.to_string().ends_with("> 0"));
                assert_eq!(premises.len(), 1);
                let lean = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect("the exact local comparison source should be reusable");
                assert!(lean.contains("(0 : ℝ) < b"), "{lean}");

                let mut malformed = test_litex_to_lean_ir(source, "bad-comparison-duality.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut malformed[0] else {
                    panic!("expected one forall fact")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut statement.fact.proof
                else {
                    panic!("expected forall-introduction evidence")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::ComparisonNotationDuality {
                            expected_source,
                            expected_target,
                        },
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("comparison spelling should retain an explicit duality rule")
                };
                *expected_target = expected_source.clone();
                let error = emit_lean_from_litex_to_lean_ir(&malformed)
                    .expect_err("retargeted comparison duality must stop emission")
                    .trace_message();
                assert!(
                    error.contains("does not match its retained source and target"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn strict_order_not_equality_replays_exact_ordered_premises() {
        run_with_large_stack(
            "strict_order_not_equality_replays_exact_ordered_premises",
            || {
                let source = "forall b R+:\n    b != 0";
                let mut ir = test_litex_to_lean_ir(source, "strict-order-not-equality.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                    panic!("expected one forall fact")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut statement.fact.proof
                else {
                    panic!("expected forall-introduction evidence")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::Builtin(
                            LitexToLeanBuiltinRuleIr::NotEqualFromStrictOrder,
                        ),
                    premises,
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("strict positivity should retain the checked order-to-ne rule")
                };
                assert_eq!(premises.len(), 3);
                assert!(matches!(
                    premises[0].proposition,
                    Fact::AtomicFact(AtomicFact::InFact(_))
                ));
                assert!(matches!(
                    premises[1].proposition,
                    Fact::AtomicFact(AtomicFact::InFact(_))
                ));
                assert!(matches!(
                    premises[2].proposition,
                    Fact::AtomicFact(AtomicFact::LessFact(_) | AtomicFact::GreaterFact(_))
                ));
                let lean = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect("the retained strict-order proof should compile");
                assert!(lean.contains("lt_irrefl"), "{lean}");

                let mut malformed = test_litex_to_lean_ir(source, "bad-strict-order-ne.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut malformed[0] else {
                    panic!("expected one forall fact")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut statement.fact.proof
                else {
                    panic!("expected forall-introduction evidence")
                };
                let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("expected one rule application")
                };
                premises.pop();
                let error = emit_lean_from_litex_to_lean_ir(&malformed)
                    .expect_err("a missing ordered premise must stop emission")
                    .trace_message();
                assert!(error.contains("expected 3 premises"), "{error}");
            },
        );
    }

    #[test]
    fn function_application_preserves_flat_and_nested_litex_layers() {
        run_with_large_stack(
            "function_application_preserves_flat_and_nested_litex_layers",
            || {
                let flat = compile_to_lean_from_source(
                    "forall f fn(x, y, z R) R:\n    f(1, 2, 3) = f(1, 2, 3)",
                    "flat-function-layer.lit",
                )
                .expect("flat source layer should compile");
                assert!(flat.contains("Set ((x : ℝ) → (y : ℝ) → (z : ℝ) → ℝ)"));
                assert!(flat.contains("f 1 2 3"), "{flat}");

                let nested = compile_to_lean_from_source(
                    "forall f fn(x R: x > 0) fn(y R) R:\n    f(2)(3) = f(2)(3)",
                    "nested-function-layer.lit",
                )
                .expect("nested source layers should compile");
                assert!(nested.contains("Set ((x : ℝ) → x > 0 → (y : ℝ) → ℝ)"));
                assert!(
                    nested.contains("f 2 well_defined_fact_")
                        && nested.contains("well_defined_fact_")
                        && nested.contains(" 3"),
                    "{nested}"
                );
            },
        );
    }

    #[test]
    fn refined_function_return_sets_keep_output_membership_contracts() {
        run_with_large_stack(
            "refined_function_return_sets_keep_output_membership_contracts",
            || {
                let flat = compile_to_lean_from_source(
                    "forall f fn(x R) R+:\n    f(1) = f(1)",
                    "refined-function-return.lit",
                )
                .expect("a refined return must lower to a raw function plus pointwise membership");
                assert!(
                    flat.contains("litex_function_value x")
                        && flat.contains("Litex.StandardSets.RPos"),
                    "{flat}"
                );
                assert!(!flat.contains("sorry"), "{flat}");

                let nested = compile_to_lean_from_source(
                    "forall f fn(x R) fn(y R) R+:\n    f(1)(2) = f(1)(2)",
                    "nested-refined-function-return.lit",
                )
                .expect("a nested refined return must preserve both source application layers");
                assert!(
                    nested.contains("litex_function_value x")
                        && nested.contains("Litex.StandardSets.RPos"),
                    "{nested}"
                );
                assert!(!nested.contains("sorry"), "{nested}");
            },
        );
    }

    #[test]
    fn lean_currying_does_not_accept_a_new_litex_application_layer() {
        run_with_large_stack(
            "lean_currying_does_not_accept_a_new_litex_application_layer",
            || {
                let error = compile_to_lean_from_source(
                    "forall f fn(x, y, z R) R:\n    f(1)(2, 3) = f(1)(2, 3)",
                    "invalid-function-layer.lit",
                )
                .expect_err("Litex must reject the extra application layer before lowering");
                let message = error.trace_message();
                assert!(
                    message.contains("number of args")
                        || message.contains("return set")
                        || message.contains("not well-defined"),
                    "{message}"
                );
            },
        );
    }

    #[test]
    fn one_function_symbol_is_not_retyped_at_an_unrelated_signature() {
        run_with_large_stack(
            "one_function_symbol_is_not_retyped_at_an_unrelated_signature",
            || {
                let error = compile_to_lean_from_source(
                    "forall f fn(x R) R:\n    f $in fn(x Q) Q",
                    "conflicting-function-signatures.lit",
                )
                .expect_err("one source symbol must keep its declared function carrier");
                let message = error.trace_message();
                assert!(
                    message.contains("verification failed")
                        || message.contains("unverified")
                        || message.contains("unknown"),
                    "{message}"
                );
            },
        );
    }

    #[test]
    fn malformed_function_well_definedness_certificates_fail_closed() {
        run_with_large_stack(
            "malformed_function_well_definedness_certificates_fail_closed",
            || {
                let source = "forall f fn(x R: x > 0) R:\n    f(2) = f(2)";

                let mut missing = test_litex_to_lean_ir(source, "missing-function-wd.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut missing[0] else {
                    panic!("expected one fact statement")
                };
                statement
                    .well_definedness
                    .facts
                    .retain(|evidence| evidence.fact.proposition.to_string() != "2 > 0");
                let missing_error = emit_lean_from_litex_to_lean_ir(&missing)
                    .unwrap_err()
                    .trace_message();
                assert!(
                    missing_error.contains("missing or out of verifier order")
                        || missing_error.contains("missing the retained domain proof")
                        || missing_error.contains("duplicated, missing, or out of verifier order")
                        || missing_error
                            .contains("object occurrence references a missing fact certificate"),
                    "{missing_error}"
                );

                let mut reordered = test_litex_to_lean_ir(source, "reordered-function-wd.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut reordered[0] else {
                    panic!("expected one fact statement")
                };
                assert!(statement.well_definedness.facts.len() > 1);
                statement.well_definedness.facts.swap(0, 1);
                let reordered_error = emit_lean_from_litex_to_lean_ir(&reordered)
                    .unwrap_err()
                    .trace_message();
                assert!(
                    reordered_error.contains("out of verifier order"),
                    "{reordered_error}"
                );

                let mut mismatched = test_litex_to_lean_ir(source, "mismatched-function-wd.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut mismatched[0] else {
                    panic!("expected one fact statement")
                };
                let evidence = statement
                    .well_definedness
                    .facts
                    .iter_mut()
                    .find(|evidence| evidence.fact.proposition.to_string() == "2 > 0")
                    .expect("domain proof should be present");
                evidence.expected_proposition = InFact::new(
                    Number::new("2".to_string()).into(),
                    StandardSet::R.into(),
                    default_line_file(),
                )
                .into();
                let mismatch_error = emit_lean_from_litex_to_lean_ir(&mismatched)
                    .unwrap_err()
                    .trace_message();
                assert!(
                    mismatch_error.contains("does not match its frozen verifier target")
                        || mismatch_error.contains(
                            "target well-definedness requirement changed its frozen proposition"
                        ),
                    "{mismatch_error}"
                );

                let mut missing_reference =
                    test_litex_to_lean_ir(source, "missing-function-wd-reference.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut missing_reference[0] else {
                    panic!("expected one fact statement")
                };
                statement.well_definedness.target_requirements.clear();
                let missing_reference_error = emit_lean_from_litex_to_lean_ir(&missing_reference)
                    .unwrap_err()
                    .trace_message();
                assert!(
                    missing_reference_error
                        .contains("missing an exact retained WD requirement reference"),
                    "{missing_reference_error}"
                );

                let mut missing_root =
                    test_litex_to_lean_ir(source, "missing-environment-wd-root.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut missing_root[0] else {
                    panic!("expected one fact statement")
                };
                statement.well_definedness.root_proof_ids[0] = WellDefinedObjProofId::new(u64::MAX);
                let missing_root_error = emit_lean_from_litex_to_lean_ir(&missing_root)
                    .unwrap_err()
                    .trace_message();
                assert!(
                    missing_root_error.contains("missing root proof"),
                    "{missing_root_error}"
                );

                let mut cyclic = test_litex_to_lean_ir(source, "cyclic-environment-wd.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut cyclic[0] else {
                    panic!("expected one fact statement")
                };
                let root_id = statement.well_definedness.root_proof_ids[0];
                statement
                    .well_definedness
                    .objects
                    .iter_mut()
                    .find(|object| object.well_defined_obj_proof_id == root_id)
                    .expect("the projected root should be present")
                    .child_proof_ids
                    .push(root_id);
                let cyclic_error = emit_lean_from_litex_to_lean_ir(&cyclic)
                    .unwrap_err()
                    .trace_message();
                assert!(cyclic_error.contains("contains a cycle"), "{cyclic_error}");

                let mut disconnected =
                    test_litex_to_lean_ir(source, "disconnected-environment-wd.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut disconnected[0] else {
                    panic!("expected one fact statement")
                };
                let mut orphan = statement.well_definedness.objects[0].clone();
                orphan.occurrence_id = WellDefinednessObjectOccurrenceId::new(u64::MAX - 1);
                orphan.well_defined_obj_proof_id = WellDefinedObjProofId::new(u64::MAX - 1);
                statement.well_definedness.objects.push(orphan);
                let disconnected_error = emit_lean_from_litex_to_lean_ir(&disconnected)
                    .unwrap_err()
                    .trace_message();
                assert!(
                    disconnected_error.contains("unreachable from its statement roots"),
                    "{disconnected_error}"
                );

                let mut inconsistent_projection =
                    test_litex_to_lean_ir(source, "inconsistent-environment-wd-projection.lit");
                let LitexToLeanStatementIr::Fact(statement) = &mut inconsistent_projection[0]
                else {
                    panic!("expected one fact statement")
                };
                let object = statement
                    .well_definedness
                    .objects
                    .iter_mut()
                    .find(|object| !object.fact_ids.is_empty())
                    .expect("at least one projected object should own a fact");
                object.fact_ids.push(object.fact_ids[0]);
                let inconsistent_projection_error =
                    emit_lean_from_litex_to_lean_ir(&inconsistent_projection)
                        .unwrap_err()
                        .trace_message();
                assert!(
                    inconsistent_projection_error.contains(
                        "stable DAG edges disagree with the statement-local fact projection"
                    ),
                    "{inconsistent_projection_error}"
                );
            },
        );
    }

    #[test]
    fn report_mode_collects_the_same_function_well_definedness_certificate() {
        run_with_large_stack(
            "report_mode_collects_the_same_function_well_definedness_certificate",
            || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("function-wd-report.lit");
                let report = compile_to_lean_with_report(
                    "forall f fn(x R: x > 0) R:\n    f(2) = f(2)",
                    &mut runtime,
                )
                .unwrap();
                assert_eq!(report.status, LitexToLeanCompilationStatus::Complete);
                assert!(report.unsupported.is_empty());
                assert!(report.lean_code.contains("well_defined_fact_"));
                assert!(report.lean_code.contains("f 2 well_defined_fact_"));
            },
        );
    }

    #[test]
    fn named_function_definition_replays_scoped_well_definedness() {
        run_with_large_stack(
            "named_function_definition_replays_scoped_well_definedness",
            || {
                let source = "have fn reciprocal(x R: x != 0) R = 1 / x\n\nforall x R:\n    x != 0\n    =>:\n        reciprocal(x) = 1 / x";
                let ir = test_litex_to_lean_ir(source, "named-function-definition-wd.lit");
                let LitexToLeanStatementIr::Fact(evaluation) = &ir[1] else {
                    panic!("the second statement should retain the evaluation theorem")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &evaluation.fact.proof
                else {
                    panic!("the evaluation theorem should retain forall-introduction evidence")
                };
                assert!(matches!(
                    underlying_test_proof(&conclusions[0].proof),
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::CheckedFunctionDefinitionReplay { .. },
                        parameter_requirements,
                        premises,
                    } if parameter_requirements.is_empty() && premises.is_empty()
                ));
                let lean = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect("checked named function should lower to one native Lean definition");
                assert!(
                    lean.contains("def reciprocal : (x : ℝ) → x ≠ 0 → ℝ"),
                    "{lean}"
                );
                assert!(lean.contains("fun (x : ℝ) (litex_domain_fact_1 : x ≠ 0)"));
                assert!(lean.contains("litex_function_return_check_"), "{lean}");
                assert!(lean.contains("Litex checked defining equality"), "{lean}");
                assert!(lean.contains("reciprocal x litex_domain_fact_1"), "{lean}");
                assert!(lean.contains("simpa only [reciprocal]"), "{lean}");
                assert!(!lean.contains("sorry"), "{lean}");
                assert!(!lean.contains("axiom"), "{lean}");
            },
        );
    }

    #[test]
    fn named_function_definition_replays_refined_return_membership() {
        run_with_large_stack(
            "named_function_definition_replays_refined_return_membership",
            || {
                let source = "have fn positive_successor(x R: x > 0) R+ = x + 1\n\nforall x R:\n    x > 0\n    =>:\n        positive_successor(x) $in R+";
                let ir = test_litex_to_lean_ir(source, "named-refined-function-output.lit");
                let LitexToLeanStatementIr::HaveFnEqual(definition) = &ir[0] else {
                    panic!("the first statement should retain a checked function definition")
                };
                assert!(matches!(
                    underlying_test_proof(&definition.return_check.proof),
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::RefinedNumericMembership { .. },
                        ..
                    }
                ));
                let lean = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect("the retained return check should prove pointwise R+ membership");
                assert!(
                    lean.contains("def positive_successor : (x : ℝ) → x > 0 → ℝ"),
                    "{lean}"
                );
                assert!(lean.contains("Litex.StandardSets.RPos"), "{lean}");
                assert!(lean.contains("litex_function_return_check_"), "{lean}");
                assert!(lean.contains("simpa only [positive_successor]"), "{lean}");
                assert!(
                    !lean.contains("change True\n    trivial\n  exact (x + 1)"),
                    "{lean}"
                );
                assert!(!lean.contains("sorry"), "{lean}");
                assert!(!lean.contains("axiom"), "{lean}");
            },
        );
    }

    #[test]
    fn malformed_named_function_and_evaluation_evidence_fail_closed() {
        run_with_large_stack(
            "malformed_named_function_and_evaluation_evidence_fail_closed",
            || {
                let source = "have fn reciprocal(x R: x != 0) R = 1 / x\n\nforall x R:\n    x != 0\n    =>:\n        reciprocal(x) = 1 / x";

                let mut malformed_definition =
                    test_litex_to_lean_ir(source, "malformed-named-function-definition.lit");
                let LitexToLeanStatementIr::HaveFnEqual(definition) = &mut malformed_definition[0]
                else {
                    panic!("the first statement should be a checked function definition")
                };
                definition.defining_equality.expected_proposition =
                    definition.membership.proposition.clone();
                let error = emit_lean_from_litex_to_lean_ir(&malformed_definition)
                    .expect_err("retargeted stored definition evidence must stop emission")
                    .trace_message();
                assert!(
                    error.contains("stored fact does not match its frozen verifier target"),
                    "{error}"
                );

                let mut malformed_replay =
                    test_litex_to_lean_ir(source, "malformed-named-function-replay.lit");
                let LitexToLeanStatementIr::Fact(evaluation) = &mut malformed_replay[1] else {
                    panic!("the second statement should be an evaluation theorem")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut evaluation.fact.proof
                else {
                    panic!("the evaluation theorem should retain forall-introduction evidence")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::CheckedFunctionDefinitionReplay {
                            defining_equality_fact_id,
                            ..
                        },
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("evaluation should retain checked definition-replay evidence")
                };
                *defining_equality_fact_id =
                    FactId::new(defining_equality_fact_id.value() + 10_000);
                let error = emit_lean_from_litex_to_lean_ir(&malformed_replay)
                    .expect_err("an unknown defining equality ID must stop emission")
                    .trace_message();
                assert!(error.contains("unemitted defining equality"), "{error}");
            },
        );
    }

    #[test]
    fn source_identity_selects_the_lean_namespace() {
        run_with_large_stack("source_identity_selects_the_lean_namespace", || {
            let mut standalone_runtime = Runtime::new();
            standalone_runtime
                .new_file_path_new_env_new_name_scope("/virtual/chapter01-introduction.lit");
            let standalone =
                compile_to_lean("abstract_prop marked(x)", &mut standalone_runtime).unwrap();
            assert!(standalone.contains("\nnamespace chapter01_introduction\n\n"));
            assert_eq!(
                standalone.matches("namespace Litex.StandardSets").count(),
                1
            );
            assert!(standalone.ends_with("\nend chapter01_introduction\n"));

            let mut registered_runtime = Runtime::new();
            let module_id = registered_runtime
                .new_repository_path_new_env_new_name_scope(
                    "/virtual/project".to_string(),
                    "/virtual/project/litex.config".to_string(),
                )
                .unwrap();
            let file_id = registered_runtime
                .current_module_mut()
                .create_exported_file(
                    "/virtual/project/chapter02.lit".to_string(),
                    "A::chap2".to_string(),
                );
            registered_runtime.push_file_execution_frame(
                module_id,
                file_id,
                "/virtual/project/chapter02.lit",
            );
            let registered = compile_to_lean(
                "prop is_one(x R):\n    x = 1\n\n$is_one(1)\n\n2 $in R",
                &mut registered_runtime,
            )
            .unwrap();
            assert!(registered.contains("\nnamespace A.chap2\n\n"));
            assert!(registered.ends_with("\nend A.chap2\n"));
            assert!(!registered.contains("namespace chapter02"));
            assert_eq!(
                registered.matches("namespace Litex.StandardSets").count(),
                1
            );
            assert!(registered.contains("2 ∈ Litex.StandardSets.R"));
            assert!(registered.contains("def is_one (x : ℝ) : Prop :="));
            assert!(registered.contains("simp [is_one]"));

            let anonymous = compile_to_lean_from_source(
                "abstract_prop marked(x)",
                "/virtual/diagnostic-only.lit",
            )
            .unwrap();
            assert!(!anonymous.contains("\nnamespace diagnostic_only\n"));
            assert_eq!(anonymous.matches("\nnamespace ").count(), 1);
            assert!(anonymous.contains("\nnamespace Litex.StandardSets\n"));
        });
    }

    #[test]
    fn concise_polymorphic_fact_names_stay_inside_universe_section() {
        run_with_large_stack(
            "concise_polymorphic_fact_names_stay_inside_universe_section",
            || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("/virtual/tmp.lit");
                let output =
                    compile_to_lean("forall a set:\n    $is_set(a)", &mut runtime).unwrap();

                let theorem = output
                    .find("theorem fact4")
                    .expect("the polymorphic stored fact must be emitted");
                let section_and_namespace_end = output
                    .find("\nend\n\nend tmp\n")
                    .expect("the section must close before the namespace");

                assert!(output.contains("theorem fact4 : ∀ {α : Type u} [LitexObject α]"));
                assert!(output.contains("∀ (a : Set α), litexIsSet a"));
                assert!(!output.contains("global_fact_"));
                assert!(!output.contains("litex_carrier_"));
                assert!(!output.contains("alpha0"));
                assert!(output.lines().any(|line| line == "universe u"));
                assert!(!output.contains("LitexUniverse"));
                assert!(theorem < section_and_namespace_end);
                assert!(output.ends_with("\nend\n\nend tmp\n"));
            },
        );
    }

    #[test]
    fn default_universe_name_coexists_with_namespace_and_term_named_u() {
        run_with_large_stack(
            "default_universe_name_coexists_with_namespace_and_term_named_u",
            || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("/virtual/u.lit");
                let output =
                    compile_to_lean("forall u set:\n    $is_set(u)", &mut runtime).unwrap();

                assert!(output.contains("namespace u"), "{output}");
                assert!(output.lines().any(|line| line == "universe u"));
                assert!(output.contains("∀ {α : Type u} [LitexObject α]"));
                assert!(output.contains("∀ (u : Set α), litexIsSet u"));
                assert!(!output.contains("LitexUniverse"));
                assert!(!output.contains("LitexFact"));
            },
        );
    }

    #[test]
    fn homogeneous_generic_set_relations_share_one_unicode_carrier() {
        run_with_large_stack(
            "homogeneous_generic_set_relations_share_one_unicode_carrier",
            || {
                let output = compile_to_lean_from_source(
                    "forall a set, b set:\n    a = b\n    =>:\n        a = b\n",
                    "homogeneous-generic-carrier",
                )
                .unwrap();

                assert!(output.contains(
                    "∀ {α : Type u} [LitexObject α], ∀ (a : Set α), ∀ (b : Set α), ∀ (litex_domain_fact_1 : a = b), a = b"
                ), "{output}");
                assert!(!output.contains("alpha0"), "{output}");
                assert!(!output.contains("alpha1"), "{output}");

                let unrelated = compile_to_lean_from_source(
                    "forall a set, b set:\n    $is_set(a)\n    =>:\n        $is_set(b)\n",
                    "independent-generic-carriers",
                )
                .unwrap();
                assert!(unrelated.contains(
                    "∀ {α : Type u} [LitexObject α], ∀ (a : Set α), ∀ {α1 : Type u} [LitexObject α1], ∀ (b : Set α1)"
                ), "{unrelated}");
            },
        );
    }

    #[test]
    fn litex_to_lean_ir_mode_records_recursive_ir_and_emits_only_trust_as_axiom() {
        run_with_large_stack(
            "litex_to_lean_ir_mode_records_recursive_ir_and_emits_only_trust_as_axiom",
            || {
                let source = r#"
abstract_prop marked(x)
abstract_prop unparameterized()

prop is_one(x R):
    x = 1

trust forall x R:
    x != 0
    =>:
        $marked(x)

$is_one(1)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x

forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0

forall x R:
    x != 0
    =>:
        x != 0
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("litex-to-lean-ir-mvp.lit");
                let output = compile_to_lean(source, &mut runtime).unwrap();

                assert!(output.starts_with("import Mathlib\n\nnamespace Litex.BuiltinRules\n\n"));
                assert!(
                    output.find("end Litex.BuiltinRules").unwrap()
                        < output.find("namespace litex_to_lean_ir_mvp").unwrap()
                );
                assert!(output.contains("class LitexObject (α : Type u) : Prop where"));
                assert!(!output.contains("LitexFact"));
                assert!(output.contains("opaque marked {α : Type u} [LitexObject α] : α → Prop"));
                assert!(output.contains("opaque unparameterized : Prop"));
                assert!(!output.contains("namespace LitexGenerated"));
                assert!(!output.contains("end LitexGenerated"));
                assert!(output.lines().any(|line| line == "universe u"));
                assert!(!output.contains("LitexUniverse"));
                assert!(output.ends_with("\nend litex_to_lean_ir_mvp\n"));
                assert!(output.contains("def is_one (x : ℝ) : Prop :="));
                assert!(!output.contains("LitexSet"));
                assert_eq!(output.matches("\naxiom fact").count(), 1);
                assert!(output.contains(":= fact"));
                assert!(output.contains("is_one 1"));
                assert!(output.contains("simp [is_one]"));
                assert!(output.contains("let proof_arg_"));
                assert!(output.contains("intro a litex_param_fact_1"));
                assert!(output.contains("b litex_param_fact_2"));
                assert!(output.contains("x litex_param_fact_3"));
                assert!(output.contains("litex_domain_fact_1"));
                assert!(output.contains("field_simp [litex_domain_fact_"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn compile_to_lean_statement_scopes_lower_have_cases_and_contra() {
        run_with_large_stack(
            "compile_to_lean_statement_scopes_lower_have_cases_and_contra",
            || {
                let source = r#"
have x R = 2

by cases:
    ? x = x
    case x = 2:
        have y R = 3
        y = 3
    case x != 2:
        impossible x != 2

by contra:
    ? 2 = 2
    2 = 2
    impossible 2 != 2
"#;
                let statement_irs = test_litex_to_lean_ir(source, "statement-scopes-ir.lit");
                assert!(matches!(
                    statement_irs[0],
                    LitexToLeanStatementIr::HaveObjEqual(_)
                ));
                let LitexToLeanStatementIr::Proof(by_cases) = &statement_irs[1] else {
                    panic!("second statement should be proof IR");
                };
                assert!(matches!(
                    by_cases.facts[0].proof,
                    LitexToLeanFactProofIr::CaseSplit { .. }
                ));
                let LitexToLeanStatementIr::Proof(by_contra) = &statement_irs[2] else {
                    panic!("third statement should be proof IR");
                };
                assert!(matches!(
                    by_contra.facts[0].proof,
                    LitexToLeanFactProofIr::ByContradiction { .. }
                ));

                let output =
                    compile_to_lean_from_source(source, "statement-scopes-output").unwrap();
                assert!(output.contains("def x : ℝ := 2"), "{output}");
                assert!(output.contains("let y : ℝ := 3"), "{output}");
                assert!(output.contains("simpa only [x] using"), "{output}");
                assert!(output.contains("Classical.em (x = 2)"), "{output}");
                assert!(output.contains("rcases"), "{output}");
                assert!(
                    output.contains("apply Classical.byContradiction"),
                    "{output}"
                );
                assert!(!output.contains("axiom fact"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_statement_scopes_reject_malformed_local_premises() {
        run_with_large_stack(
            "compile_to_lean_statement_scopes_reject_malformed_local_premises",
            || {
                let source = r#"
have x R = 2

by cases:
    ? x = x
    case x = 2
    case x != 2:
        impossible x != 2

by contra:
    ? 2 = 2
    impossible 2 != 2
"#;
                let mut malformed_cases =
                    test_litex_to_lean_ir(source, "malformed-case-assumption.lit");
                let LitexToLeanStatementIr::Proof(by_cases) = &mut malformed_cases[1] else {
                    panic!("second statement should be proof IR");
                };
                let LitexToLeanFactProofIr::CaseSplit { branches, .. } =
                    &mut by_cases.facts[0].proof
                else {
                    panic!("second statement should contain case-split evidence");
                };
                branches[0].assumption.fact = branches[1].assumption.fact.clone();
                let error = emit_lean_from_litex_to_lean_ir(&malformed_cases)
                    .expect_err("a branch premise that disagrees with coverage must be rejected")
                    .trace_message();
                assert!(
                    error.contains("case-split assumption does not match its coverage branch"),
                    "{error}"
                );

                let mut malformed_contra =
                    test_litex_to_lean_ir(source, "malformed-contra-assumption.lit");
                let LitexToLeanStatementIr::Proof(by_contra) = &mut malformed_contra[2] else {
                    panic!("third statement should be proof IR");
                };
                let target = by_contra.facts[0].proposition.clone();
                let LitexToLeanFactProofIr::ByContradiction {
                    reverse_assumption, ..
                } = &mut by_contra.facts[0].proof
                else {
                    panic!("third statement should contain contradiction evidence");
                };
                reverse_assumption.fact = target;
                let error = emit_lean_from_litex_to_lean_ir(&malformed_contra)
                    .expect_err("a reverse premise that is not the goal negation must be rejected")
                    .trace_message();
                assert!(
                    error.contains("reverse assumption is not the logical negation"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_choice_have_uses_checked_nonempty_certificate() {
        run_with_large_stack(
            "compile_to_lean_choice_have_uses_checked_nonempty_certificate",
            || {
                let source = include_str!(
                    "../../examples/05_compiler_interop/compile_to_lean_choice_have.lit"
                );
                let statement_irs = test_litex_to_lean_ir(source, "choice-have-ir.lit");
                let LitexToLeanStatementIr::HaveObjChoice(top_level_choice) = &statement_irs[0]
                else {
                    panic!("first statement should be object-choice IR");
                };
                assert_eq!(top_level_choice.choices.len(), 1);
                assert!(matches!(
                    underlying_test_proof(&top_level_choice.choices[0].nonempty_proof.proof),
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::RealSetNonempty,
                        ..
                    }
                ));
                assert!(matches!(
                    top_level_choice.choices[0].membership.proof,
                    LitexToLeanFactProofIr::ObjectChoice { .. }
                ));

                let LitexToLeanStatementIr::Proof(by_contra) = &statement_irs[2] else {
                    panic!("third statement should be proof IR");
                };
                let LitexToLeanFactProofIr::ByContradiction { steps, .. } =
                    &by_contra.facts[0].proof
                else {
                    panic!("third statement should retain contradiction evidence");
                };
                assert!(matches!(steps[0], LitexToLeanStatementIr::HaveObjChoice(_)));

                let output = compile_to_lean_from_source(source, "choice-have-output").unwrap();
                assert!(
                    output.contains(
                        "def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty"
                    ),
                    "{output}"
                );
                assert!(output.contains("theorem litex_choice_source_"), "{output}");
                assert!(
                    output.contains(
                        "noncomputable def selected : ℝ := Exists.choose litex_choice_source_"
                    ),
                    "{output}"
                );
                assert!(
                    output.contains("let local_choice : ℝ := Exists.choose proof_fact_"),
                    "{output}"
                );
                assert!(output.contains("Exists.choose_spec"), "{output}");
                assert!(!output.contains("axiom fact"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_choice_have_rejects_missing_or_mismatched_evidence() {
        run_with_large_stack(
            "compile_to_lean_choice_have_rejects_missing_or_mismatched_evidence",
            || {
                let source = "have selected R";
                let mut missing = test_litex_to_lean_ir(source, "choice-have-missing-proof.lit");
                let LitexToLeanStatementIr::HaveObjChoice(choice) = &mut missing[0] else {
                    panic!("statement should be object-choice IR");
                };
                choice.choices[0].nonempty_proof.proof = LitexToLeanFactProofIr::Unsupported {
                    reason: "missing checked nonemptiness backend".to_string(),
                };
                let error = emit_lean_from_litex_to_lean_ir(&missing)
                    .expect_err("choice without a checked nonemptiness backend must fail")
                    .trace_message();
                assert!(
                    error.contains("missing checked nonemptiness backend"),
                    "{error}"
                );

                let mut mismatched = test_litex_to_lean_ir(source, "choice-have-wrong-source.lit");
                let LitexToLeanStatementIr::HaveObjChoice(choice) = &mut mismatched[0] else {
                    panic!("statement should be object-choice IR");
                };
                choice.choices[0].nonempty_proof.proposition =
                    choice.choices[0].membership.proposition.clone();
                let error = emit_lean_from_litex_to_lean_ir(&mismatched)
                    .expect_err("choice source from another fact family must fail")
                    .trace_message();
                assert!(
                    error.contains("object-choice source is not a nonempty-set fact"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_exist_have_uses_checked_introduction_and_projections() {
        run_with_large_stack(
            "compile_to_lean_exist_have_uses_checked_introduction_and_projections",
            || {
                let source = include_str!(
                    "../../examples/05_compiler_interop/compile_to_lean_exist_have.lit"
                );
                let statement_irs = test_litex_to_lean_ir(source, "exist-have-ir.lit");
                let LitexToLeanStatementIr::Proof(introduction) = &statement_irs[0] else {
                    panic!("first statement should be existential-introduction proof IR");
                };
                assert!(matches!(
                    introduction.facts[0].proof,
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::ExistIntroduction { .. },
                        ..
                    }
                ));
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) = &statement_irs[1]
                else {
                    panic!("second statement should be existential-elimination IR");
                };
                assert_eq!(obtain.witnesses.len(), 1);
                assert_eq!(obtain.projections.len(), 3);
                assert!(matches!(
                    obtain.projections[0].proof,
                    LitexToLeanFactProofIr::ExistentialElimination {
                        role: LitexToLeanExistentialProjectionRoleIr::ParameterType {
                            witness_index: 0
                        },
                        ..
                    }
                ));
                assert!(matches!(
                    obtain.projections[2].proof,
                    LitexToLeanFactProofIr::ExistentialElimination {
                        role: LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index: 1 },
                        ..
                    }
                ));
                assert!(matches!(
                    statement_irs[5],
                    LitexToLeanStatementIr::HaveExistentialWitness(_)
                ));
                let LitexToLeanStatementIr::Proof(by_contra) = &statement_irs[9] else {
                    panic!("last statement should be contradiction proof IR");
                };
                let LitexToLeanFactProofIr::ByContradiction { steps, .. } =
                    &by_contra.facts[0].proof
                else {
                    panic!("last statement should retain contradiction evidence");
                };
                assert!(matches!(
                    steps[0],
                    LitexToLeanStatementIr::HaveExistentialWitness(_)
                ));

                let output = compile_to_lean_from_source(source, "exist-have-output").unwrap();
                assert!(output.contains("∃ source : ℝ"), "{output}");
                assert!(output.contains("theorem litex_exist_source_"), "{output}");
                assert!(
                    output.contains("noncomputable def selected : ℝ := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("noncomputable def shorthand : ℝ := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("let local_selected : ℝ := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("noncomputable def chosen_left : ℝ := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("noncomputable def chosen_right : ℝ := Exists.choose ("),
                    "{output}"
                );
                assert!(output.contains("Exists.choose_spec"), "{output}");
                assert!(!output.contains("axiom fact"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_exist_have_rejects_malformed_evidence() {
        run_with_large_stack(
            "compile_to_lean_exist_have_rejects_malformed_evidence",
            || {
                let source = include_str!(
                    "../../examples/05_compiler_interop/compile_to_lean_exist_have.lit"
                );
                let mut malformed_projection =
                    test_litex_to_lean_ir(source, "exist-wrong-projection.lit");
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) =
                    &mut malformed_projection[1]
                else {
                    panic!("second statement should be existential-elimination IR");
                };
                let LitexToLeanFactProofIr::ExistentialElimination {
                    expected_proposition,
                    ..
                } = &mut obtain.projections[0].proof
                else {
                    panic!("first projection should contain elimination evidence");
                };
                *expected_proposition = obtain.source.proposition.clone();
                let error = emit_lean_from_litex_to_lean_ir(&malformed_projection)
                    .expect_err("a mismatched existential projection must be rejected")
                    .trace_message();
                assert!(
                    error.contains("disagrees with its retained expected proposition"),
                    "{error}"
                );

                let mut malformed_introduction =
                    test_litex_to_lean_ir(source, "exist-wrong-introduction.lit");
                let LitexToLeanStatementIr::Proof(introduction) = &mut malformed_introduction[0]
                else {
                    panic!("first statement should be proof IR");
                };
                let wrong_body = introduction.facts[0].proposition.clone();
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::ExistIntroduction {
                            expected_body_facts,
                            ..
                        },
                    ..
                } = &mut introduction.facts[0].proof
                else {
                    panic!("first proof should contain existential-introduction evidence");
                };
                expected_body_facts[0] = wrong_body;
                let error = emit_lean_from_litex_to_lean_ir(&malformed_introduction)
                    .expect_err("mismatched existential-introduction evidence must be rejected")
                    .trace_message();
                assert!(
                    error.contains("body evidence disagrees with its retained proposition"),
                    "{error}"
                );

                let mut malformed_alpha =
                    test_litex_to_lean_ir(source, "exist-wrong-alpha-source.lit");
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) =
                    &mut malformed_alpha[1]
                else {
                    panic!("second statement should be existential-elimination IR");
                };
                let wrong_source = obtain.projections[0].proposition.clone();
                let LitexToLeanFactProofIr::ExistentialAlphaRenameCitation {
                    source_proposition,
                    ..
                } = underlying_test_proof_mut(&mut obtain.source.proof)
                else {
                    panic!("source proof should retain alpha-renaming evidence");
                };
                *source_proposition = wrong_source;
                let error = emit_lean_from_litex_to_lean_ir(&malformed_alpha)
                    .expect_err("a non-existential alpha source must be rejected")
                    .trace_message();
                assert!(
                    error.contains("requires two positive `exist` facts"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_obtain_from_existential_prop_uses_checked_definition_projection() {
        run_with_large_stack(
            "compile_to_lean_obtain_from_existential_prop_uses_checked_definition_projection",
            || {
                let source = include_str!(
                    "../../examples/01_proof_patterns/obtain_from_existential_prop.lit"
                );
                let statement_irs = test_litex_to_lean_ir(source, "obtain-from-prop-ir.lit");
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) = &statement_irs[2]
                else {
                    panic!("third statement should be existential-elimination IR");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::DefinitionProjection {
                            definition,
                            expected_source,
                            expected_target,
                        },
                    parameter_requirements,
                    premises,
                } = &obtain.source.proof
                else {
                    panic!("obtain source should retain definition-projection evidence");
                };
                assert_eq!(definition, "has_copy");
                assert_eq!(expected_source.to_string(), "$has_copy(2)");
                assert_eq!(
                    expected_target.to_string(),
                    obtain.source.proposition.to_string()
                );
                assert!(parameter_requirements.is_empty());
                assert_eq!(premises.len(), 1);
                assert_eq!(premises[0].proposition.to_string(), "$has_copy(2)");

                let output =
                    compile_to_lean_from_source(source, "obtain-from-prop-output.lit").unwrap();
                assert!(output.contains("simpa only [has_copy] using"), "{output}");
                assert!(
                    output.contains("noncomputable def copy : ℝ := Exists.choose"),
                    "{output}"
                );
                assert!(!output.contains("axiom fact"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_atomic_fact_witness_uses_checked_definition_introduction() {
        run_with_large_stack(
            "compile_to_lean_atomic_fact_witness_uses_checked_definition_introduction",
            || {
                let source =
                    include_str!("../../examples/01_proof_patterns/witness_atomic_fact.lit");
                let statement_irs = test_litex_to_lean_ir(source, "witness-atomic-fact-ir.lit");
                let LitexToLeanStatementIr::Proof(introduction) = &statement_irs[1] else {
                    panic!("second statement should be atomic-fact introduction IR");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::DefinitionIntroduction {
                            definition,
                            expected_source,
                            expected_target,
                        },
                    parameter_requirements,
                    premises,
                } = &introduction.facts[0].proof
                else {
                    panic!("atomic fact witness should retain definition-introduction evidence");
                };
                assert_eq!(definition, "divides");
                assert!(matches!(expected_source, Fact::ExistFact(_)));
                assert_eq!(expected_target.to_string(), "$divides(6, 2)");
                assert!(parameter_requirements.is_empty());
                assert_eq!(premises.len(), 1);
                assert!(matches!(
                    premises[0].proof,
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::ExistIntroduction { .. },
                        ..
                    }
                ));
                assert!(introduction.inferred_facts.iter().any(|fact| matches!(
                    fact.proof,
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::DefinitionProjection { .. },
                        ..
                    }
                )));

                let output =
                    compile_to_lean_from_source(source, "witness-atomic-fact-output.lit").unwrap();
                assert!(output.contains("simpa only [divides] using"), "{output}");
                assert!(output.contains("exact ⟨(3 : ℤ)"), "{output}");
                assert!(!output.contains("axiom fact"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_atomic_fact_witness_rejects_exist_unique_before_lowering() {
        run_with_large_stack(
            "compile_to_lean_atomic_fact_witness_rejects_exist_unique_before_lowering",
            || {
                let source = r#"
prop unique_value(a R):
    exist! x R st {x = a}

trust forall u, v R:
    u = 2
    v = 2
    =>:
        u = v

witness $unique_value(2) from 2:
    2 = 2
"#;
                let error = compile_to_lean_from_source_with_report(
                    source,
                    "witness-atomic-exist-unique-boundary.lit",
                )
                .expect_err("runtime must reject unique-existence atomic-fact witnesses");
                let message = error.trace_message();
                assert!(
                    message.contains(
                        "atomic fact witness does not support the `exist!` definition of `unique_value`"
                    ),
                    "{message}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_atomic_fact_witness_rejects_malformed_introduction_ir() {
        run_with_large_stack(
            "compile_to_lean_atomic_fact_witness_rejects_malformed_introduction_ir",
            || {
                let source =
                    include_str!("../../examples/01_proof_patterns/witness_atomic_fact.lit");

                let mut wrong_target =
                    test_litex_to_lean_ir(source, "witness-atomic-fact-wrong-target.lit");
                let LitexToLeanStatementIr::Proof(introduction) = &mut wrong_target[1] else {
                    panic!("second statement should be atomic-fact introduction IR");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::DefinitionIntroduction {
                            expected_target, ..
                        },
                    premises,
                    ..
                } = &mut introduction.facts[0].proof
                else {
                    panic!("atomic fact witness should retain definition-introduction evidence");
                };
                *expected_target = premises[0].proposition.clone();
                let error = emit_lean_from_litex_to_lean_ir(&wrong_target)
                    .expect_err("a changed definition-introduction target must be rejected")
                    .trace_message();
                assert!(
                    error.contains(
                        "definition-introduction target disagrees with its retained expected proposition"
                    ),
                    "{error}"
                );

                let mut missing_source =
                    test_litex_to_lean_ir(source, "witness-atomic-fact-missing-source.lit");
                let LitexToLeanStatementIr::Proof(introduction) = &mut missing_source[1] else {
                    panic!("second statement should be atomic-fact introduction IR");
                };
                let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                    &mut introduction.facts[0].proof
                else {
                    panic!("atomic fact witness should retain rule-application evidence");
                };
                premises.clear();
                let error = emit_lean_from_litex_to_lean_ir(&missing_source)
                    .expect_err("definition introduction without its source must be rejected")
                    .trace_message();
                assert!(
                    error.contains(
                        "definition-introduction evidence requires no parameter requirements and exactly one source premise"
                    ),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_obtain_from_existential_prop_rejects_malformed_projection_ir() {
        run_with_large_stack(
            "compile_to_lean_obtain_from_existential_prop_rejects_malformed_projection_ir",
            || {
                let source = include_str!(
                    "../../examples/01_proof_patterns/obtain_from_existential_prop.lit"
                );

                let mut wrong_source = test_litex_to_lean_ir(source, "obtain-wrong-source.lit");
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) = &mut wrong_source[2]
                else {
                    panic!("third statement should be existential-elimination IR");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::DefinitionProjection {
                            expected_source, ..
                        },
                    ..
                } = &mut obtain.source.proof
                else {
                    panic!("obtain source should retain definition-projection evidence");
                };
                *expected_source = obtain.source.proposition.clone();
                let error = emit_lean_from_litex_to_lean_ir(&wrong_source)
                    .expect_err("a changed projection source must be rejected")
                    .trace_message();
                assert!(
                    error.contains(
                        "definition-projection source disagrees with its retained expected proposition"
                    ),
                    "{error}"
                );

                let mut wrong_target = test_litex_to_lean_ir(source, "obtain-wrong-target.lit");
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) = &mut wrong_target[2]
                else {
                    panic!("third statement should be existential-elimination IR");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::DefinitionProjection {
                            expected_target, ..
                        },
                    premises,
                    ..
                } = &mut obtain.source.proof
                else {
                    panic!("obtain source should retain definition-projection evidence");
                };
                *expected_target = premises[0].proposition.clone();
                let error = emit_lean_from_litex_to_lean_ir(&wrong_target)
                    .expect_err("a changed projection target must be rejected")
                    .trace_message();
                assert!(
                    error.contains(
                        "definition-projection target disagrees with its retained expected proposition"
                    ),
                    "{error}"
                );

                let mut missing_source = test_litex_to_lean_ir(source, "obtain-missing-source.lit");
                let LitexToLeanStatementIr::HaveExistentialWitness(obtain) = &mut missing_source[2]
                else {
                    panic!("third statement should be existential-elimination IR");
                };
                let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                    &mut obtain.source.proof
                else {
                    panic!("obtain source should retain rule-application evidence");
                };
                premises.clear();
                let error = emit_lean_from_litex_to_lean_ir(&missing_source)
                    .expect_err("a projection without its source proof must be rejected")
                    .trace_message();
                assert!(
                    error.contains(
                        "definition-projection evidence requires no parameter requirements and exactly one source premise"
                    ),
                    "{error}"
                );

                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("obtain-tampered-certificate.lit");
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut obtain_result = None;
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let is_obtain = matches!(
                        &statement,
                        Stmt::DefObjStmt(DefObjStmt::ObtainObjFromAtomicFact(_))
                    );
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    if is_obtain {
                        obtain_result = Some(result);
                        break;
                    }
                }
                let mut obtain_result = obtain_result.expect("obtain result should be present");
                let success = obtain_result
                    .non_factual_success_mut()
                    .expect("obtain should have a non-factual success result");
                let projection = success.inside_results[0]
                    .factual_success_mut()
                    .expect("obtain source should be a factual projection result");
                let VerifiedByResult::BuiltinRule(verification) = &mut projection.verified_by
                else {
                    panic!("projection should retain builtin-rule verification evidence");
                };
                let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) =
                    &mut verification.evidence
                else {
                    panic!("projection should retain its typed definition certificate");
                };
                evidence.definition.name = "wrong_definition".to_string();
                let error = runtime
                    .build_litex_to_lean_ir_statement(&obtain_result)
                    .expect_err("a changed verifier-side definition certificate must be rejected")
                    .trace_message();
                assert!(
                    error.contains(
                        "source prop `has_copy` does not match retained definition `wrong_definition`"
                    ),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_exist_have_rejects_sanitized_binder_capture() {
        run_with_large_stack(
            "compile_to_lean_exist_have_rejects_sanitized_binder_capture",
            || {
                let source = r#"
prop captured(xα set):
    exist xβ xα st {xβ = xβ}
"#;
                let error = compile_to_lean_from_source(source, "exist-name-capture.lit")
                    .expect_err("distinct SymbolIds with one Lean spelling must be rejected")
                    .trace_message();
                assert!(
                    error.contains("cannot safely emit the existential binder"),
                    "{error}"
                );
                assert!(
                    error.contains("also becomes Lean identifier `x_`"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_statement_scope_boundaries_remain_explicit() {
        run_with_large_stack(
            "compile_to_lean_statement_scope_boundaries_remain_explicit",
            || {
                let selection = compile_to_lean_from_source_with_report(
                    "have arbitrary_nonempty_set nonempty_set",
                    "unsupported-meta-selection-have",
                )
                .unwrap();
                assert_eq!(selection.status, LitexToLeanCompilationStatus::Incomplete);
                assert_eq!(selection.unsupported.len(), 1);
                assert!(selection.unsupported[0]
                    .reason
                    .contains("meta-level parameter type `nonempty_set`"));

                let unsupported_value_check = compile_to_lean_from_source_with_report(
                    "have carrier set = R",
                    "unsupported-have-value-check",
                )
                .unwrap();
                assert_eq!(
                    unsupported_value_check.status,
                    LitexToLeanCompilationStatus::Incomplete
                );
                assert_eq!(unsupported_value_check.unsupported.len(), 1);
                assert!(unsupported_value_check.unsupported[0]
                    .reason
                    .contains("Every object is a set"));
                assert!(!unsupported_value_check.lean_code.contains("def carrier"));
                assert!(!unsupported_value_check.lean_code.contains("sorry"));

                let proof_step = compile_to_lean_from_source_with_report(
                    r#"
by cases:
    ? 1 = 1
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
"#,
                    "unsupported-case-step",
                )
                .unwrap();
                assert_eq!(proof_step.status, LitexToLeanCompilationStatus::Incomplete);
                assert_eq!(proof_step.unsupported.len(), 1);
                assert!(proof_step.unsupported[0].reason.contains("DoNothingStmt"));
                assert!(!proof_step.lean_code.contains("sorry"));
                assert!(!proof_step.lean_code.contains("axiom fact"));

                let preimage = compile_to_lean_from_source_with_report(
                    r#"
have fn square(x R) R = x^2
square(2) $in fn_range(square)
have by preimage root from square(2) $in fn_range(square)
"#,
                    "unsupported-function-preimage",
                )
                .unwrap();
                assert_eq!(preimage.status, LitexToLeanCompilationStatus::Incomplete);
                assert!(!preimage
                    .unsupported
                    .iter()
                    .any(|item| item.reason.contains("HaveFnEqualStmt")));
                assert!(preimage.lean_code.contains("def square"));
                assert!(preimage
                    .unsupported
                    .iter()
                    .any(|item| item.reason.contains("HaveByPreimageStmt")));
                assert!(!preimage.lean_code.contains("sorry"));
                assert!(!preimage.lean_code.contains("axiom fact"));
            },
        );
    }

    #[test]
    fn litex_to_lean_ir_preserves_fact_ids_and_verified_routes() {
        run_with_large_stack(
            "litex_to_lean_ir_preserves_fact_ids_and_verified_routes",
            || {
                let source = r#"
abstract_prop marked(x)

prop is_one(x R):
    x = 1

trust forall x R:
    x != 0
    =>:
        $marked(x)

$is_one(1)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("litex-to-lean-ir-shape");
                runtime.replace_litex_to_lean_ir_mode(true);
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut statement_irs = Vec::new();
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    statement_irs.push(result.litex_to_lean_ir().unwrap().clone());
                }

                assert!(matches!(
                    statement_irs[0],
                    LitexToLeanStatementIr::AbstractProp(_)
                ));
                assert!(matches!(statement_irs[1], LitexToLeanStatementIr::Prop(_)));
                let LitexToLeanStatementIr::Trust(trust) = &statement_irs[2] else {
                    panic!("third IR item should be trust");
                };
                let trusted_forall_id = trust.facts[0]
                    .fact_id
                    .expect("trusted fact must have an ID");
                assert!(matches!(
                    trust.facts[0].proof,
                    LitexToLeanFactProofIr::Trusted
                ));

                let LitexToLeanStatementIr::Fact(by_definition) = &statement_irs[3] else {
                    panic!("fourth IR item should be a fact");
                };
                assert!(matches!(
                    underlying_test_proof(&by_definition.fact.proof),
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::DefinitionReduction { definition },
                        ..
                    } if definition == "is_one"
                ));

                let LitexToLeanStatementIr::Fact(local_requirement_forall) = &statement_irs[4]
                else {
                    panic!("fifth IR item should be a forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction {
                    premises,
                    conclusions,
                    ..
                } = &local_requirement_forall.fact.proof
                else {
                    panic!("sixth fact should retain forall-introduction evidence");
                };
                assert_eq!(premises.len(), 2);
                let local_nonzero_id = premises[0].fact_id;
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::KnownForallInstantiation { source_fact_id, .. },
                    parameter_requirements,
                    premises: requirements,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("conclusion should retain known-forall evidence");
                };
                assert_eq!(*source_fact_id, trusted_forall_id);
                assert_eq!(parameter_requirements.len(), 1);
                assert_eq!(requirements.len(), 1);
                assert!(matches!(
                    underlying_test_proof(&requirements[0].proof),
                    LitexToLeanFactProofIr::KnownFactCitation { source_fact_id }
                        if *source_fact_id == local_nonzero_id
                ));

                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[5] else {
                    panic!("sixth IR item should be a fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction {
                    parameter_premises,
                    premises,
                    inferred_premises,
                    conclusions,
                } = &forall.fact.proof
                else {
                    panic!("last fact should retain forall-introduction evidence");
                };
                assert_eq!(parameter_premises.len(), 3);
                assert_eq!(premises.len(), 1);
                assert!(inferred_premises.is_empty());
                let forall_id = forall.fact.fact_id.expect("stored forall must have an ID");
                assert!(parameter_premises
                    .iter()
                    .chain(premises.iter())
                    .all(|premise| premise.fact_id < forall_id));
                assert!(matches!(
                    underlying_test_proof(&conclusions[0].proof),
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::Normalization {
                            kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                        },
                        ..
                    }
                ));
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rule_ir_preserves_recursive_evidence() {
        run_with_large_stack(
            "compile_to_lean_builtin_rule_ir_preserves_recursive_evidence",
            || {
                let source = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
"#;
                let statement_irs = test_litex_to_lean_ir(source, "builtin-rule-ir-shape");
                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction {
                    premises,
                    conclusions,
                    ..
                } = &forall.fact.proof
                else {
                    panic!("tracer should retain its temporary forall environment");
                };
                assert_eq!(premises.len(), 2);
                assert_eq!(conclusions.len(), 1);

                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                    parameter_requirements,
                    premises: rule_premises,
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("forall conclusion should retain a registered rule certificate");
                };
                assert_eq!(application.rule_id.as_str(), "nonzero.div");
                assert_eq!(application.bindings.len(), 2);
                assert_eq!(application.parameter_requirement_count, 2);
                assert_eq!(application.premise_count, 2);
                assert_eq!(parameter_requirements.len(), 2);
                let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) =
                    &conclusions[0].proposition
                else {
                    panic!("tracer conclusion should remain a non-equality fact");
                };
                let Obj::Div(quotient) = &target.left else {
                    panic!("tracer conclusion should retain its quotient");
                };
                assert_eq!(
                    application.bindings[0].object,
                    LitexToLeanObjectIr::lower(quotient.left.as_ref()).unwrap()
                );
                assert_eq!(
                    application.bindings[1].object,
                    LitexToLeanObjectIr::lower(quotient.right.as_ref()).unwrap()
                );
                assert_eq!(rule_premises.len(), 2);
                for (rule_premise, local_premise) in rule_premises.iter().zip(premises.iter()) {
                    assert!(matches!(
                        underlying_test_proof(&rule_premise.proof),
                        LitexToLeanFactProofIr::KnownFactCitation { source_fact_id }
                            if *source_fact_id == local_premise.fact_id
                    ));
                }
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rule_ir_emits_checked_lemma_application() {
        run_with_large_stack(
            "compile_to_lean_builtin_rule_ir_emits_checked_lemma_application",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_builtin_rule_ir.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(&path.to_string_lossy());
                let output = compile_to_lean(&source, &mut runtime).unwrap();

                assert!(output.contains("namespace compile_to_lean_builtin_rule_ir"));
                assert!(output.contains("_root_.Litex.BuiltinRules.nonzero_div"));
                assert!(output.contains("have proof_fact_"));
                assert!(!output.contains("OtherUnsupported"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rule_ir_preserves_reverse_orientation() {
        run_with_large_stack(
            "compile_to_lean_builtin_rule_ir_preserves_reverse_orientation",
            || {
                let source = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        0 != a / b
"#;
                let output = compile_to_lean_from_source(source, "builtin-rule-reverse").unwrap();
                assert!(output.contains("Ne.symm (div_ne_zero proof_fact_"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rule_ir_rejects_malformed_certificate() {
        run_with_large_stack(
            "compile_to_lean_builtin_rule_ir_rejects_malformed_certificate",
            || {
                let source = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
"#;
                let mut statement_irs = test_litex_to_lean_ir(source, "builtin-rule-invalid-ir");
                let LitexToLeanStatementIr::Fact(forall) = &mut statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("tracer conclusion should be a rule application");
                };
                premises.pop();

                let error = emit_lean_from_litex_to_lean_ir(&statement_irs)
                    .expect_err("malformed builtin certificate must stop emission")
                    .trace_message();
                assert!(error.contains("expected 2 parameter requirements and 2 premises"));
                assert!(error.contains("received 2 and 1"));
            },
        );
    }

    #[test]
    fn compile_to_lean_registered_rule_linker_rejects_unknown_id_and_stale_fingerprint() {
        run_with_large_stack(
            "compile_to_lean_registered_rule_linker_rejects_unknown_id_and_stale_fingerprint",
            || {
                let source = r#"
forall x R:
    0 <= abs(x)
"#;
                let original = test_litex_to_lean_ir(source, "registered-rule-linker-negative");

                let mut unknown = original.clone();
                let LitexToLeanStatementIr::Fact(forall) = &mut unknown[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("tracer conclusion should retain registered evidence");
                };
                application.rule_id = RuleId::new("unknown.missing").unwrap();
                let error = emit_lean_from_litex_to_lean_ir(&unknown)
                    .expect_err("unknown registered RuleId must stop emission")
                    .trace_message();
                assert!(error.contains("no Lean adapter for local builtin `unknown.missing`"));

                let mut stale = original;
                let LitexToLeanStatementIr::Fact(forall) = &mut stale[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("tracer conclusion should retain registered evidence");
                };
                application.semantic_fingerprint =
                    RuleFingerprint::from_hex("0".repeat(64)).unwrap();
                let error = emit_lean_from_litex_to_lean_ir(&stale)
                    .expect_err("stale registered fingerprint must stop emission")
                    .trace_message();
                assert!(error.contains(
                    "Lean adapter fingerprint disagrees with local builtin `order.abs_nonnegative`"
                ));
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rule_ir_rejects_resolved_zero_without_equality_evidence() {
        run_with_large_stack(
            "compile_to_lean_builtin_rule_ir_rejects_resolved_zero_without_equality_evidence",
            || {
                let source = r#"
forall a, b, z R:
    z = 0
    a != 0
    b != 0
    =>:
        a / b != z
"#;
                let error = compile_to_lean_from_source(source, "builtin-rule-resolved-zero")
                    .expect_err("a resolved zero alias lacks compiler equality evidence")
                    .trace_message();
                assert!(error.contains("no checked backend"));
                assert!(error.contains("div_not_equal_zero_from_numerator_nonzero"));
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rules_20_use_distinct_registered_rules_and_compile() {
        run_with_large_stack(
            "compile_to_lean_builtin_rules_20_use_distinct_registered_rules_and_compile",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit");
                let source = fs::read_to_string(&path).unwrap();
                let statement_irs = test_litex_to_lean_ir(&source, "builtin-rules-20-ir");
                let mut rule_names = Vec::new();
                for statement in statement_irs.iter() {
                    let LitexToLeanStatementIr::Fact(forall) = statement else {
                        panic!("each tracer statement should be a stored forall fact");
                    };
                    let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                        &forall.fact.proof
                    else {
                        panic!("each tracer statement should retain forall evidence");
                    };
                    let LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                        ..
                    } = underlying_test_proof(&conclusions[0].proof)
                    else {
                        panic!("each tracer conclusion should retain registered-rule evidence");
                    };
                    rule_names.push(application.rule_id.as_str().to_string());
                }
                rule_names.sort();
                rule_names.dedup();
                assert_eq!(rule_names.len(), 20, "{rule_names:#?}");
                assert!(rule_names.contains(&"order.less_equal_of_less".to_string()));
                assert!(rule_names.contains(&"order.div_positive".to_string()));

                let output = emit_lean_from_litex_to_lean_ir(&statement_irs).unwrap();
                assert_eq!(output.matches("theorem fact").count(), 20);
                assert_eq!(output.matches("_root_.Litex.BuiltinRules.").count(), 20);
                assert!(output.contains("_root_.Litex.BuiltinRules.order_less_equal_of_less"));
                assert!(output.contains("_root_.Litex.BuiltinRules.order_div_positive"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn compile_to_lean_builtin_rules_20_reject_malformed_premise_arity() {
        run_with_large_stack(
            "compile_to_lean_builtin_rules_20_reject_malformed_premise_arity",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut statement_irs =
                    test_litex_to_lean_ir(&source, "builtin-rules-20-malformed");
                let LitexToLeanStatementIr::Fact(forall) = &mut statement_irs[0] else {
                    panic!("first tracer statement should be a stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("first tracer statement should retain forall evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("first tracer conclusion should be a rule application");
                };
                premises.clear();

                let error = emit_lean_from_litex_to_lean_ir(&statement_irs)
                    .expect_err("malformed arithmetic evidence must stop strict emission")
                    .trace_message();
                assert!(error.contains(
                    "expected 2 parameter requirements and 1 premises but received 2 and 0"
                ));
            },
        );
    }

    #[test]
    fn compile_to_lean_recursive_strategy_ir_preserves_typed_tree_and_compiles() {
        run_with_large_stack(
            "compile_to_lean_recursive_strategy_ir_preserves_typed_tree_and_compiles",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit");
                let source = fs::read_to_string(&path).unwrap();
                let statement_irs = test_litex_to_lean_ir(&source, "recursive-strategy-ir");
                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction {
                    inferred_premises,
                    conclusions,
                    ..
                } = &forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                assert_eq!(inferred_premises.len(), 4);
                assert!(inferred_premises.iter().all(|premise| matches!(
                    &premise.proof,
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::Builtin(
                            LitexToLeanBuiltinRuleIr::PositiveRealMembership
                        ),
                        ..
                    }
                )));
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::Arithmetic(
                            LitexToLeanArithmeticBuiltinRuleIr::AddPositiveLeftStrict,
                        )),
                    premises: outer_premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("outer strategy should lower to typed strict-addition evidence");
                };
                assert_eq!(outer_premises.len(), 2);

                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                    parameter_requirements,
                    premises,
                } = underlying_test_proof(&outer_premises[0].proof)
                else {
                    panic!("left strategy child should use its registered addition rule");
                };
                assert_eq!(application.rule_id.as_str(), "order.add_positive");
                assert_eq!(parameter_requirements.len(), 2);
                assert_eq!(premises.len(), 2);
                for requirement in parameter_requirements {
                    assert!(matches!(
                        underlying_test_proof(&requirement.proof),
                        LitexToLeanFactProofIr::RuleApplication {
                            rule: LitexToLeanProofRuleIr::Builtin(
                                LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection
                            ),
                            premises,
                            ..
                        } if premises.len() == 1
                            && matches!(
                                underlying_test_proof(&premises[0].proof),
                                LitexToLeanFactProofIr::KnownFactCitation { .. }
                            )
                    ));
                }

                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::Arithmetic(
                            LitexToLeanArithmeticBuiltinRuleIr::AddNonnegative,
                        )),
                    premises: weak_premises,
                    ..
                } = underlying_test_proof(&outer_premises[1].proof)
                else {
                    panic!("right strategy should lower to typed nonnegative-addition evidence");
                };
                assert_eq!(weak_premises.len(), 2);
                for premise in weak_premises {
                    assert!(matches!(
                        underlying_test_proof(&premise.proof),
                        LitexToLeanFactProofIr::RuleApplication {
                            rule: LitexToLeanProofRuleIr::RegisteredRule(application),
                            premises,
                            ..
                        } if application.rule_id.as_str() == "order.less_equal_of_less"
                            && premises.len() == 1
                            && matches!(
                                underlying_test_proof(&premises[0].proof),
                                LitexToLeanFactProofIr::KnownFactCitation { .. }
                            )
                    ));
                }

                let output = emit_lean_from_litex_to_lean_ir(&statement_irs).unwrap();
                assert!(!output.contains("_root_.Litex.BuiltinRules.carrier_r_pos_in_r"));
                assert!(output.contains("_root_.Litex.BuiltinRules.order_add_positive"));
                assert!(output.contains("_root_.Litex.BuiltinRules.order_less_equal_of_less"));
                assert!(output.contains("linarith only"), "{output}");
                assert!(!output.contains("OtherUnsupported"), "{output}");
                assert!(!output.contains("axiom"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_standard_set_membership_projection_is_typed_and_checked() {
        run_with_large_stack(
            "compile_to_lean_standard_set_membership_projection_is_typed_and_checked",
            || {
                let source = r#"
forall n N:
    n $in Z

forall z Z:
    z $in Q

forall q Q:
    q $in R

forall r R:
    r $in C

forall q Q+:
    q $in R+

forall z Z*:
    z $in C*

forall n N+:
    n $in C*

forall z Z-:
    z $in C*
"#;
                let statement_irs = test_litex_to_lean_ir(source, "standard-set-projection");
                assert_eq!(statement_irs.len(), 8);
                for statement in &statement_irs {
                    let LitexToLeanStatementIr::Fact(forall) = statement else {
                        panic!("each projection tracer must be a stored forall fact");
                    };
                    let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                        &forall.fact.proof
                    else {
                        panic!("each projection tracer must retain forall evidence");
                    };
                    assert_eq!(conclusions.len(), 1);
                    let LitexToLeanFactProofIr::RuleApplication {
                        rule:
                            LitexToLeanProofRuleIr::Builtin(
                                LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection,
                            ),
                        parameter_requirements,
                        premises,
                    } = underlying_test_proof(&conclusions[0].proof)
                    else {
                        panic!("projection conclusion must retain its typed builtin certificate");
                    };
                    assert!(parameter_requirements.is_empty());
                    assert_eq!(premises.len(), 1);
                    assert!(matches!(
                        underlying_test_proof(&premises[0].proof),
                        LitexToLeanFactProofIr::KnownFactCitation { .. }
                    ));
                }

                let output = emit_lean_from_litex_to_lean_ir(&statement_irs).unwrap();
                assert!(
                    output.contains("(n : ℤ) ∈ Litex.StandardSets.Z"),
                    "{output}"
                );
                assert!(
                    output.contains("(z : ℚ) ∈ Litex.StandardSets.Q"),
                    "{output}"
                );
                assert!(
                    output.contains("(q : ℝ) ∈ Litex.StandardSets.R"),
                    "{output}"
                );
                assert!(
                    output.contains("(r : ℂ) ∈ Litex.StandardSets.C"),
                    "{output}"
                );
                assert!(
                    output.contains("(q : ℝ) ∈ Litex.StandardSets.RPos"),
                    "{output}"
                );
                assert!(
                    output.contains("(z : ℂ) ∈ Litex.StandardSets.CStar"),
                    "{output}"
                );
                assert!(output.contains("exact_mod_cast"), "{output}");
                assert!(output.contains("ne_of_gt"), "{output}");
                assert!(output.contains("ne_of_lt"), "{output}");
                assert!(!output.contains("_root_.Litex.BuiltinRules.carrier_"));
                assert!(!output.contains("OtherUnsupported"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn compile_to_lean_standard_set_membership_projection_rejects_malformed_certificate() {
        run_with_large_stack(
            "compile_to_lean_standard_set_membership_projection_rejects_malformed_certificate",
            || {
                let mut statement_irs = test_litex_to_lean_ir(
                    "forall n N:\n    n $in Z\n",
                    "standard-set-projection-malformed",
                );
                let LitexToLeanStatementIr::Fact(forall) = &mut statement_irs[0] else {
                    panic!("tracer must produce a stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer must retain forall evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("projection conclusion must be a rule application");
                };
                premises.clear();

                let error = emit_lean_from_litex_to_lean_ir(&statement_irs)
                    .expect_err("malformed projection evidence must stop strict emission")
                    .trace_message();
                assert!(
                    error.contains("expected 1 premise but received 0"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_direct_cross_carrier_standard_subset_remains_unsupported() {
        run_with_large_stack(
            "compile_to_lean_direct_cross_carrier_standard_subset_remains_unsupported",
            || {
                let error =
                    compile_to_lean_from_source("N $subset Z\n", "standard-set-subset-boundary")
                        .expect_err("direct cross-carrier subset semantics remain undecided")
                        .trace_message();
                assert!(error.contains("no checked backend"), "{error}");
                assert!(error.contains("standard_set_subset"), "{error}");
            },
        );
    }

    #[test]
    fn compile_to_lean_recursive_strategy_ir_rejects_malformed_certificate() {
        run_with_large_stack(
            "compile_to_lean_recursive_strategy_ir_rejects_malformed_certificate",
            || {
                let source = include_str!(
                    "../../examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit"
                );
                let mut statement_irs =
                    test_litex_to_lean_ir(source, "recursive-strategy-malformed");
                let LitexToLeanStatementIr::Fact(forall) = &mut statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication { rule, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("outer strategy should be a rule application");
                };
                *rule = LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::Arithmetic(
                    LitexToLeanArithmeticBuiltinRuleIr::AddPositiveRightStrict,
                ));

                let error = emit_lean_from_litex_to_lean_ir(&statement_irs)
                    .expect_err("a strategy certificate with the wrong premise order must fail")
                    .trace_message();
                assert!(error.contains("premise 1 expected WeakOrder"), "{error}");
            },
        );
    }

    #[test]
    fn compile_to_lean_non_additive_structural_strategy_remains_explicitly_unsupported() {
        run_with_large_stack(
            "compile_to_lean_non_additive_structural_strategy_remains_explicitly_unsupported",
            || {
                let source = r#"
forall x, y R:
    x^2 < y^2
    =>:
        abs(x) < abs(y)
"#;
                let error = compile_to_lean_from_source(source, "unsupported-structural-strategy")
                    .expect_err("a label-only structural strategy must remain unsupported")
                    .trace_message();
                assert!(error.contains("numeric-order strategy"), "{error}");
                assert!(error.contains("no checked backend"), "{error}");
            },
        );
    }

    #[test]
    fn closed_rational_builtin_is_emitted_from_ir() {
        run_with_large_stack("closed_rational_builtin_is_emitted_from_ir", || {
            let output =
                compile_to_lean_from_source("1 / 2 / 3 / 4 = 1 / 24", "closed-ir").unwrap();

            assert!(output.contains("theorem fact1"));
            assert!(output.contains(
                "-- native proof view, left fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))"
            ));
            assert!(output.contains("norm_num"));
            assert!(!output.contains("sorry"));
        });
    }

    #[test]
    fn native_standard_domain_membership_keeps_a_bare_numeral() {
        let output =
            compile_to_lean_from_source("2 $in R\n", "native-standard-membership").unwrap();
        assert!(
            output.contains("theorem fact") && output.contains(": 2 ∈ Litex.StandardSets.R := by"),
            "{output}"
        );
        assert!(!output.contains("LitexSet"), "{output}");
        assert!(!output.contains("litexR"), "{output}");
        assert!(!output.contains("LitexAddEq"), "{output}");
        assert!(
            !output.contains(": 2 ∈ (Set.univ : Set ℝ) := by"),
            "{output}"
        );
    }

    #[test]
    fn compact_standard_numeric_subsets_use_native_mathlib_sets() {
        let source = r#"
forall n N+:
    n $in N+

Z+ = N+

forall q Q+:
    q $in Q+

forall r R+:
    r $in R+

forall z Z-:
    z $in Z-

forall q Q-:
    q $in Q-

forall r R-:
    r $in R-

forall z Z*:
    z $in Z*

forall q Q*:
    q $in Q*

forall r R*:
    r $in R*

forall c C*:
    c $in C*
"#;
        let output =
            compile_to_lean_from_source(source, "compact-standard-numeric-subsets").unwrap();

        for expected in [
            "∀ (n : ℕ) (litex_param_fact_1 : n ∈ Litex.StandardSets.NPos), n ∈ Litex.StandardSets.NPos",
            "Litex.StandardSets.NPos = Litex.StandardSets.NPos",
            "∀ (q : ℚ) (litex_param_fact_1 : q ∈ Litex.StandardSets.QPos), q ∈ Litex.StandardSets.QPos",
            "∀ (r : ℝ) (litex_param_fact_1 : r ∈ Litex.StandardSets.RPos), r ∈ Litex.StandardSets.RPos",
            "∀ (z : ℤ) (litex_param_fact_1 : z ∈ Litex.StandardSets.ZNeg), z ∈ Litex.StandardSets.ZNeg",
            "∀ (q : ℚ) (litex_param_fact_1 : q ∈ Litex.StandardSets.QNeg), q ∈ Litex.StandardSets.QNeg",
            "∀ (r : ℝ) (litex_param_fact_1 : r ∈ Litex.StandardSets.RNeg), r ∈ Litex.StandardSets.RNeg",
            "∀ (z : ℤ) (litex_param_fact_1 : z ∈ Litex.StandardSets.ZStar), z ∈ Litex.StandardSets.ZStar",
            "∀ (q : ℚ) (litex_param_fact_1 : q ∈ Litex.StandardSets.QStar), q ∈ Litex.StandardSets.QStar",
            "∀ (r : ℝ) (litex_param_fact_1 : r ∈ Litex.StandardSets.RStar), r ∈ Litex.StandardSets.RStar",
            "∀ (c : ℂ) (litex_param_fact_1 : c ∈ Litex.StandardSets.CStar), c ∈ Litex.StandardSets.CStar",
        ] {
            assert!(
                output.contains(expected),
                "missing `{expected}` in:\n{output}"
            );
        }
        assert!(!output.contains("\naxiom fact"), "{output}");
        assert!(!output.contains("sorry"), "{output}");

        let positive_integer_alias =
            compile_to_lean_from_source("forall z Z+:\n    z $in Z+\n", "positive-integer-alias")
                .unwrap();
        assert!(
            positive_integer_alias.contains(
                "∀ (z : ℕ) (litex_param_fact_1 : z ∈ Litex.StandardSets.NPos), z ∈ Litex.StandardSets.NPos"
            ),
            "{positive_integer_alias}"
        );
    }

    #[test]
    fn closed_compact_numeric_memberships_emit_checked_norm_num_proofs() {
        let source = r#"
1 $in N+
1 $in Q+
2 $in R+
0 - 1 $in Z-
0 - 1 $in Q-
0 - 1 $in R-
1 $in Z*
1 $in Q*
1 $in R*
1 $in C*
not 0 $in N+
not 0 $in Q+
not 0 $in R+
not 0 $in Z-
not 0 $in Q-
not 0 $in R-
not 0 $in Z*
not 0 $in Q*
not 0 $in R*
not 0 $in C*
"#;
        let output =
            compile_to_lean_from_source(source, "closed-compact-numeric-memberships").unwrap();

        for expected in [
            "1 ∈ Litex.StandardSets.NPos",
            "1 ∈ Litex.StandardSets.QPos",
            "2 ∈ Litex.StandardSets.RPos",
            "(0 - 1) ∈ Litex.StandardSets.ZNeg",
            "(0 - 1) ∈ Litex.StandardSets.QNeg",
            "(0 - 1) ∈ Litex.StandardSets.RNeg",
            "1 ∈ Litex.StandardSets.ZStar",
            "1 ∈ Litex.StandardSets.QStar",
            "1 ∈ Litex.StandardSets.RStar",
            "1 ∈ Litex.StandardSets.CStar",
            "0 ∉ Litex.StandardSets.NPos",
            "0 ∉ Litex.StandardSets.QPos",
            "0 ∉ Litex.StandardSets.RPos",
            "0 ∉ Litex.StandardSets.ZNeg",
            "0 ∉ Litex.StandardSets.QNeg",
            "0 ∉ Litex.StandardSets.RNeg",
            "0 ∉ Litex.StandardSets.ZStar",
            "0 ∉ Litex.StandardSets.QStar",
            "0 ∉ Litex.StandardSets.RStar",
            "0 ∉ Litex.StandardSets.CStar",
        ] {
            assert!(
                output.contains(expected),
                "missing `{expected}` in:\n{output}"
            );
        }
        assert!(output.matches("by\n  norm_num").count() >= 20, "{output}");
        assert!(!output.contains("\naxiom fact"), "{output}");
        assert!(!output.contains("sorry"), "{output}");
    }

    #[test]
    fn builtin_predicates_use_native_props_and_selected_checked_rules() {
        let source = r#"
$prime(53)
not $prime(54)
$coprime(14, 25)
not $coprime(14, 21)

forall A, B set:
    A $subset B
    =>:
        B $superset A

forall A, B set:
    not A $subset B
    =>:
        not B $superset A

forall A, B set:
    A $proper_subset B
    =>:
        A $proper_subset B

forall A, B set:
    not A $proper_subset B
    =>:
        not A $proper_subset B

forall A, B set:
    A $proper_superset B
    =>:
        A $proper_superset B

forall A, B set:
    not A $proper_superset B
    =>:
        not A $proper_superset B

forall a, b R:
    not a < b
    =>:
        not a < b

forall a, b R:
    not a <= b
    =>:
        not a <= b

forall a, b R:
    not a > b
    =>:
        not a > b

forall a, b R:
    not a >= b
    =>:
        not a >= b
"#;
        let output = compile_to_lean_from_source(source, "builtin-predicates").unwrap();

        for expected in [
            "Nat.Prime 53",
            "¬ Nat.Prime 54",
            "Nat.Coprime 14 25",
            "¬ Nat.Coprime 14 21",
            "(litex_domain_fact_1 : A ⊆ B), A ⊆ B",
            "(litex_domain_fact_1 : ¬ (A ⊆ B)), ¬ (A ⊆ B)",
            "(litex_domain_fact_1 : (A ⊆ B) ∧ A ≠ B), (A ⊆ B) ∧ A ≠ B",
            "(litex_domain_fact_1 : ¬ (A ⊆ B) ∨ A = B), ¬ (A ⊆ B) ∨ A = B",
            "(litex_domain_fact_1 : (B ⊆ A) ∧ A ≠ B), (B ⊆ A) ∧ A ≠ B",
            "(litex_domain_fact_1 : ¬ (B ⊆ A) ∨ A = B), ¬ (B ⊆ A) ∨ A = B",
            "(litex_domain_fact_1 : ¬ (a < b)), ¬ (a < b)",
            "(litex_domain_fact_1 : ¬ (a ≤ b)), ¬ (a ≤ b)",
            "(litex_domain_fact_1 : ¬ (a > b)), ¬ (a > b)",
            "(litex_domain_fact_1 : ¬ (a ≥ b)), ¬ (a ≥ b)",
        ] {
            assert!(
                output.contains(expected),
                "missing `{expected}` in:\n{output}"
            );
        }
        assert!(output.matches("norm_num").count() >= 4, "{output}");
        assert!(!output.contains("$prime"), "{output}");
        assert!(!output.contains("$coprime"), "{output}");
        assert!(!output.contains("$proper_"), "{output}");
        assert!(!output.contains("\naxiom fact"), "{output}");
        assert!(!output.contains("sorry"), "{output}");
    }

    #[test]
    fn set_relation_duality_ir_retains_its_checked_reversed_premise() {
        let source = r#"
forall A, B set:
    A $superset B
    =>:
        B $subset A

forall A, B set:
    A $subset B
    =>:
        B $superset A

forall A, B set:
    not A $superset B
    =>:
        not B $subset A

forall A, B set:
    not A $subset B
    =>:
        not B $superset A
"#;
        let mut statement_irs = test_litex_to_lean_ir(source, "set-relation-duality-ir");
        let expected_rules = [
            LitexToLeanSetRelationDualityBuiltinRuleIr::SubsetFromSuperset,
            LitexToLeanSetRelationDualityBuiltinRuleIr::SupersetFromSubset,
            LitexToLeanSetRelationDualityBuiltinRuleIr::NotSubsetFromNotSuperset,
            LitexToLeanSetRelationDualityBuiltinRuleIr::NotSupersetFromNotSubset,
        ];
        for (statement, expected_rule) in statement_irs.iter_mut().zip(expected_rules) {
            let LitexToLeanStatementIr::Fact(forall) = statement else {
                panic!("duality tracer should produce stored forall facts");
            };
            let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                &mut forall.fact.proof
            else {
                panic!("duality tracer should retain forall-introduction evidence");
            };
            let LitexToLeanFactProofIr::RuleApplication {
                rule:
                    LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::SetRelationDuality(rule)),
                premises,
                ..
            } = underlying_test_proof_mut(&mut conclusions[0].proof)
            else {
                panic!("duality tracer should retain typed set-relation evidence");
            };
            assert_eq!(*rule, expected_rule);
            assert_eq!(premises.len(), 1);
        }

        let LitexToLeanStatementIr::Fact(forall) = &mut statement_irs[1] else {
            unreachable!();
        };
        let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } = &mut forall.fact.proof
        else {
            unreachable!();
        };
        let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
            underlying_test_proof_mut(&mut conclusions[0].proof)
        else {
            unreachable!();
        };
        premises.clear();

        let error = emit_lean_from_litex_to_lean_ir(&statement_irs)
            .expect_err("duality evidence without its checked premise must fail")
            .trace_message();
        assert!(
            error.contains("set-relation duality evidence expected 1 premise but received 0"),
            "{error}"
        );
    }

    #[test]
    fn unordered_complex_positive_subset_remains_rejected() {
        let result =
            compile_to_lean_from_source("1 $in C+\n", "unsupported-complex-positive-subset");
        assert!(
            result.is_err(),
            "C+ must not be invented as an ordered complex subset"
        );
    }

    #[test]
    fn unconstrained_reflexive_numeral_keeps_lean_defaulting_local() {
        let output = compile_to_lean_from_source("2 = 2\n", "bare-reflexive-numeral").unwrap();

        assert!(output.contains(": 2 = 2 := by"), "{output}");
        assert!(!output.contains("(2 : ℚ)"), "{output}");
        assert!(!output.contains("(2 : ℝ)"), "{output}");
    }

    #[test]
    fn trusted_closed_division_does_not_choose_a_carrier() {
        let error = compile_to_lean_from_source(
            "trust 1 / 2 = 1 / 2\n",
            "underconstrained-trusted-division",
        )
        .expect_err("trust must not choose a numeric carrier")
        .trace_message();

        assert!(error.contains("no checked target carrier"), "{error}");
    }

    #[test]
    fn native_bounded_binders_preserve_membership_and_cross_domain_expectation() {
        let source = r#"
trust forall x R:
    x $in R

trust forall z Z:
    z / 2 $in Q
"#;
        let output = compile_to_lean_from_source(source, "native-bounded-binders").unwrap();
        assert!(
            output.contains(
                "∀ (x : ℝ) (litex_param_fact_1 : x ∈ Litex.StandardSets.R), x ∈ Litex.StandardSets.R"
            ),
            "{output}"
        );
        assert!(
            output.contains(
                "∀ (z : ℤ) (litex_param_fact_1 : z ∈ Litex.StandardSets.Z), (z / 2 : ℚ) ∈ Litex.StandardSets.Q"
            ),
            "{output}"
        );
        assert!(!output.contains("(z : ℚ)"), "{output}");
    }

    #[test]
    fn named_theorem_preserves_source_name_and_local_proof_scope() {
        run_with_large_stack(
            "named_theorem_preserves_source_name_and_local_proof_scope",
            || {
                let source = r#"thm real_reflexivity:
    ? forall x R:
        x = x
    x = x
"#;
                let ir = test_litex_to_lean_ir(source, "named-theorem-ir.lit");
                let [LitexToLeanStatementIr::NamedTheorem(theorem)] = ir.as_slice() else {
                    panic!("source theorem should lower to named-theorem IR");
                };
                assert_eq!(theorem.name, "real_reflexivity");
                assert_eq!(theorem.proof_steps.len(), 1);
                assert!(theorem.theorem.fact_id.is_some());
                assert!(theorem.stored_projections.is_empty());
                let LitexToLeanFactProofIr::ForallIntroduction {
                    parameter_premises,
                    conclusions,
                    ..
                } = &theorem.theorem.proof
                else {
                    panic!("named theorem should retain forall-introduction evidence");
                };
                assert_eq!(parameter_premises.len(), 1);
                assert_eq!(conclusions.len(), 1);

                let primary_id = theorem.theorem.fact_id.unwrap();
                let output = emit_lean_from_litex_to_lean_ir(&ir).unwrap();
                assert!(
                    output.contains("theorem real_reflexivity : ∀ (x : ℝ)"),
                    "{output}"
                );
                assert!(output.contains("have proof_fact_"), "{output}");
                assert!(
                    !output.contains(&format!("theorem {} :", lean_stored_fact_name(primary_id))),
                    "{output}"
                );
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn named_theorem_preserves_domain_premises_and_ordered_conclusions() {
        run_with_large_stack(
            "named_theorem_preserves_domain_premises_and_ordered_conclusions",
            || {
                let source = r#"thm nonzero_self_and_reflexive:
    ? forall x R:
        x != 0
        =>:
            x != 0
            x = x
"#;
                let ir = test_litex_to_lean_ir(source, "named-theorem-conjunction.lit");
                let [LitexToLeanStatementIr::NamedTheorem(theorem)] = ir.as_slice() else {
                    unreachable!();
                };
                let LitexToLeanFactProofIr::ForallIntroduction {
                    premises,
                    conclusions,
                    ..
                } = &theorem.theorem.proof
                else {
                    unreachable!();
                };
                assert_eq!(premises.len(), 1);
                assert_eq!(conclusions.len(), 2);

                let output = emit_lean_from_litex_to_lean_ir(&ir).unwrap();
                assert!(output.contains("theorem nonzero_self_and_reflexive"));
                assert!(output.contains("(litex_domain_fact_1 : x ≠ 0)"));
                assert!(output.contains("(x ≠ 0 ∧ x = x)"), "{output}");
                assert!(output.contains("exact ⟨proof_fact_"), "{output}");
            },
        );
    }

    #[test]
    fn malformed_named_theorem_evidence_fails_transactionally() {
        run_with_large_stack(
            "malformed_named_theorem_evidence_fails_transactionally",
            || {
                let source = r#"thm real_reflexivity:
    ? forall x R:
        x = x
    x = x
"#;
                let mut missing_conclusion = test_litex_to_lean_ir(source, "named-theorem-bad.lit");
                let [LitexToLeanStatementIr::NamedTheorem(theorem)] =
                    missing_conclusion.as_mut_slice()
                else {
                    unreachable!();
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut theorem.theorem.proof
                else {
                    unreachable!();
                };
                conclusions.clear();
                let report = emit_lean_from_litex_to_lean_ir_with_report(&missing_conclusion);
                assert!(!report.is_complete());
                assert!(!report.lean_code.contains("theorem real_reflexivity"));
                assert!(report.unsupported[0]
                    .reason
                    .contains("source has 1 conclusions"));

                let mut reordered_step =
                    test_litex_to_lean_ir(source, "named-theorem-step-order.lit");
                let [LitexToLeanStatementIr::NamedTheorem(theorem)] = reordered_step.as_mut_slice()
                else {
                    unreachable!();
                };
                theorem.proof_steps[0].position = 2;
                let error = emit_lean_from_litex_to_lean_ir(&reordered_step)
                    .expect_err("out-of-order theorem proof evidence must fail")
                    .trace_message();
                assert!(
                    error.contains("proof steps are out of verifier order"),
                    "{error}"
                );

                let mut unsupported_step =
                    test_litex_to_lean_ir(source, "named-theorem-local-boundary.lit");
                let [LitexToLeanStatementIr::NamedTheorem(theorem)] =
                    unsupported_step.as_mut_slice()
                else {
                    unreachable!();
                };
                theorem.proof_steps[0].statement =
                    LitexToLeanStatementIr::Trust(LitexToLeanTrustIr {
                        facts: Vec::new(),
                        inferred_facts: Vec::new(),
                    });
                let report = emit_lean_from_litex_to_lean_ir_with_report(&unsupported_step);
                assert!(!report.is_complete());
                assert!(!report.lean_code.contains("theorem real_reflexivity"));
                assert!(report.unsupported[0]
                    .reason
                    .contains("does not support local statement"));
            },
        );
    }

    #[test]
    fn named_theorem_target_name_collision_fails_closed() {
        run_with_large_stack("named_theorem_target_name_collision_fails_closed", || {
            let source = r#"trust 1 = 1

thm collision_probe:
    ? forall x R:
        x = x
"#;
            let mut ir = test_litex_to_lean_ir(source, "named-theorem-name-collision.lit");
            let LitexToLeanStatementIr::Trust(trusted) = &ir[0] else {
                unreachable!();
            };
            let collision_name =
                lean_stored_fact_name(trusted.facts[0].fact_id.expect("trusted fact ID"));
            let LitexToLeanStatementIr::NamedTheorem(theorem) = &mut ir[1] else {
                unreachable!();
            };
            theorem.name = collision_name.clone();
            let report = emit_lean_from_litex_to_lean_ir_with_report(&ir);
            assert!(!report.is_complete());
            assert!(
                report
                    .lean_code
                    .contains(&format!("axiom {collision_name}")),
                "{}",
                report.lean_code
            );
            assert!(!report
                .lean_code
                .contains(&format!("theorem {collision_name} : ∀")));
            assert!(report.unsupported[0].reason.contains(&format!(
                "declaration name `{collision_name}` is already reserved"
            )));
        });
    }

    #[test]
    fn axiom_and_by_theorem_steps_remain_explicit_named_theorem_boundaries() {
        run_with_large_stack(
            "axiom_and_by_theorem_steps_remain_explicit_named_theorem_boundaries",
            || {
                let axiom = compile_to_lean_from_source_with_report(
                    "axiom assumed_reflexivity:\n    ? forall x R:\n        x = x\n",
                    "named-theorem-axiom-boundary.lit",
                )
                .unwrap();
                assert!(!axiom.is_complete());
                assert_eq!(axiom.unsupported.len(), 1);
                assert!(axiom.unsupported[0]
                    .reason
                    .contains("does not compile explicit `axiom`"));
                assert!(!axiom.lean_code.contains("\naxiom assumed_reflexivity :"));

                let by_theorem = compile_to_lean_from_source_with_report(
                    r#"thm base_reflexivity:
    ? forall x R:
        x = x

thm replay_reflexivity:
    ? forall x R:
        x = x
    by thm base_reflexivity(x)
"#,
                    "named-theorem-by-thm-boundary.lit",
                )
                .unwrap();
                assert!(!by_theorem.is_complete());
                assert_eq!(by_theorem.unsupported.len(), 1);
                assert_eq!(by_theorem.unsupported[0].statement_index, 2);
                assert!(by_theorem.lean_code.contains("theorem base_reflexivity"));
                assert!(!by_theorem.lean_code.contains("theorem replay_reflexivity"));
                assert!(by_theorem.unsupported[0]
                    .reason
                    .contains("does not support statement kind"));
            },
        );
    }

    #[test]
    fn finite_set_index_builtin_theorem_remains_a_fail_closed_compiler_boundary() {
        run_with_large_stack(
            "finite_set_index_builtin_theorem_remains_a_fail_closed_compiler_boundary",
            || {
                let result = compile_to_lean_from_source(
                    "by thm finite_set_has_bijective_index({})\n",
                    "finite-set-index-builtin-theorem-boundary.lit",
                );
                assert!(
                    result.is_err(),
                    "the compiler must reject this kernel-only existential instead of emitting Lean"
                );
            },
        );
    }

    #[test]
    fn compile_to_lean_mixed_projected_forall() {
        run_with_large_stack("compile_to_lean_mixed_projected_forall", || {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_mixed_projected_forall.lit");
            let source = fs::read_to_string(&path).unwrap();
            let ir = test_litex_to_lean_ir(&source, &path.to_string_lossy());
            let [LitexToLeanStatementIr::ProjectedForall(projected)] = ir.as_slice() else {
                panic!("mixed forall must retain its runtime-stored projections");
            };
            assert_eq!(projected.facts.len(), 2);
            assert!(projected.facts.iter().all(|fact| fact.fact_id.is_some()));
            assert!(projected.facts.iter().all(|fact| matches!(
                &fact.proof,
                LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. }
                    if conclusions.len() == 1
            )));

            let output = compile_to_lean_from_source(&source, &path.to_string_lossy()).unwrap();
            assert!(
                output.contains("∀ (a : ℝ) (litex_param_fact_1 : a ∈ Litex.StandardSets.R), a = a"),
                "{output}"
            );
            assert!(output.contains("∀ (b : Set"), "{output}");
            assert_eq!(output.matches("theorem fact").count(), 2, "{output}");
            assert!(!output.contains("a = b"), "{output}");

            let reused = format!(
                "{}\n\nforall a R:\n    a = a\n\nforall b set:\n    b = b\n",
                source
            );
            let reused_output =
                compile_to_lean_from_source(&reused, "projected-forall-reuse").unwrap();
            assert_eq!(reused_output.matches("theorem fact").count(), 2);

            assert!(compile_to_lean_from_source(
                "forall a R, b set:\n    a = b\n",
                "mixed-carrier-equality-boundary"
            )
            .is_err());
        });
    }

    #[test]
    fn compile_to_lean_multiple_conclusion_forall_builds_checked_conjunction() {
        let source = "forall a, b R:\n    a + b = a + b\n    a * b = a * b\n";
        let output = compile_to_lean_from_source(source, "multiple-forall-conclusions").unwrap();
        assert!(
            output.contains("(a + b) = (a + b) ∧ (a * b) = (a * b)"),
            "{output}"
        );
        assert!(output.contains("exact ⟨proof_fact_"), "{output}");

        let mut ir = test_litex_to_lean_ir(source, "malformed-multiple-forall-conclusions");
        let [LitexToLeanStatementIr::Fact(forall)] = ir.as_mut_slice() else {
            panic!("fully covered forall should be stored as one fact");
        };
        let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } = &mut forall.fact.proof
        else {
            panic!("forall should retain introduction evidence");
        };
        conclusions.pop();
        let error = emit_lean_from_litex_to_lean_ir(&ir)
            .expect_err("missing conjunction evidence must fail")
            .trace_message();
        assert!(error.contains("source has 2 conclusions"), "{error}");
    }

    #[test]
    fn temporary_forall_premise_is_emitted_as_local_exact() {
        run_with_large_stack("temporary_forall_premise_is_emitted_as_local_exact", || {
            let output = compile_to_lean_from_source(
                "forall x R:\n    x != 0\n    =>:\n        x != 0",
                "temporary-local-fact",
            )
            .unwrap();

            assert!(output.contains("intro x litex_param_fact_1 litex_domain_fact_1"));
            assert!(output.contains("exact litex_domain_fact_1"));
            assert!(!output.contains("axiom"));
            assert!(!output.contains("sorry"));
        });
    }

    #[test]
    fn generated_proof_fact_coordinates_distinguish_proof_spaces() {
        run_with_large_stack(
            "generated_proof_fact_coordinates_distinguish_proof_spaces",
            || {
                let source = r#"
abstract_prop p(x)
abstract_prop q(x)

forall x R:
    $p(x)
    =>:
        $p(x)

forall y R:
    $q(y)
    =>:
        $q(y)
"#;
                let output = compile_to_lean_from_source(source, "local-proof-spaces").unwrap();

                assert_eq!(output.matches("\ntheorem fact").count(), 2);
                assert!(output.contains("intro x litex_param_fact_1 litex_domain_fact_1"));
                assert!(output.contains("intro y litex_param_fact_1 litex_domain_fact_1"));
                assert_eq!(output.matches("exact litex_domain_fact_1").count(), 2);
            },
        );
    }

    #[test]
    fn nested_proof_space_inherits_outer_facts_and_resets_its_proof_fact_index() {
        let mut emitter = LeanEmitter::new(None);
        let root = LeanProofContext::default();
        let mut outer = root.new_proof_space();
        assert_eq!(emitter.next_proof_fact_name(&mut outer), "proof_fact_1_1");
        assert_eq!(emitter.next_proof_fact_name(&mut outer), "proof_fact_1_2");

        outer
            .proof_fact_names
            .insert(FactId::new(42), "proof_fact_1_2".to_string());
        let mut nested = outer.new_proof_space();
        assert_eq!(
            nested.proof_fact_names.get(&FactId::new(42)),
            Some(&"proof_fact_1_2".to_string())
        );
        assert_eq!(emitter.next_proof_fact_name(&mut nested), "proof_fact_2_1");
        assert_eq!(emitter.next_proof_fact_name(&mut outer), "proof_fact_1_3");
    }

    #[test]
    fn local_atomic_fact_is_transported_by_recorded_equality_rule() {
        run_with_large_stack(
            "local_atomic_fact_is_transported_by_recorded_equality_rule",
            || {
                let source = r#"
abstract_prop p(a)

forall a, b set:
    $p(a)
    a = b
    =>:
        $p(b)
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("equality-transport-ir");
                runtime.replace_litex_to_lean_ir_mode(true);
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut statement_irs = Vec::new();
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    if statement_irs.len() == 1 {
                        let success = result.factual_success().expect("forall success");
                        let VerifiedByResult::ForallProof(forall_proof) = &success.verified_by
                        else {
                            panic!("second statement should retain its forall proof");
                        };
                        let conclusion = forall_proof.proves[0]
                            .result
                            .factual_success()
                            .expect("forall conclusion success");
                        let VerifiedByResult::Fact(citation) =
                            underlying_test_verified_by(&conclusion.verified_by)
                        else {
                            panic!("transported conclusion should cite a known fact");
                        };
                        let transport = citation
                            .equality_transport
                            .as_ref()
                            .expect("transport evidence should be captured by the verifier");
                        assert!(citation.source_fact_id.is_some());
                        assert_eq!(transport.steps.len(), 1);
                        assert!(transport.steps[0].equality_fact_id.is_some());
                    }
                    statement_irs.push(result.litex_to_lean_ir().unwrap().clone());
                }

                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction {
                    premises: local_premises,
                    conclusions,
                    ..
                } = &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(rewrite),
                    premises: rewrite_premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("conclusion should retain equality-rewrite evidence");
                };
                assert_eq!(rewrite.steps.len(), 1);
                assert_eq!(rewrite_premises.len(), 2);
                assert_eq!(
                    rewrite.steps[0].direction,
                    LitexToLeanEqualityRewriteDirectionIr::Forward
                );
                assert!(rewrite_premises.iter().all(|premise| {
                    premise.fact_id.is_some_and(|fact_id| {
                        local_premises.iter().any(|local| local.fact_id == fact_id)
                    })
                }));

                let output =
                    compile_to_lean_from_source(source, "equality-transport-output").unwrap();
                assert!(output.contains(
                    "intro _ _ a b litex_domain_fact_1 litex_domain_fact_2\n  have proof_fact_1_1"
                ));
                assert!(output.contains("have proof_fact_1_1 : p a := litex_domain_fact_1"));
                assert!(output.contains("have proof_fact_1_2 : a = b := litex_domain_fact_2"));
                assert!(output.contains("have proof_fact_1_3 : p b := by"));
                assert!(output.contains("simpa only [proof_fact_1_2] using proof_fact_1_1"));
                assert!(output.contains("exact proof_fact_1_3"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn equality_transport_normalizes_reverse_and_repeated_edges() {
        run_with_large_stack(
            "equality_transport_normalizes_reverse_and_repeated_edges",
            || {
                let source = r#"
abstract_prop q(x)
abstract_prop related(x, y)

forall a, b, c set:
    $q(c)
    a = b
    b = c
    =>:
        $q(a)

forall a, b set:
    $related(a, b)
    a = b
    =>:
        $related(b, a)
"#;
                let output =
                    compile_to_lean_from_source(source, "multi-equality-transport").unwrap();

                assert!(output.contains("have proof_fact_1_1 : q c := litex_domain_fact_1"));
                assert!(output.contains("have proof_fact_1_4 : q a := by"));
                assert!(output
                    .contains("simpa only [proof_fact_1_2, proof_fact_1_3] using proof_fact_1_1"));
                let related_proof = output
                    .split("have proof_fact_2_1 : related a b")
                    .nth(1)
                    .expect("binary transport proof");
                assert_eq!(
                    related_proof
                        .split("simpa only")
                        .next()
                        .unwrap()
                        .matches("have proof_fact_2_2")
                        .count(),
                    1,
                    "one equality used at two argument positions should be emitted once"
                );
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn resolved_atomic_fact_citation_replays_equality_and_normalization() {
        run_with_large_stack(
            "resolved_atomic_fact_citation_replays_equality_and_normalization",
            || {
                let source = include_str!(
                    "../../examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit"
                );
                let statement_irs = test_litex_to_lean_ir(source, "resolved-atomic-fact-ir");
                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(rewrite),
                    premises: rewrite_premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("outer proof should replay the resolved equalities");
                };
                assert_eq!(rewrite.steps.len(), 2);
                assert_eq!(rewrite_premises.len(), 3);
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::Normalization {
                            kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                        },
                    premises: normalization_premises,
                    ..
                } = &rewrite_premises[0].proof
                else {
                    panic!("rewrite source should be produced by nested normalization");
                };
                assert_eq!(normalization_premises.len(), 1);
                assert!(matches!(
                    normalization_premises[0].proof,
                    LitexToLeanFactProofIr::KnownFactCitation { .. }
                ));

                let output = compile_to_lean_from_source(source, "resolved-atomic-fact").unwrap();

                assert!(
                    output.lines().any(|line| {
                        line.contains("have proof_fact_") && line.contains(": p (13 + 1 : ℝ) := by")
                    }),
                    "{output}"
                );
                assert!(
                    output.lines().any(|line| {
                        line.contains("have proof_fact_") && line.contains(": p (14 : ℝ)")
                    }),
                    "{output}"
                );
                assert!(!output.contains("p ((13 : ℕ) + 1)"), "{output}");
                assert!(
                    output.lines().any(|line| {
                        line.contains("convert proof_fact_") && line.contains(" using 1")
                    }),
                    "{output}"
                );
                assert!(
                    output.lines().any(|line| {
                        line.contains("have proof_fact_") && line.contains(": p (a + b) := by")
                    }),
                    "{output}"
                );
                assert!(
                    output.lines().any(|line| {
                        line.contains("simpa only [proof_fact_")
                            && line.contains(", proof_fact_")
                            && line.contains("] using proof_fact_")
                    }),
                    "{output}"
                );
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn resolved_atomic_fact_composes_citation_transport_with_transformations() {
        run_with_large_stack(
            "resolved_atomic_fact_composes_citation_transport_with_transformations",
            || {
                let source = r#"
abstract_prop p(x)

forall a, b R:
    a = 13
    b = 1
    14 = 15
    $p(15)
    =>:
        $p(a + b)
"#;
                let statement_irs =
                    test_litex_to_lean_ir(source, "composed-resolved-atomic-fact-ir");
                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(goal_rewrite),
                    premises: goal_rewrite_premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("outer proof should rewrite the normalized fact to the goal");
                };
                assert_eq!(goal_rewrite.steps.len(), 2);
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::Normalization { .. },
                    premises: normalization_premises,
                    ..
                } = &goal_rewrite_premises[0].proof
                else {
                    panic!("outer rewrite source should be produced by normalization");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(source_rewrite),
                    premises: source_rewrite_premises,
                    ..
                } = &normalization_premises[0].proof
                else {
                    panic!("normalization source should be transported from the cited fact");
                };
                assert_eq!(source_rewrite.steps.len(), 1);
                assert_eq!(source_rewrite_premises.len(), 2);

                let output =
                    compile_to_lean_from_source(source, "composed-resolved-atomic-fact").unwrap();
                assert!(output.contains(": p (a + b) := by"), "{output}");
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn nested_function_argument_resolution_compiles_through_native_function_ir() {
        run_with_large_stack(
            "nested_function_argument_resolution_compiles_through_native_function_ir",
            || {
                let source = r#"
abstract_prop p(x, y)

forall f fn(x R) R, a, b, c R:
    a = 13
    b = 1
    $p(f(14), c)
    =>:
        $p(f(a + b), c)
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("nested-resolved-atomic-fact");
                let (results, error) = run_source_code(source, &mut runtime);
                assert!(error.is_none());
                let success = results[1].factual_success().expect("forall success");
                let VerifiedByResult::ForallProof(forall_proof) = &success.verified_by else {
                    panic!("second statement should retain its forall proof");
                };
                let conclusion = forall_proof.proves[0]
                    .result
                    .factual_success()
                    .expect("forall conclusion success");
                let VerifiedByResult::Fact(citation) = conclusion.underlying_verified_by() else {
                    panic!("resolved conclusion should retain its source citation");
                };
                let transformation = citation
                    .fact_transformation
                    .as_ref()
                    .expect("nested resolution should retain replayable transformations");
                assert!(
                    transformation.source.to_string().contains("f(14)"),
                    "{}",
                    transformation.source
                );
                assert_eq!(transformation.steps.len(), 2);
                assert!(
                    transformation.steps[0]
                        .result
                        .to_string()
                        .contains("f(13 + 1)"),
                    "{}",
                    transformation.steps[0].result
                );
                assert!(matches!(
                    transformation.steps[0].rule,
                    FactTransformationRule::RationalNormalization
                ));
                assert!(
                    transformation.steps[1].result.to_string().contains("a +"),
                    "{}",
                    transformation.steps[1].result
                );
                let FactTransformationRule::EqualityRewrite(rewrite) =
                    &transformation.steps[1].rule
                else {
                    panic!("second transformation should be equality rewrite");
                };
                assert_eq!(rewrite.steps.len(), 2);
                assert!(rewrite
                    .steps
                    .iter()
                    .all(|step| step.equality_fact_id.is_some()));

                let lean = compile_to_lean_from_source(source, "nested-resolved-atomic-fact")
                    .expect("native function carriers now cross the Obj IR boundary");
                assert!(
                    lean.contains("Set ((x : ℝ) → ℝ)") && lean.contains("p (f (a + b)) c"),
                    "{lean}"
                );
                assert!(!lean.contains("sorry"), "{lean}");
            },
        );
    }

    #[test]
    fn compound_equality_transport_is_recorded_at_arbitrary_object_depth() {
        run_with_large_stack(
            "compound_equality_transport_is_recorded_at_arbitrary_object_depth",
            || {
                let source = r#"
abstract_prop p(x, y)

forall f fn(x R) R, a, b, c R:
    a + b = 14
    $p(f(14), c)
    =>:
        $p(f(a + b), c)
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("nested-compound-equality-transport");
                let (results, error) = run_source_code(source, &mut runtime);
                assert!(error.is_none());
                let success = results[1].factual_success().expect("forall success");
                let VerifiedByResult::ForallProof(forall_proof) = &success.verified_by else {
                    panic!("second statement should retain its forall proof");
                };
                let conclusion = forall_proof.proves[0]
                    .result
                    .factual_success()
                    .expect("forall conclusion success");
                let VerifiedByResult::Fact(citation) = conclusion.underlying_verified_by() else {
                    panic!("conclusion should retain its source citation");
                };
                let transport = citation
                    .equality_transport
                    .as_ref()
                    .expect("nested compound equality should retain transport evidence");
                assert_eq!(transport.steps.len(), 1);
                assert_eq!(transport.steps[0].from.to_string(), "14");
                assert!(
                    matches!(&transport.steps[0].to, Obj::Add(_)),
                    "{}",
                    transport.steps[0].to
                );
                assert!(
                    transport.steps[0].equality.to_string().ends_with("= 14"),
                    "{}",
                    transport.steps[0].equality
                );
                assert!(transport.steps[0].equality_fact_id.is_some());
                assert!(citation.fact_transformation.is_none());

                let lean =
                    compile_to_lean_from_source(source, "nested-compound-equality-transport")
                        .expect(
                            "native function objects should preserve nested equality transport",
                        );
                assert!(lean.contains("Set ((x : ℝ) → ℝ)"), "{lean}");
                assert!(lean.contains("p (f (a + b)) c"), "{lean}");
                assert!(
                    lean.lines().any(|line| {
                        line.contains("simpa only [proof_fact_")
                            && line.contains("] using proof_fact_")
                    }),
                    "{lean}"
                );
                assert!(!lean.contains("sorry"), "{lean}");
            },
        );
    }

    #[test]
    fn nested_compound_equality_transport_lowers_to_litex_to_lean_ir() {
        run_with_large_stack(
            "nested_compound_equality_transport_lowers_to_litex_to_lean_ir",
            || {
                let source = r#"
abstract_prop p(x, y)

forall a, b, c R:
    a + b = 14
    $p(abs(14), c)
    =>:
        $p(abs(a + b), c)
"#;
                let statement_irs =
                    test_litex_to_lean_ir(source, "nested-compound-equality-transport-ir");
                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(rewrite),
                    premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("nested compound equality should lower as equality rewrite");
                };
                assert_eq!(rewrite.steps.len(), 1);
                assert_eq!(premises.len(), 2);

                let output =
                    compile_to_lean_from_source(source, "nested-compound-equality-transport")
                        .unwrap();
                assert!(output.contains("simpa only ["), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn unresolved_nested_symbol_does_not_create_a_partial_transformation_proof() {
        run_with_large_stack(
            "unresolved_nested_symbol_does_not_create_a_partial_transformation_proof",
            || {
                let source = r#"
abstract_prop p(x)

forall a, b R:
    a = 13
    $p(14)
    =>:
        $p(a + b)
"#;
                let error = compile_to_lean_from_source(source, "partly-resolved-atomic-fact")
                    .expect_err("an unresolved b must leave the Litex goal unverified");
                let error_debug = format!("{error:?}");
                assert!(error_debug.contains("verification failed"), "{error_debug}");
            },
        );
    }

    #[test]
    fn resolved_defined_symbols_use_the_same_recursive_transformation_evidence() {
        run_with_large_stack(
            "resolved_defined_symbols_use_the_same_recursive_transformation_evidence",
            || {
                let source = r#"
abstract_prop p(x)

have a R = 13

have b R = 1

trust $p(14)

$p(a + b)
"#;
                let statement_irs = test_litex_to_lean_ir(source, "resolved-defined-symbols-ir");
                let LitexToLeanStatementIr::Fact(result) = statement_irs.last().unwrap() else {
                    panic!("last IR item should be the resolved fact");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(rewrite),
                    premises,
                    ..
                } = underlying_test_proof(&result.fact.proof)
                else {
                    panic!("defined symbols should retain equality-rewrite evidence");
                };
                assert_eq!(rewrite.steps.len(), 2);
                assert!(matches!(
                    premises[0].proof,
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::Normalization { .. },
                        ..
                    }
                ));

                let output =
                    compile_to_lean_from_source(source, "resolved-defined-symbols").unwrap();
                assert!(output.contains("theorem fact"), "{output}");
                assert!(output.contains(": p (a + b) := by"), "{output}");
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn equality_transport_ignores_redundant_shortcuts_and_side_branches() {
        run_with_large_stack(
            "equality_transport_ignores_redundant_shortcuts_and_side_branches",
            || {
                let source = r#"
abstract_prop t(x)

forall a, b, c, f, g, h, u, v, w, z set:
    a = b
    b = c
    a = c
    c = g
    f = g
    h = b
    h = u
    u = v
    w = z
    $t(a)
    =>:
        $t(f)
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("branched-equality-transport");
                runtime.replace_litex_to_lean_ir_mode(true);
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut statement_irs = Vec::new();
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    statement_irs.push(result.litex_to_lean_ir().unwrap().clone());
                }

                let LitexToLeanStatementIr::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::EqualityRewrite(rewrite),
                    premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("conclusion should retain equality transport");
                };
                let equality_premises = premises[1..]
                    .iter()
                    .map(|premise| {
                        strip_parsing_free_param_tags_for_user_display(
                            &premise.proposition.to_string(),
                        )
                    })
                    .collect::<Vec<_>>();
                assert_eq!(
                    equality_premises,
                    vec![
                        "a = b".to_string(),
                        "b = c".to_string(),
                        "c = g".to_string(),
                        "f = g".to_string(),
                    ]
                );
                assert_eq!(rewrite.steps.len(), 4);
                assert_eq!(
                    rewrite.steps[3].direction,
                    LitexToLeanEqualityRewriteDirectionIr::Backward
                );

                let first_output =
                    compile_to_lean_from_source(source, "branched-equality-output").unwrap();
                assert!(!first_output.contains(": a = c :="));
                assert!(!first_output.contains(": h = b :="));
                assert!(!first_output.contains(": h = u :="));
                assert!(!first_output.contains(": u = v :="));
                assert!(!first_output.contains(": w = z :="));
                assert!(!first_output.contains("sorry"));
                for _ in 0..12 {
                    assert_eq!(
                        compile_to_lean_from_source(source, "branched-equality-output").unwrap(),
                        first_output
                    );
                }
            },
        );
    }

    #[test]
    fn comparison_notation_transport_is_structured_and_checked() {
        run_with_large_stack(
            "comparison_notation_transport_is_structured_and_checked",
            || {
                let source = "forall a, b R:\n    a > b\n    =>:\n        b < a";
                let lean = compile_to_lean_from_source(source, "comparison-notation-transport")
                    .expect("the verifier now retains the exact comparison duality source");
                assert!(
                    lean.contains("(litex_domain_fact_1 : a > b), b < a"),
                    "{lean}"
                );
                assert!(
                    lean.contains("have proof_fact_1_1 : a > b := litex_domain_fact_1"),
                    "{lean}"
                );
                assert!(lean.contains("exact proof_fact_1_1"), "{lean}");
                assert!(!lean.contains("sorry"), "{lean}");
            },
        );
    }

    #[test]
    fn equality_transport_without_stored_edge_provenance_fails_closed() {
        run_with_large_stack(
            "equality_transport_without_stored_edge_provenance_fails_closed",
            || {
                let source = r#"
abstract_prop t(x)

forall x R:
    x + 1 = 3
    $t(x)
    =>:
        $t(2)
"#;
                let error = compile_to_lean_from_source(source, "derived-equality-transport")
                    .expect_err("a derived equality without proof provenance must be rejected")
                    .trace_message();

                assert!(error.contains("has no compiler proof provenance"));
                assert!(!error.contains("sorry"));
            },
        );
    }

    #[test]
    fn direct_fact_citation_can_reference_a_forall_fact() {
        run_with_large_stack("direct_fact_citation_can_reference_a_forall_fact", || {
            let source = "forall x R:\n    x = x\n\nforall x R:\n    x = x";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("forall-citation-route");
            runtime.replace_litex_to_lean_ir_mode(true);
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .unwrap();
            let mut statement_irs = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).unwrap();
                let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                statement_irs.push(result.litex_to_lean_ir().unwrap().clone());
            }

            let LitexToLeanStatementIr::Fact(first) = &statement_irs[0] else {
                panic!("first IR item should be a forall fact");
            };
            let first_id = first.fact.fact_id.expect("first forall must have an ID");
            let LitexToLeanStatementIr::Fact(second) = &statement_irs[1] else {
                panic!("second IR item should be a cited forall fact");
            };
            assert!(matches!(
                underlying_test_proof(&second.fact.proof),
                LitexToLeanFactProofIr::KnownFactCitation { source_fact_id }
                    if *source_fact_id == first_id
            ));
        });
    }

    #[test]
    fn temporary_fact_id_survives_as_known_forall_domain_evidence() {
        run_with_large_stack(
            "temporary_fact_id_survives_as_known_forall_domain_evidence",
            || {
                let source = r#"
abstract_prop marked(x)

trust forall x R:
    x != 0
    =>:
        $marked(x)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)
"#;
                let output =
                    compile_to_lean_from_source(source, "temporary-domain-evidence").unwrap();

                assert!(
                    output.contains(
                        "intro x litex_param_fact_1 litex_domain_fact_1 litex_domain_fact_2"
                    ),
                    "{output}"
                );
                assert!(
                    output.contains("-- Litex parameter requirement for `x`: x : ℝ"),
                    "{output}"
                );
                assert!(output.contains("let proof_arg_1_1 : ℝ := x"), "{output}");
                assert!(
                    output.contains(
                        "have proof_fact_1_2 : x ∈ Litex.StandardSets.R := litex_param_fact_1"
                    ),
                    "{output}"
                );
                assert!(
                    output.contains("have proof_fact_1_3 : x ≠ 0 := litex_domain_fact_1"),
                    "{output}"
                );
                assert!(output.contains(":= fact"), "{output}");
                assert!(
                    output.contains(" proof_arg_1_1 proof_fact_1_2 proof_fact_1_3"),
                    "{output}"
                );
                assert_eq!(output.matches("\naxiom fact").count(), 1);
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn known_forall_use_materializes_arguments_application_and_goal_normalization() {
        run_with_large_stack(
            "known_forall_use_materializes_arguments_application_and_goal_normalization",
            || {
                let source = r#"
abstract_prop marked2(x, y)

trust forall x R:
    $marked2(x, x + 1)

$marked2(1, 2)
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("known-forall-materialization");
                runtime.replace_litex_to_lean_ir_mode(true);
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut statement_irs = Vec::new();
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    statement_irs.push(result.litex_to_lean_ir().unwrap().clone());
                }

                let LitexToLeanStatementIr::Fact(target) = &statement_irs[2] else {
                    panic!("third IR item should be the proved marked2 fact");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::Normalization {
                            kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                        },
                    premises,
                    ..
                } = underlying_test_proof(&target.fact.proof)
                else {
                    panic!("the final goal should retain normalization from a direct instance");
                };
                assert_eq!(premises.len(), 1);
                let direct_instance = &premises[0];
                assert_ne!(
                    direct_instance.proposition.to_string(),
                    target.fact.proposition.to_string()
                );
                let LitexToLeanFactProofIr::RuleApplication {
                    rule: LitexToLeanProofRuleIr::KnownForallInstantiation { arguments, .. },
                    parameter_requirements,
                    premises: domain_requirements,
                } = underlying_test_proof(&direct_instance.proof)
                else {
                    panic!("the normalization premise should be the direct forall instance");
                };
                assert_eq!(arguments.len(), 1);
                assert_eq!(arguments[0].param, "x");
                assert!(matches!(
                    &arguments[0].param_type,
                    LitexToLeanParameterTypeIr::MemberOf {
                        set: LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real),
                        element_carrier: LitexToLeanCarrierIr::Real,
                    }
                ));
                assert_eq!(parameter_requirements.len(), 1);
                assert!(domain_requirements.is_empty());

                let output = emit_lean_from_litex_to_lean_ir(&statement_irs).unwrap();
                assert!(
                    output.contains("-- Litex parameter requirement for `x`: (2 - 1) : ℝ"),
                    "{output}"
                );
                assert!(
                    output.contains("let proof_arg_2_1 : ℝ := (2 - 1)"),
                    "{output}"
                );
                assert!(
                    output.contains("have proof_fact_2_2 : (2 - 1) ∈ Litex.StandardSets.R := by"),
                    "{output}"
                );
                assert!(output.contains("have proof_fact_2_3 : marked2"), "{output}");
                assert!(output.contains(":= fact"), "{output}");
                assert!(output.contains(" proof_arg_2_1"), "{output}");
                assert!(
                    output.contains("convert proof_fact_1_1 using 1 <;> norm_num"),
                    "{output}"
                );
                assert!(output.contains("exact proof_fact_1_2"), "{output}");
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn changed_closed_real_membership_citation_uses_checked_closed_rule() {
        run_with_large_stack(
            "changed_closed_real_membership_citation_uses_checked_closed_rule",
            || {
                let source = r#"
trust 1 $in R

abstract_prop marked2(x, y)

trust forall x R:
    $marked2(x, x + 1)

$marked2(1, 2)
"#;
                let output =
                    compile_to_lean_from_source(source, "closed-membership-citation").unwrap();

                assert!(
                    output.contains("have proof_fact_2_2 : (2 - 1) ∈ Litex.StandardSets.R := by"),
                    "{output}"
                );
                assert!(output.contains("change True"), "{output}");
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn preloaded_fact_id_without_ir_declaration_is_rejected() {
        run_with_large_stack(
            "preloaded_fact_id_without_ir_declaration_is_rejected",
            || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("preloaded-fact-boundary");
                let tokenizer = Tokenizer::new();
                let mut blocks = tokenizer
                    .parse_blocks("trust 1 = 1", runtime.current_file_path_rc())
                    .unwrap();
                let mut block = blocks.remove(0);
                let statement = runtime.parse_stmt(&mut block).unwrap();
                run_stmt_at_global_env(&statement, &mut runtime).unwrap();

                let error = compile_to_lean("1 = 1", &mut runtime)
                    .expect_err("a preloaded ID has no declaration in this emitted Lean module")
                    .trace_message();
                assert!(error.contains("before that fact has a Lean declaration"));
                assert!(!runtime.litex_to_lean_ir_mode());
            },
        );
    }

    #[test]
    fn compile_to_lean_set_obj_abi_uses_native_sets_and_structural_set_operations() {
        run_with_large_stack(
            "compile_to_lean_set_obj_abi_uses_native_sets_and_structural_set_operations",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit");
                let source = fs::read_to_string(path).unwrap();
                let output = compile_to_lean_from_source(&source, "set-obj-abi").unwrap();

                assert!(output.contains("[LitexObject α"), "{output}");
                assert!(output.contains(": Set α"), "{output}");
                assert!(output.contains("(A ∪ B) = (A ∪ B)"), "{output}");
                assert!(output.contains("(A ∩ B) = (A ∩ B)"), "{output}");
                assert!(output.contains("(A \\ B) = (A \\ B)"), "{output}");
                assert_eq!(output.matches("intro _ _ A B\n  rfl").count(), 3);
                assert!(!output.contains("LitexSet"));
                assert!(!output.contains("inductive LitexSet"));
                assert!(!output.contains("Type uLitex"));
                assert!(!output.contains("(A B : ℝ)"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn binder_owning_object_probe_compiles_structural_terms_and_membership() {
        run_with_large_stack(
            "binder_owning_object_probe_compiles_structural_terms_and_membership",
            || {
                for (label, source) in [
                    (
                        "set-builder-membership",
                        "forall x R:\n    x > 0\n    =>:\n        x $in {y R: y > 0}\n",
                    ),
                    (
                        "anonymous-function-membership",
                        "fn(x R: x > 0) R+ {x + 1} $in fn(x R: x > 0) R+\n",
                    ),
                    (
                        "refined-function-output",
                        "forall f fn(x R: x > 0) R+, x R:\n    x > 0\n    =>:\n        f(x) $in R+\n",
                    ),
                    (
                        "nested-refined-function-output",
                        "forall f fn(x R: x > 0) fn(y R: y > 0) R+, x, y R:\n    x > 0\n    y > 0\n    =>:\n        f(x)(y) $in R+\n",
                    ),
                ] {
                    let output = compile_to_lean_from_source(source, label).unwrap_or_else(|error| {
                        panic!("{label} should compile: {}", error.trace_message())
                    });
                    if label == "anonymous-function-membership" {
                        assert!(
                            output.contains(
                                "have litex_fn_universal_membership_1 : x ∈ Litex.StandardSets.R"
                            ),
                            "the pointwise Litex forall proof must receive the native function binder's erased universal membership:\n{output}"
                        );
                        assert!(output.contains("intro x litex_fn_domain_1"), "{output}");
                    }
                }
            },
        );
    }

    #[test]
    fn compile_to_lean_set_builder_is_a_native_predicate_set() {
        run_with_large_stack(
            "compile_to_lean_set_builder_is_a_native_predicate_set",
            || {
                let source = "{x R: x = x} = {x R: x = x}";
                let output = compile_to_lean_from_source(source, "set-builder-structural")
                    .expect("a set builder must lower with its own local binder");

                assert!(output.contains("{x : ℝ |"), "{output}");
                assert!(
                    output.contains("(x ∈ Litex.StandardSets.R) ∧ x = x"),
                    "{output}"
                );
                assert!(output.contains("rfl"), "{output}");
                assert!(!output.contains("axiom fact"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn malformed_binder_owning_membership_evidence_fails_closed() {
        run_with_large_stack(
            "malformed_binder_owning_membership_evidence_fails_closed",
            || {
                let mut builder = test_litex_to_lean_ir(
                    "forall x R:\n    x > 0\n    =>:\n        x $in {y R: y > 0}",
                    "malformed-set-builder-membership",
                );
                let LitexToLeanStatementIr::Fact(statement) = &mut builder[0] else {
                    panic!("set-builder membership should retain one forall statement")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut statement.fact.proof
                else {
                    panic!("set-builder membership should retain forall introduction")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::SetBuilderMembership {
                            expected_premises, ..
                        },
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("set-builder membership should retain constructor evidence")
                };
                expected_premises.pop();
                let error = emit_lean_from_litex_to_lean_ir(&builder)
                    .expect_err("a missing set-builder predicate premise must stop emission")
                    .trace_message();
                assert!(error.contains("premises do not match"), "{error}");

                let mut anonymous = test_litex_to_lean_ir(
                    "fn(x R: x > 0) R+ {x + 1} $in fn(x R: x > 0) R+",
                    "malformed-anonymous-function-membership",
                );
                let LitexToLeanStatementIr::Fact(statement) = &mut anonymous[0] else {
                    panic!("anonymous membership should retain one fact")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::FunctionSetMembership {
                            expected_target,
                            expected_pointwise,
                            ..
                        },
                    ..
                } = underlying_test_proof_mut(&mut statement.fact.proof)
                else {
                    panic!("anonymous membership should retain pointwise evidence")
                };
                *expected_pointwise = expected_target.clone();
                let error = emit_lean_from_litex_to_lean_ir(&anonymous)
                    .expect_err("a non-forall pointwise certificate must stop emission")
                    .trace_message();
                assert!(error.contains("pointwise forall premise"), "{error}");

                let mut application = test_litex_to_lean_ir(
                    "forall f fn(x R: x > 0) R+, x R:\n    x > 0\n    =>:\n        f(x) $in R+",
                    "malformed-refined-application-membership",
                );
                let LitexToLeanStatementIr::Fact(statement) = &mut application[0] else {
                    panic!("refined application membership should retain one forall statement")
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut statement.fact.proof
                else {
                    panic!("refined application membership should retain forall introduction")
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    rule:
                        LitexToLeanProofRuleIr::FunctionApplicationReturnMembership {
                            function_set,
                            typed_return_set,
                            ..
                        },
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("refined application should retain exact return membership evidence")
                };
                *typed_return_set = function_set.clone();
                let error = emit_lean_from_litex_to_lean_ir(&application)
                    .expect_err("a retargeted application return set must stop emission")
                    .trace_message();
                assert!(
                    error.contains("does not match its source application"),
                    "{error}"
                );
            },
        );
    }

    #[test]
    fn closed_remainder_keeps_the_integer_operator_contract() {
        run_with_large_stack(
            "closed_remainder_keeps_the_integer_operator_contract",
            || {
                let output = compile_to_lean_from_source("5 % 2 = 5 % 2\n", "closed-remainder")
                    .expect("closed integer remainder should compile");

                assert!(
                    output.contains("(5 : ℤ) % (2 : ℤ)"),
                    "remainder literals must not elaborate as Nat:\n{output}"
                );
            },
        );
    }

    #[test]
    fn refined_numeric_binders_replay_source_well_definedness() {
        run_with_large_stack(
            "refined_numeric_binders_replay_source_well_definedness",
            || {
                for (label, source) in [
                    (
                        "nonzero-integer-remainder",
                        "forall a Z, b Z*:\n    a % b = a % b\n",
                    ),
                    (
                        "nonzero-real-function-domain",
                        "forall f fn(x R: x != 0) R, a R*:\n    f(a) = f(a)\n",
                    ),
                    (
                        "positive-real-function-domain",
                        "forall f fn(x R: x > 0) R, a R+:\n    f(a) = f(a)\n",
                    ),
                ] {
                    compile_to_lean_from_source(source, label).unwrap_or_else(|error| {
                        panic!("{label} should compile: {}", error.trace_message())
                    });
                }
            },
        );
    }

    #[test]
    fn integer_closure_and_closed_remainder_computation_have_checked_lowering() {
        run_with_large_stack(
            "integer_closure_and_closed_remainder_computation_have_checked_lowering",
            || {
                let source = r#"
forall a, b Z:
    a + b $in Z
    a - b $in Z
    a * b $in Z

5 % 2 = 1
"#;
                let output = compile_to_lean_from_source(source, "integer-closure-and-remainder")
                    .expect("integer closure and closed remainder computation should compile");
                assert!(output.contains("%"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn unsupported_builtin_never_falls_back_to_axiom_or_sorry() {
        run_with_large_stack(
            "unsupported_builtin_never_falls_back_to_axiom_or_sorry",
            || {
                let error = compile_to_lean_from_source("sin(0) = 0", "unsupported-builtin")
                    .expect_err("unsupported builtin must stop emission")
                    .trace_message();

                assert!(error.contains("no checked backend") || error.contains("does not support"));
            },
        );
    }

    #[test]
    fn compile_to_lean_partial_report_keeps_supported_statements_and_marks_incomplete() {
        run_with_large_stack(
            "compile_to_lean_partial_report_keeps_supported_statements_and_marks_incomplete",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_partial_report.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(&path.to_string_lossy());
                let report = compile_to_lean_with_report(&source, &mut runtime).unwrap();

                assert_eq!(report.status, LitexToLeanCompilationStatus::Incomplete);
                assert!(!report.is_complete());
                assert_eq!(report.unsupported.len(), 1);
                assert_eq!(report.unsupported[0].statement_index, 2);
                assert_eq!(
                    report.unsupported[0].phase,
                    LitexToLeanCompilationPhase::LeanEmission
                );
                assert!(report.unsupported[0].statement.contains("sin"));
                assert!(report
                    .lean_code
                    .contains("-- Litex-to-Lean status: incomplete"));
                assert!(report
                    .lean_code
                    .contains("-- Litex-to-Lean omitted statement 2 during Lean emission"));
                assert_eq!(report.lean_code.matches("theorem fact").count(), 2);
                assert!(!report.lean_code.contains("axiom"));
                assert!(!report.lean_code.contains("sorry"));
                assert!(!runtime.litex_to_lean_ir_mode());
            },
        );
    }

    #[test]
    fn compile_to_lean_partial_report_rolls_back_a_partly_emitted_statement() {
        run_with_large_stack(
            "compile_to_lean_partial_report_rolls_back_a_partly_emitted_statement",
            || {
                let mut source_ir =
                    test_litex_to_lean_ir("trust 1 = 1\n\n2 = 2", "partial-rollback");
                let LitexToLeanStatementIr::Trust(mut trusted) = source_ir.remove(0) else {
                    panic!("first test statement should produce trust IR");
                };
                let LitexToLeanStatementIr::Fact(proved) = source_ir.remove(0) else {
                    panic!("second test statement should produce fact IR");
                };
                trusted.facts.push(proved.fact);
                let report =
                    emit_lean_from_litex_to_lean_ir_with_report(&[LitexToLeanStatementIr::Trust(
                        trusted,
                    )]);

                assert_eq!(report.status, LitexToLeanCompilationStatus::Incomplete);
                assert_eq!(report.unsupported.len(), 1);
                assert_eq!(
                    report.unsupported[0].phase,
                    LitexToLeanCompilationPhase::LeanEmission
                );
                assert!(report.unsupported[0]
                    .reason
                    .contains("only an explicit Litex `trust` statement may emit a Lean axiom"));
                assert!(!report.lean_code.contains("axiom fact"));
                assert!(report
                    .lean_code
                    .contains("-- Litex-to-Lean omitted statement 1"));
            },
        );
    }

    #[test]
    fn unsupported_nested_requirement_builtin_is_rejected() {
        run_with_large_stack("unsupported_nested_requirement_builtin_is_rejected", || {
            let source = r#"
abstract_prop marked(x)

trust forall x R:
    x != 0
    =>:
        $marked(x)

$marked(1)
"#;
            let error = compile_to_lean_from_source(source, "unsupported-nested-requirement")
                .expect_err("numeric nonzero requirement has no Lean backend yet")
                .trace_message();

            assert!(error.contains("no checked backend"));
            assert!(!error.contains("sorry"));
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_mixed_projected_forall_compiles_with_lean() {
        run_with_large_stack(
            "compile_to_lean_mixed_projected_forall_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
                    "examples/05_compiler_interop/compile_to_lean_mixed_projected_forall.lit",
                );
                let source = fs::read_to_string(&path).unwrap();
                let generated =
                    compile_to_lean_from_source(&source, &path.to_string_lossy()).unwrap();

                let lean_file = private_tmp_lean_file("litex_to_lean_mixed_projected_forall");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "mixed projected-forall generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_set_obj_abi_compiles_with_lean() {
        run_with_large_stack("compile_to_lean_set_obj_abi_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit");
            let source = fs::read_to_string(path).unwrap();
            let generated = compile_to_lean_from_source(&source, "set-obj-abi-kernel").unwrap();

            let lean_file = private_tmp_lean_file("litex_to_lean_set_obj_abi");
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "set-Obj generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_statement_scopes_compile_with_lean() {
        run_with_large_stack("compile_to_lean_statement_scopes_compile_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_statement_scopes.lit");
            let source = fs::read_to_string(path).unwrap();
            let generated =
                compile_to_lean_from_source(&source, "statement-scopes-kernel").unwrap();

            let lean_file = private_tmp_lean_file("litex_to_lean_statement_scopes");
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "statement-scope generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_choice_have_compiles_with_lean() {
        run_with_large_stack("compile_to_lean_choice_have_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_choice_have.lit");
            let source = fs::read_to_string(path).unwrap();
            let generated = compile_to_lean_from_source(&source, "choice-have-kernel").unwrap();

            let lean_file = private_tmp_lean_file("litex_to_lean_choice_have");
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "choice-have generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_exist_have_compiles_with_lean() {
        run_with_large_stack("compile_to_lean_exist_have_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_exist_have.lit");
            let source = fs::read_to_string(path).unwrap();
            let generated = compile_to_lean_from_source(&source, "exist-have-kernel").unwrap();

            let lean_file = private_tmp_lean_file("litex_to_lean_exist_have");
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "exist-have generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_obtain_from_existential_prop_compiles_with_lean() {
        run_with_large_stack(
            "compile_to_lean_obtain_from_existential_prop_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let source = include_str!(
                    "../../examples/01_proof_patterns/obtain_from_existential_prop.lit"
                );
                let generated =
                    compile_to_lean_from_source(source, "obtain-from-existential-prop-kernel")
                        .unwrap();

                let lean_file = private_tmp_lean_file("litex_to_lean_obtain_from_prop");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "obtain-from-prop generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_atomic_fact_witness_compiles_with_lean() {
        run_with_large_stack(
            "compile_to_lean_atomic_fact_witness_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let source =
                    include_str!("../../examples/01_proof_patterns/witness_atomic_fact.lit");
                let generated =
                    compile_to_lean_from_source(source, "witness-atomic-fact-kernel").unwrap();

                let lean_file = private_tmp_lean_file("litex_to_lean_witness_atomic_fact");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "atomic fact witness generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_resolved_atomic_fact_compiles_with_lean() {
        run_with_large_stack(
            "compile_to_lean_resolved_atomic_fact_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit");
                let source = fs::read_to_string(&path).unwrap();
                let generated =
                    compile_to_lean_from_source(&source, &path.to_string_lossy()).unwrap();

                let lean_file = private_tmp_lean_file("litex_to_lean_resolved_atomic_fact");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "resolved-atomic-fact generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn generated_native_numeric_abi_compiles_with_lean() {
        run_with_large_stack("generated_native_numeric_abi_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let source_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_numeric_obj_abi.lit");
            let source = fs::read_to_string(&source_path).unwrap();
            let generated = compile_to_lean_from_source(
                &source,
                source_path.to_str().expect("example path must be UTF-8"),
            )
            .unwrap();
            assert!(generated.contains("(5 : ℤ) % (2 : ℤ)"), "{generated}");
            assert!(!generated.contains("sorry"), "{generated}");
            let lean_file = private_tmp_lean_file("litex_to_lean_native_numeric_abi");
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "native numeric ABI generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn generated_restricted_function_well_definedness_compiles_with_lean() {
        run_with_large_stack(
            "generated_restricted_function_well_definedness_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let source_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
                    "examples/05_compiler_interop/compile_to_lean_function_well_definedness.lit",
                );
                let source = fs::read_to_string(&source_path).unwrap();
                let generated = compile_to_lean_from_source(
                    &source,
                    source_path.to_str().expect("example path must be UTF-8"),
                )
                .unwrap();
                let lean_file = private_tmp_lean_file("litex_to_lean_function_wd");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "restricted function WD generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_partial_report_compiles_with_lean() {
        run_with_large_stack("compile_to_lean_partial_report_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples/05_compiler_interop/compile_to_lean_partial_report.lit");
            let source = fs::read_to_string(&path).unwrap();
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(&path.to_string_lossy());
            let report = compile_to_lean_with_report(&source, &mut runtime).unwrap();
            assert_eq!(report.status, LitexToLeanCompilationStatus::Incomplete);

            let lean_file = private_tmp_lean_file("litex_to_lean_partial");
            fs::write(&lean_file, &report.lean_code).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(&project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "partial generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                report.lean_code,
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_recursive_strategy_ir_compiles_with_lean() {
        run_with_large_stack(
            "compile_to_lean_recursive_strategy_ir_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit");
                let source = fs::read_to_string(&path).unwrap();
                let generated =
                    compile_to_lean_from_source(&source, &path.to_string_lossy()).unwrap();

                let lean_file = private_tmp_lean_file("litex_to_lean_recursive_strategy_ir");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "recursive-strategy generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_builtin_rules_20_compiles_with_lean() {
        run_with_large_stack(
            "compile_to_lean_builtin_rules_20_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit");
                let source = fs::read_to_string(&path).unwrap();
                let generated =
                    compile_to_lean_from_source(&source, &path.to_string_lossy()).unwrap();

                let lean_file = private_tmp_lean_file("litex_to_lean_builtin_rules_20");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lake)
                    .args(["env", "lean"])
                    .arg(&lean_file)
                    .current_dir(project)
                    .output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "20-rule generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn compile_to_lean_mvp_compiles_with_lean() {
        run_with_large_stack("compile_to_lean_mvp_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
            let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
            let source = r#"
abstract_prop transported(a)

forall a, b set:
    $transported(a)
    a = b
    =>:
        $transported(b)

abstract_prop related(x, y)

forall a, b set:
    $related(a, b)
    a = b
    =>:
        $related(b, a)

forall a, b, c set:
    $transported(c)
    a = b
    b = c
    =>:
        $transported(a)

abstract_prop marked(x)

prop is_one(x R):
    x = 1

trust forall x R:
    x != 0
    =>:
        $marked(x)

$is_one(1)

forall x R:
    x != 0
    x < 10
    =>:
        $marked(x)

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x

forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0

forall x R:
    x != 0
    =>:
        x != 0

abstract_prop marked2(x, y)

trust forall x R:
    $marked2(x, x + 1)

$marked2(1, 2)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("lean-kernel-mvp.lit");
            let generated = compile_to_lean(source, &mut runtime).unwrap();
            let lean_file = private_tmp_lean_file("litex_to_lean_mvp");
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new(lake)
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output();
            let _ = fs::remove_file(&lean_file);
            let output = output.unwrap();
            assert!(
                output.status.success(),
                "generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
    }

    #[test]
    fn compile_to_lean_builtin_set_and_abs_rules_preserve_checked_routes() {
        run_with_large_stack(
            "compile_to_lean_builtin_set_and_abs_rules_preserve_checked_routes",
            || {
                let source = r#"
forall A, B set:
    union(A, B) = union(B, A)

forall A set:
    union(A, A) = A

forall A set:
    union(A, {}) = A

forall A, B set:
    intersect(A, B) = intersect(B, A)

forall A, B set, x A:
    x $in union(A, B)

forall A, B set, x A:
    x $in B
    =>:
        x $in intersect(A, B)

forall A, B set, x A:
    not x $in B
    =>:
        x $in set_minus(A, B)

forall x R:
    0 <= x
    =>:
        abs(x) = x

forall x R:
    x != 0
    =>:
        0 < abs(x)

$is_nonempty_set(N)
$is_nonempty_set(Z)
$is_nonempty_set(Q)
$is_nonempty_set(R)
$is_nonempty_set(C)
"#;
                let ir = test_litex_to_lean_ir(source, "builtin-set-and-abs-rules");
                let output = emit_lean_from_litex_to_lean_ir(&ir).unwrap();
                assert_eq!(output.matches("theorem fact").count(), 14);
                for theorem in [
                    "set_union_commutative",
                    "set_union_idempotent",
                    "set_union_empty_right",
                    "set_intersect_commutative",
                    "set_union_membership_left",
                    "set_intersect_membership",
                    "set_set_minus_membership",
                    "order_abs_eq_self_of_nonnegative",
                    "order_abs_positive_of_nonzero",
                ] {
                    assert!(
                        output.contains(&format!("_root_.Litex.BuiltinRules.{theorem}")),
                        "{output}"
                    );
                }
                assert!(output.contains("exact abs_of_nonneg"), "{output}");
                assert!(output.contains("exact abs_pos.mpr"), "{output}");
                assert!(
                    output.contains("litexIsNonemptySet Litex.StandardSets.N"),
                    "{output}"
                );
                assert!(
                    output.contains("litexIsNonemptySet Litex.StandardSets.Z"),
                    "{output}"
                );
                assert!(
                    output.contains("litexIsNonemptySet Litex.StandardSets.Q"),
                    "{output}"
                );
                assert!(
                    output.contains("litexIsNonemptySet Litex.StandardSets.R"),
                    "{output}"
                );
                assert!(
                    output.contains("litexIsNonemptySet Litex.StandardSets.C"),
                    "{output}"
                );
                assert!(!output.contains("axiom"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn compile_to_lean_set_membership_rejects_malformed_premise_arity() {
        run_with_large_stack(
            "compile_to_lean_set_membership_rejects_malformed_premise_arity",
            || {
                let source = r#"
forall A, B set, x A:
    x $in union(A, B)
"#;
                let mut ir = test_litex_to_lean_ir(source, "set-membership-malformed");
                let LitexToLeanStatementIr::Fact(forall) = &mut ir[0] else {
                    panic!("set-membership tracer should store one forall fact");
                };
                let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("set-membership tracer should retain forall evidence");
                };
                let LitexToLeanFactProofIr::RuleApplication {
                    parameter_requirements,
                    ..
                } = underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("union membership should retain its builtin rule application");
                };
                parameter_requirements.pop();
                let error = emit_lean_from_litex_to_lean_ir(&ir)
                    .expect_err("malformed union membership evidence must stop emission")
                    .trace_message();
                assert!(
                    error.contains(
                        "expected 3 parameter requirements and 0 premises but received 2 and 0"
                    ),
                    "{error}"
                );
            },
        );
    }

    fn private_tmp_lean_file(stem: &str) -> std::path::PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::path::Path::new("/private/tmp").join(format!(
            "{}_{}_{}.lean",
            stem,
            std::process::id(),
            nonce
        ))
    }

    fn run_with_large_stack(test_name: &str, action: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(action)
            .unwrap()
            .join()
            .unwrap();
    }

    fn test_litex_to_lean_ir(source: &str, entry_label: &str) -> Vec<LitexToLeanStatementIr> {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(entry_label);
        runtime.replace_litex_to_lean_ir_mode(true);
        let tokenizer = Tokenizer::new();
        let blocks = tokenizer
            .parse_blocks(source, runtime.current_file_path_rc())
            .unwrap();
        let mut statement_irs = Vec::new();
        for mut block in blocks {
            let statement = runtime.parse_stmt(&mut block).unwrap();
            let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
            statement_irs.push(result.litex_to_lean_ir().unwrap().clone());
        }
        statement_irs
    }

    fn underlying_test_proof(mut proof: &LitexToLeanFactProofIr) -> &LitexToLeanFactProofIr {
        while let LitexToLeanFactProofIr::Memo { proof: source } = proof {
            proof = source.as_ref();
        }
        proof
    }

    fn underlying_test_proof_mut(
        mut proof: &mut LitexToLeanFactProofIr,
    ) -> &mut LitexToLeanFactProofIr {
        loop {
            match proof {
                LitexToLeanFactProofIr::Memo { proof: source } => proof = source.as_mut(),
                _ => return proof,
            }
        }
    }

    fn underlying_test_verified_by(mut verified_by: &VerifiedByResult) -> &VerifiedByResult {
        while let VerifiedByResult::StatementMemo(source) = verified_by {
            verified_by = &source.verified_by;
        }
        verified_by
    }
}
