use crate::common::keywords::IS_CHOICE_FUNCTION_FOR;
use crate::litex_to_lean_ir::LitexToLeanAggregateObjectIr;
use crate::prelude::*;
use crate::verify::rule_schema::{canonical_atomic_facts_equal, MatchLimits};
use std::collections::{HashMap, HashSet};

use super::shared_lean_library::{generated_import_header, rule_theorem_name};
use super::{
    LitexToLeanCompilationPhase, LitexToLeanCompilationReport, LitexToLeanUnsupportedStatement,
};

pub fn compile_to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let started_capture = runtime.start_well_defined_capture();
    let result = compile_to_lean_in_mode(source_code, runtime);
    if started_capture {
        runtime.stop_well_defined_capture();
    }
    result
}

pub fn compile_to_lean_with_report(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<LitexToLeanCompilationReport, RuntimeError> {
    let lean_code = compile_to_lean(source_code, runtime)?;
    Ok(LitexToLeanCompilationReport::new(lean_code, Vec::new()))
}

pub fn compile_to_lean_from_source(
    source_code: &str,
    entry_label: &str,
) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    compile_to_lean(&normalized, &mut runtime)
}

/// Verify one standalone Litex source and return the exact compiler IR captured
/// from that successful verifier run. Backends consume this tree instead of
/// reparsing source text or rerunning proof search.
pub fn capture_litex_to_lean_ir_from_source(
    source_code: &str,
    entry_label: &str,
) -> Result<Vec<LitexToLeanStatementIr>, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    let started_capture = runtime.start_well_defined_capture();
    let result = capture_litex_to_lean_ir(&normalized, &mut runtime);
    if started_capture {
        runtime.stop_well_defined_capture();
    }
    result
}

pub fn compile_to_lean_from_source_with_report(
    source_code: &str,
    entry_label: &str,
) -> Result<LitexToLeanCompilationReport, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    compile_to_lean_with_report(&normalized, &mut runtime)
}

pub fn emit_lean_from_litex_to_lean_ir(
    ir: &[LitexToLeanStatementIr],
) -> Result<String, RuntimeError> {
    let mut emitter = UniversalEmitter::new();
    for statement in ir {
        emitter.emit_statement(statement)?;
    }
    Ok(emitter.finish())
}

pub fn emit_lean_from_litex_to_lean_ir_with_report(
    ir: &[LitexToLeanStatementIr],
) -> LitexToLeanCompilationReport {
    match emit_lean_from_litex_to_lean_ir(ir) {
        Ok(lean_code) => LitexToLeanCompilationReport::new(lean_code, Vec::new()),
        Err(error) => {
            let line_file = default_line_file();
            let diagnostic = LitexToLeanUnsupportedStatement::new(
                1,
                "universal-object IR emission".to_string(),
                &line_file,
                LitexToLeanCompilationPhase::LeanEmission,
                error.trace_message(),
            );
            let lean_code = format!(
                "{}\n\n-- Litex-to-Lean incomplete: {}\n",
                generated_import_header(),
                diagnostic.reason.replace('\n', " ")
            );
            LitexToLeanCompilationReport::new(lean_code, vec![diagnostic])
        }
    }
}

fn compile_to_lean_in_mode(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<String, RuntimeError> {
    let ir = capture_litex_to_lean_ir(source_code, runtime)?;
    emit_lean_from_litex_to_lean_ir(&ir)
}

fn capture_litex_to_lean_ir(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<Vec<LitexToLeanStatementIr>, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let blocks = tokenizer.parse_blocks(source_code, runtime.current_file_path_rc())?;
    let mut ir = Vec::new();
    for mut block in blocks {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(universal_error(
                &statement.line_file(),
                "Litex-to-Lean received an unverified Litex statement",
            ));
        }
        let Some(statement_ir) = result.litex_to_lean_ir() else {
            return Err(universal_error(
                &statement.line_file(),
                "Litex-to-Lean capture completed a statement without producing IR",
            ));
        };
        ir.push(statement_ir.clone());
    }
    if ir.is_empty() {
        return Err(universal_error(
            &default_line_file(),
            "Litex-to-Lean requires at least one supported statement",
        ));
    }
    Ok(ir)
}

#[derive(Clone)]
struct GlobalFactBinding {
    theorem_name: String,
    proposition: Fact,
    parameter_symbol_ids: Vec<SymbolId>,
    parameter_fact_ids: Vec<FactId>,
    domain_fact_ids: Vec<FactId>,
}

#[derive(Clone)]
struct FunctionBinding {
    function: LitexToLeanFunctionTypeIr,
    membership_proof_name: String,
    uses_fn_space: bool,
}

#[derive(Clone)]
struct GlobalObjectBinding {
    name: String,
    source_object: Obj,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
    applicable_name: Option<String>,
    result_membership_name: Option<String>,
    function_membership_name: Option<String>,
}

#[derive(Clone, Default)]
struct RenderContext {
    symbol_names: HashMap<SymbolId, String>,
    local_fact_names: HashMap<FactId, String>,
    local_fact_propositions: HashMap<FactId, Fact>,
    local_forall_facts: HashMap<FactId, Fact>,
    well_defined_fact_names: HashMap<WellDefinedFactId, String>,
    /// Exact verifier DAG node selected for each certificate-bearing source object.
    /// The renderer never searches membership propositions to reconstruct this
    /// association.
    well_defined_object_ids: HashMap<SourceObjectOccurrenceId, WellDefinedObjId>,
    function_bindings: HashMap<FactId, FunctionBinding>,
    well_defined_object_names: HashMap<WellDefinedObjId, String>,
    well_defined_applicable_names: HashMap<WellDefinedObjId, String>,
    well_defined_result_membership_names: HashMap<WellDefinedObjId, String>,
    well_definedness: LitexToLeanWellDefinednessCertificateIr,
    /// Lexical WD scopes currently available to a local proof replay.  Facts
    /// and child objects may live in this scope or any visible prefix, never
    /// in a sibling/descendant scope.
    active_binder_scope_ids: Vec<WellDefinedBinderScopeId>,
    function_set_depth: usize,
    forall_depth: Option<usize>,
}

struct ForallEmission {
    context: RenderContext,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
    parameter_symbol_ids: Vec<SymbolId>,
    parameter_fact_ids: Vec<FactId>,
    domain_fact_ids: Vec<FactId>,
    local_proof_steps: Vec<LocalProofStep>,
    inferred_facts: Vec<InferredFactEmission>,
    conclusions: Vec<LitexToLeanFactIr>,
}

struct LocalProofStep {
    name: String,
    proposition: String,
    proof: String,
}

struct InferredFactEmission {
    name: String,
    proposition: String,
    proof: String,
}

#[derive(Clone)]
struct ApplicationScope {
    source_occurrence_id: SourceObjectOccurrenceId,
    context: RenderContext,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
}

#[derive(Clone)]
struct ProofCarryingObjectScope {
    source_occurrence_ids: HashSet<SourceObjectOccurrenceId>,
    context: RenderContext,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
}

struct RenderedFunctionApplication {
    result_membership: String,
    contract_fact_id: FactId,
    function: LitexToLeanFunctionTypeIr,
}

#[derive(Clone)]
struct WellDefinedHelperBinding {
    theorem_name: String,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
}

#[derive(Clone)]
struct BinderScopeEmission {
    context: RenderContext,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
}

#[derive(Clone)]
struct NamedFunctionHelpers {
    implementation_name: String,
    body_name: String,
    body_object_definition_names: Vec<String>,
}

struct UniversalEmitter {
    declarations: Vec<String>,
    global_facts: HashMap<FactId, GlobalFactBinding>,
    global_function_bindings: HashMap<FactId, FunctionBinding>,
    global_objects: HashMap<WellDefinedObjId, GlobalObjectBinding>,
    well_defined_helpers: HashMap<WellDefinedFactId, WellDefinedHelperBinding>,
    binder_scope_inferred_helpers:
        HashMap<(WellDefinedBinderScopeId, FactId), WellDefinedHelperBinding>,
    prop_definitions: HashMap<String, LitexToLeanDefPropStmtIr>,
    named_function_helpers: HashMap<String, NamedFunctionHelpers>,
    global_names: HashSet<String>,
    next_local_scope_id: usize,
    next_sketch_namespace_id: usize,
}

impl UniversalEmitter {
    fn new() -> Self {
        Self {
            declarations: Vec::new(),
            global_facts: HashMap::new(),
            global_function_bindings: HashMap::new(),
            global_objects: HashMap::new(),
            well_defined_helpers: HashMap::new(),
            binder_scope_inferred_helpers: HashMap::new(),
            prop_definitions: HashMap::new(),
            named_function_helpers: HashMap::new(),
            global_names: HashSet::new(),
            next_local_scope_id: 0,
            next_sketch_namespace_id: 0,
        }
    }

    fn finish(self) -> String {
        let mut output = generated_import_header().to_string();
        if !self.declarations.is_empty() {
            output.push_str("\n\n");
            output.push_str(&self.declarations.join("\n\n"));
        }
        output.push('\n');
        output
    }

    fn emit_statement(&mut self, statement: &LitexToLeanStatementIr) -> Result<(), RuntimeError> {
        let well_definedness = match statement {
            LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::LetObjStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjEqualStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveFnEqualStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::DefThmStmt(ir) => Some(&ir.well_definedness),
            LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ExampleStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::SketchStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ClaimStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::Fact(ir) => Some(&ir.well_definedness),
            LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessExistFact(ir)) => {
                Some(&ir.well_definedness)
            }
            LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessAtomicFact(ir)) => {
                Some(&ir.well_definedness)
            }
            _ => None,
        };
        if let Some(well_definedness) = well_definedness {
            crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                well_definedness,
            )
            .map_err(|message| universal_error(&statement_line_file(statement), message))?;
        }
        match statement {
            LitexToLeanStatementIr::Fact(ir) => self.emit_fact_statement(ir),
            LitexToLeanStatementIr::UnsafeStmt(ir) => match ir {
                LitexToLeanUnsafeStmtIr::TrustStmt(ir) => self.emit_trust(ir),
                LitexToLeanUnsafeStmtIr::TrustHaveStmt(_) => unreachable_unemitted_statement_ir(),
            },
            LitexToLeanStatementIr::DefObjStmt(ir) => match ir {
                LitexToLeanDefObjStmtIr::LetObjStmt(ir) => self.emit_let_object(ir),
                LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(ir) => {
                    self.emit_have_object_choice(ir)
                }
                LitexToLeanDefObjStmtIr::HaveObjEqualStmt(ir) => self.emit_have_object_equal(ir),
                LitexToLeanDefObjStmtIr::HaveObjByExistFactsStmt(ir) => {
                    self.emit_have_existential_witness(&ir.source, &ir.witnesses, &ir.projections)
                }
                LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(ir) => {
                    self.emit_have_existential_witness(&ir.source, &ir.witnesses, &ir.projections)
                }
                LitexToLeanDefObjStmtIr::ObtainObjFromAtomicFact(ir) => {
                    self.emit_have_existential_witness(&ir.source, &ir.witnesses, &ir.projections)
                }
                LitexToLeanDefObjStmtIr::HaveFnEqualStmt(ir) => self.emit_have_function_equal(ir),
                LitexToLeanDefObjStmtIr::HaveTupleStmt(ir) => self.emit_have_tuple(ir),
                LitexToLeanDefObjStmtIr::ObtainObjFromThm(_)
                | LitexToLeanDefObjStmtIr::HaveByPreimageStmt(_)
                | LitexToLeanDefObjStmtIr::HaveFnEqualCaseByCaseStmt(_)
                | LitexToLeanDefObjStmtIr::HaveFnByInducStmt(_)
                | LitexToLeanDefObjStmtIr::HaveFnByForallExistUniqueStmt(_)
                | LitexToLeanDefObjStmtIr::HaveCartStmt(_)
                | LitexToLeanDefObjStmtIr::HaveSeqStmt(_)
                | LitexToLeanDefObjStmtIr::HaveFiniteSeqStmt(_)
                | LitexToLeanDefObjStmtIr::HaveMatrixStmt(_) => {
                    unreachable_unemitted_statement_ir()
                }
            },
            LitexToLeanStatementIr::DefPredicateStmt(ir) => match ir {
                LitexToLeanDefPredicateStmtIr::DefPropStmt(ir) => self.emit_prop(ir),
                LitexToLeanDefPredicateStmtIr::DefAbstractPropStmt(ir) => {
                    self.emit_abstract_prop(ir)
                }
            },
            LitexToLeanStatementIr::DefInterfaceStmt(ir) => match ir {
                LitexToLeanDefInterfaceStmtIr::DefSettingStmt(_)
                | LitexToLeanDefInterfaceStmtIr::DefTemplateStmt(_)
                | LitexToLeanDefInterfaceStmtIr::DefStructStmt(_) => {
                    unreachable_unemitted_statement_ir()
                }
            },
            LitexToLeanStatementIr::DefAlgoStmt(_) | LitexToLeanStatementIr::DefStrategyStmt(_) => {
                unreachable_unemitted_statement_ir()
            }
            LitexToLeanStatementIr::DefThmStmt(ir) => self.emit_named_theorem(ir),
            LitexToLeanStatementIr::By(ir) => match ir {
                LitexToLeanByStmtIr::ByCasesStmt(ir) => {
                    self.emit_proof(&ir.facts, &ir.inferred_facts, &ir.well_definedness)
                }
                LitexToLeanByStmtIr::ByContraStmt(ir) => {
                    self.emit_proof(&ir.facts, &ir.inferred_facts, &ir.well_definedness)
                }
                LitexToLeanByStmtIr::ByDefStmt(ir) => {
                    self.emit_proof(&ir.facts, &ir.inferred_facts, &ir.well_definedness)
                }
                LitexToLeanByStmtIr::ByEnumerateFiniteSetStmt(_)
                | LitexToLeanByStmtIr::ByFiniteSetInducStmt(_)
                | LitexToLeanByStmtIr::ByInducStmt(_)
                | LitexToLeanByStmtIr::ByForStmt(_)
                | LitexToLeanByStmtIr::ByExtensionStmt(_)
                | LitexToLeanByStmtIr::ByEnumerateRangeStmt(_)
                | LitexToLeanByStmtIr::ByClosedRangeAsCasesStmt(_)
                | LitexToLeanByStmtIr::ByTransitivePropStmt(_)
                | LitexToLeanByStmtIr::BySymmetricPropStmt(_)
                | LitexToLeanByStmtIr::ByReflexivePropStmt(_)
                | LitexToLeanByStmtIr::ByAntisymmetricPropStmt(_)
                | LitexToLeanByStmtIr::ByZornLemmaStmt(_)
                | LitexToLeanByStmtIr::ByAxiomOfChoiceStmt(_)
                | LitexToLeanByStmtIr::ByRegularityAxiomStmt(_)
                | LitexToLeanByStmtIr::ByThmStmt(_) => unreachable_unemitted_statement_ir(),
            },
            LitexToLeanStatementIr::Witness(ir) => match ir {
                LitexToLeanWitnessStmtIr::WitnessExistFact(ir) => {
                    self.emit_proof(&ir.facts, &ir.inferred_facts, &ir.well_definedness)
                }
                LitexToLeanWitnessStmtIr::WitnessAtomicFact(ir) => {
                    self.emit_proof(&ir.facts, &ir.inferred_facts, &ir.well_definedness)
                }
                LitexToLeanWitnessStmtIr::WitnessNonemptySet(_) => {
                    unreachable_unemitted_statement_ir()
                }
            },
            LitexToLeanStatementIr::ProofBlock(ir) => match ir {
                LitexToLeanProofBlockStmtIr::ClaimStmt(ir) => self.emit_claim(ir),
                LitexToLeanProofBlockStmtIr::ExampleStmt(ir) => self.emit_example(ir),
                LitexToLeanProofBlockStmtIr::SketchStmt(ir) => self.emit_sketch(ir),
                LitexToLeanProofBlockStmtIr::TryStmt(_) => unreachable_unemitted_statement_ir(),
            },
            LitexToLeanStatementIr::Command(ir) => match ir {
                LitexToLeanCommandStmtIr::DoNothingStmt(_) => Ok(()),
                LitexToLeanCommandStmtIr::ImportStmt(_)
                | LitexToLeanCommandStmtIr::ClearStmt(_)
                | LitexToLeanCommandStmtIr::EvalStmt(_)
                | LitexToLeanCommandStmtIr::UseStrategyStmt(_)
                | LitexToLeanCommandStmtIr::StopStrategyStmt(_) => {
                    unreachable_unemitted_statement_ir()
                }
            },
        }
    }

    fn emit_abstract_prop(
        &mut self,
        ir: &LitexToLeanDefAbstractPropStmtIr,
    ) -> Result<(), RuntimeError> {
        let name = lean_name(&ir.name);
        if !self.global_names.insert(name.clone()) {
            return Err(universal_error(
                &default_line_file(),
                format!("Lean declaration name `{name}` is already in use"),
            ));
        }
        let declaration_type = if ir.params.is_empty() {
            "Prop".to_string()
        } else {
            let mut parts = vec!["Litex.Object"; ir.params.len()];
            parts.push("Prop");
            parts.join(" → ")
        };
        self.declarations
            .push(format!("axiom {name} : {declaration_type}"));
        Ok(())
    }

    fn emit_prop(&mut self, ir: &LitexToLeanDefPropStmtIr) -> Result<(), RuntimeError> {
        if ir.iff_facts.is_empty() {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "Litex-to-Lean first statement tranche rejects bodyless concrete prop `{}`",
                    ir.name
                ),
            ));
        }
        let name = lean_name(&ir.name);
        if !self.global_names.insert(name.clone()) {
            return Err(universal_error(
                &default_line_file(),
                format!("Lean declaration name `{name}` is already in use"),
            ));
        }
        let mut context = RenderContext::default();
        let mut binders = Vec::new();
        let mut components = Vec::new();
        for group in ir.params.iter() {
            if group.symbol_ids.len() != group.names.len() || group.names.is_empty() {
                return Err(universal_error(
                    &default_line_file(),
                    "concrete prop IR has mismatched or empty parameter groups",
                ));
            }
            for (symbol_id, source_name) in group.symbol_ids.iter().zip(group.names.iter()) {
                let binder_name = lean_name(source_name);
                context.symbol_names.insert(*symbol_id, binder_name.clone());
                binders.push(format!("({binder_name} : Litex.Object)"));
                components.push(self.render_ir_parameter_requirement(
                    &binder_name,
                    &group.param_type,
                    &context,
                )?);
            }
        }
        for clause in ir.iff_facts.iter() {
            components.push(self.render_fact(clause, &context)?);
        }
        let body = right_associated(components, " ∧ ", "True");
        let declaration = if binders.is_empty() {
            format!("def {name} : Prop :=\n  {body}")
        } else {
            format!("def {name} {} : Prop :=\n  {body}", binders.join(" "))
        };
        self.declarations.push(declaration);
        self.prop_definitions.insert(ir.name.clone(), ir.clone());
        Ok(())
    }

    fn emit_have_object_choice(
        &mut self,
        ir: &LitexToLeanHaveObjInNonemptySetOrParamTypeStmtIr,
    ) -> Result<(), RuntimeError> {
        let mut context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            ..RenderContext::default()
        };
        for choice in ir.choices.iter() {
            let name = lean_name(&choice.name);
            if !self.global_names.insert(name.clone()) {
                return Err(universal_error(
                    &choice.membership.proposition.line_file(),
                    format!("Lean declaration name `{name}` is already in use"),
                ));
            }
            let carrier = self.render_obj_ir(&choice.carrier, &context)?;
            let expected_nonempty = format!("Litex.IsNonemptySet {carrier}");
            if self.render_fact(&choice.nonempty_proof.proposition, &context)? != expected_nonempty
            {
                return Err(universal_error(
                    &choice.nonempty_proof.proposition.line_file(),
                    "object-choice proof does not establish nonemptiness of its retained carrier",
                ));
            }
            let nonempty_proof = self.render_proof_term(&choice.nonempty_proof, &context)?;
            let expected_membership = format!("Litex.In {name} {carrier}");
            if self.render_fact(&choice.membership.proposition, &context)? != expected_membership {
                return Err(universal_error(
                    &choice.membership.proposition.line_file(),
                    "object-choice membership does not match its retained definition and carrier",
                ));
            }
            let LitexToLeanFactProofIr::ObjectChoice {
                definition,
                carrier: proof_carrier,
            } = &choice.membership.proof
            else {
                return Err(universal_error(
                    &choice.membership.proposition.line_file(),
                    "object-choice membership has malformed proof evidence",
                ));
            };
            if lean_name(definition) != name || proof_carrier != &choice.carrier {
                return Err(universal_error(
                    &choice.membership.proposition.line_file(),
                    "object-choice membership changed its definition or carrier",
                ));
            }

            self.declarations.push(format!(
                "noncomputable def {name} : Litex.Object := Classical.choose ({nonempty_proof})"
            ));
            self.emit_named_fact(
                &choice.membership,
                format!("by\n  unfold {name}\n  exact Classical.choose_spec ({nonempty_proof})"),
            )?;
            context.symbol_names.insert(choice.symbol_id, name);
        }
        Ok(())
    }

    fn emit_have_existential_witness(
        &mut self,
        source: &LitexToLeanFactIr,
        witnesses: &[LitexToLeanExistentialWitnessIr],
        projections: &[LitexToLeanFactIr],
    ) -> Result<(), RuntimeError> {
        let Fact::ExistFact(source_existential) = &source.proposition else {
            return Err(universal_error(
                &source.proposition.line_file(),
                "existential elimination retained a non-existential source",
            ));
        };
        if !source_existential.is_plain_exist()
            || witnesses.len() != 1
            || source_existential.params_def_with_type().number_of_params() != 1
            || source_existential.facts().len() != 1
            || projections.len() != 2
        {
            return Err(universal_error(
                &source.proposition.line_file(),
                "the current existential-elimination emitter requires one witness with one type and one body projection",
            ));
        }
        let mut context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            ..RenderContext::default()
        };
        self.render_existential_fact(source_existential, &context)?;
        let source_proof = self.render_proof_term(source, &context)?;
        let witness = &witnesses[0];
        let name = lean_name(&witness.name);
        if !self.global_names.insert(name.clone()) {
            return Err(universal_error(
                &source.proposition.line_file(),
                format!("Lean declaration name `{name}` is already in use"),
            ));
        }
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.Object := Classical.choose ({source_proof})"
        ));
        context.symbol_names.insert(witness.symbol_id, name.clone());
        let source_binding = &source_existential.params_def_with_type().groups[0].params[0];
        context
            .symbol_names
            .insert(source_binding.id(), name.clone());
        let expected_type =
            self.render_ir_parameter_requirement(&name, &witness.param_type, &context)?;
        let expected_body = self.render_fact(
            &source_existential.facts()[0].from_ref_to_cloned_fact(),
            &context,
        )?;
        let mut saw_type = false;
        let mut saw_body = false;
        for projection in projections.iter() {
            let LitexToLeanFactProofIr::ExistentialElimination {
                source_proposition,
                role,
                expected_proposition,
            } = &projection.proof
            else {
                return Err(universal_error(
                    &projection.proposition.line_file(),
                    "existential projection has malformed proof evidence",
                ));
            };
            if !facts_are_canonically_equal(source_proposition, &source.proposition)?
                || !facts_are_canonically_equal(expected_proposition, &projection.proposition)?
            {
                return Err(universal_error(
                    &projection.proposition.line_file(),
                    "existential projection changed its source or expected proposition",
                ));
            }
            let (expected, selector) = match role {
                LitexToLeanExistentialProjectionRoleIr::ParameterType { witness_index: 0 } => {
                    saw_type = true;
                    (&expected_type, ".1")
                }
                LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index: 0 } => {
                    saw_body = true;
                    (&expected_body, ".2")
                }
                _ => {
                    return Err(universal_error(
                        &projection.proposition.line_file(),
                        "existential projection role is outside the retained one-witness tranche",
                    ));
                }
            };
            if self.render_fact(&projection.proposition, &context)? != *expected {
                return Err(universal_error(
                    &projection.proposition.line_file(),
                    "existential projection does not match its witness role",
                ));
            }
            self.emit_named_fact(
                projection,
                format!(
                    "by\n  unfold {name}\n  exact (Classical.choose_spec ({source_proof})){selector}"
                ),
            )?;
        }
        if !saw_type || !saw_body {
            return Err(universal_error(
                &source.proposition.line_file(),
                "existential elimination did not retain both projection roles",
            ));
        }
        Ok(())
    }

    fn emit_named_theorem(&mut self, ir: &LitexToLeanDefThmStmtIr) -> Result<(), RuntimeError> {
        if ir.expected_proof_step_count != ir.proof_steps.len()
            || ir
                .proof_steps
                .iter()
                .enumerate()
                .any(|(index, step)| step.position != index + 1)
        {
            return Err(universal_error(
                &ir.theorem.proposition.line_file(),
                "named theorem proof steps changed their retained source order",
            ));
        }
        let Fact::ForallFact(forall) = &ir.theorem.proposition else {
            return Err(universal_error(
                &ir.theorem.proposition.line_file(),
                "named theorem retained a non-forall proposition",
            ));
        };
        let mut emission =
            self.prepare_forall_emission(forall, &ir.theorem.proof, &ir.well_definedness)?;
        if emission.conclusions.len() != 1 {
            return Err(universal_error(
                &ir.theorem.proposition.line_file(),
                "named theorem emission requires one checked conclusion",
            ));
        }
        let name = lean_name(&ir.name);
        if !self.global_names.insert(name.clone()) {
            return Err(universal_error(
                &ir.theorem.proposition.line_file(),
                format!("Lean declaration name `{name}` is already in use"),
            ));
        }
        let theorem_type = render_top_level_forall_type(
            &render_explicit_binders(&emission.binder_names, &emission.binder_types)?,
            &self.render_fact(&emission.conclusions[0].proposition, &emission.context)?,
        );
        let mut proof_lines = vec!["by".to_string()];
        if !emission.binder_names.is_empty() {
            proof_lines.push(format!("  intro {}", emission.binder_names.join(" ")));
        }
        for step in emission.local_proof_steps.iter() {
            proof_lines.push(render_local_proof_step(step));
        }
        for inferred in emission.inferred_facts.iter() {
            proof_lines.push(format!(
                "  have {} : {} := by\n    exact {}",
                inferred.name, inferred.proposition, inferred.proof
            ));
        }
        let mut local_index = 0;
        for step in ir.proof_steps.iter() {
            let facts = statement_proof_facts(&step.statement).ok_or_else(|| {
                universal_error(
                    &statement_line_file(&step.statement),
                    format!(
                        "named theorem proof scope does not yet emit statement `{}`",
                        statement_label(&step.statement)
                    ),
                )
            })?;
            for fact in facts {
                local_index += 1;
                let local_name = format!("__step{local_index}");
                let fact_type = self.render_fact(&fact.proposition, &emission.context)?;
                let proof = self.render_proof_term(fact, &emission.context)?;
                proof_lines.push(format!(
                    "  have {local_name} : {fact_type} := by\n    exact {proof}"
                ));
                if let Some(fact_id) = fact.fact_id {
                    emission
                        .context
                        .local_fact_names
                        .insert(fact_id, local_name);
                    emission
                        .context
                        .local_fact_propositions
                        .insert(fact_id, fact.proposition.clone());
                }
            }
        }
        let conclusion_proof =
            self.render_proof_term(&emission.conclusions[0], &emission.context)?;
        proof_lines.push(format!("  exact {conclusion_proof}"));
        self.declarations.push(format!(
            "{} :=\n{}",
            render_declaration_head(&format!("theorem {name}"), &theorem_type),
            proof_lines.join("\n")
        ));

        if let Some(fact_id) = ir.theorem.fact_id {
            let binding = GlobalFactBinding {
                theorem_name: name,
                proposition: ir.theorem.proposition.clone(),
                parameter_symbol_ids: emission.parameter_symbol_ids,
                parameter_fact_ids: emission.parameter_fact_ids,
                domain_fact_ids: emission.domain_fact_ids,
            };
            self.global_facts.insert(fact_id, binding.clone());
            for conclusion in emission.conclusions.iter() {
                if let Some(conclusion_id) = conclusion.fact_id {
                    self.global_facts.insert(conclusion_id, binding.clone());
                }
            }
        }
        for projection in ir.stored_projections.iter() {
            self.emit_stored_fact(projection, &ir.well_definedness)?;
        }
        for inferred in ir.inferred_facts.iter() {
            self.emit_stored_fact(inferred, &ir.well_definedness)?;
        }
        Ok(())
    }

    fn emit_claim(&mut self, ir: &LitexToLeanClaimStmtIr) -> Result<(), RuntimeError> {
        if matches!(ir.target.proposition, Fact::ForallFact(_)) {
            return Err(universal_error(
                &ir.line_file,
                "this simple `claim` tranche does not emit `forall` goals",
            ));
        }
        if ir.target.fact_id.is_none() {
            return Err(universal_error(
                &ir.line_file,
                "a checked `claim` target has no exported FactId",
            ));
        }
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
            &ir.block.well_definedness,
        )
        .map_err(|message| universal_error(&ir.line_file, message))?;

        let mut context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            well_definedness: ir.well_definedness.clone(),
            ..RenderContext::default()
        };
        let mut local_steps = Vec::new();
        self.prepare_local_fact_well_definedness(
            &ir.target,
            &ir.well_definedness,
            &mut context,
            &mut local_steps,
        )?;
        local_steps.extend(self.render_local_proof_block(&ir.block, &mut context, "__step")?);
        let target_proof = self.render_proof_term(&ir.target, &context)?;
        let mut proof_lines = vec!["by".to_string()];
        for step in local_steps.iter() {
            proof_lines.push(render_local_proof_step(step));
        }
        proof_lines.push(format!("  exact {target_proof}"));
        self.emit_named_fact(&ir.target, proof_lines.join("\n"))?;
        for inferred in ir.inferred_facts.iter() {
            self.emit_stored_fact(inferred, &ir.well_definedness)?;
        }
        Ok(())
    }

    fn emit_example(&mut self, ir: &LitexToLeanExampleStmtIr) -> Result<(), RuntimeError> {
        if ir.target.fact_id.is_some() {
            return Err(universal_error(
                &ir.line_file,
                "an `example` target must not retain an exported FactId",
            ));
        }
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
            &ir.block.well_definedness,
        )
        .map_err(|message| universal_error(&ir.line_file, message))?;

        if let Fact::ForallFact(forall) = &ir.target.proposition {
            let mut emission =
                self.prepare_forall_emission(forall, &ir.target.proof, &ir.well_definedness)?;
            if emission.conclusions.len() != 1 {
                return Err(universal_error(
                    &ir.line_file,
                    "forall `example` emission requires one checked conclusion",
                ));
            }
            let example_type = render_top_level_forall_type(
                &render_explicit_binders(&emission.binder_names, &emission.binder_types)?,
                &self.render_fact(&emission.conclusions[0].proposition, &emission.context)?,
            );
            let mut proof_lines = vec!["by".to_string()];
            if !emission.binder_names.is_empty() {
                proof_lines.push(format!("  intro {}", emission.binder_names.join(" ")));
            }
            for step in emission.local_proof_steps.iter() {
                proof_lines.push(render_local_proof_step(step));
            }
            for inferred in emission.inferred_facts.iter() {
                proof_lines.push(format!(
                    "  have {} : {} := by\n    exact {}",
                    inferred.name, inferred.proposition, inferred.proof
                ));
            }
            for step in self.render_local_proof_block(&ir.block, &mut emission.context, "__step")? {
                proof_lines.push(render_local_proof_step(&step));
            }
            let conclusion_proof =
                self.render_proof_term(&emission.conclusions[0], &emission.context)?;
            proof_lines.push(format!("  exact {conclusion_proof}"));
            self.declarations.push(format!(
                "{} :=\n{}",
                render_declaration_head("example", &example_type),
                proof_lines.join("\n")
            ));
            return Ok(());
        }

        let mut context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            well_definedness: ir.well_definedness.clone(),
            ..RenderContext::default()
        };
        let example_type = self.render_fact(&ir.target.proposition, &context)?;
        let mut local_steps = Vec::new();
        self.prepare_local_fact_well_definedness(
            &ir.target,
            &ir.well_definedness,
            &mut context,
            &mut local_steps,
        )?;
        local_steps.extend(self.render_local_proof_block(&ir.block, &mut context, "__step")?);
        let target_proof = self.render_proof_term(&ir.target, &context)?;
        let mut proof_lines = vec!["by".to_string()];
        for step in local_steps.iter() {
            proof_lines.push(render_local_proof_step(step));
        }
        proof_lines.push(format!("  exact {target_proof}"));
        self.declarations.push(format!(
            "example : {example_type} :=\n{}",
            proof_lines.join("\n")
        ));
        Ok(())
    }

    fn emit_sketch(&mut self, ir: &LitexToLeanSketchStmtIr) -> Result<(), RuntimeError> {
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
            &ir.block.well_definedness,
        )
        .map_err(|message| universal_error(&ir.line_file, message))?;

        let mut nested = UniversalEmitter {
            declarations: Vec::new(),
            global_facts: self.global_facts.clone(),
            global_function_bindings: self.global_function_bindings.clone(),
            global_objects: self.global_objects.clone(),
            well_defined_helpers: self.well_defined_helpers.clone(),
            binder_scope_inferred_helpers: self.binder_scope_inferred_helpers.clone(),
            prop_definitions: self.prop_definitions.clone(),
            named_function_helpers: self.named_function_helpers.clone(),
            global_names: HashSet::new(),
            next_local_scope_id: 0,
            next_sketch_namespace_id: 0,
        };
        for statement in ir.block.steps.iter() {
            nested.emit_statement(statement)?;
        }
        self.next_sketch_namespace_id += 1;
        let namespace = format!("__Sketch{:02}", self.next_sketch_namespace_id);
        self.declarations.push(format!(
            "namespace {namespace}\n\n{}\n\nend {namespace}",
            nested.declarations.join("\n\n")
        ));
        Ok(())
    }

    fn emit_have_object_equal(
        &mut self,
        ir: &LitexToLeanHaveObjEqualStmtIr,
    ) -> Result<(), RuntimeError> {
        if ir.facts.len() != ir.definitions.len() * 2 {
            return Err(universal_error(
                &default_line_file(),
                "have-object equality IR must retain exactly two stored facts per definition",
            ));
        }
        for (index, definition) in ir.definitions.iter().enumerate() {
            let name = lean_name(&definition.name);
            if !self.global_names.insert(name.clone()) {
                return Err(universal_error(
                    &default_line_file(),
                    format!("Lean declaration name `{name}` is already in use"),
                ));
            }
            let mut context = RenderContext {
                function_bindings: self.global_function_bindings.clone(),
                well_definedness: ir.well_definedness.clone(),
                ..RenderContext::default()
            };
            let value = self.render_obj_ir(&definition.value, &context)?;
            self.declarations.push(format!(
                "noncomputable def {name} : Litex.Object := {value}"
            ));

            let type_fact = &ir.facts[index * 2];
            let equality_fact = &ir.facts[index * 2 + 1];
            let expected_type =
                self.render_ir_parameter_requirement(&name, &definition.param_type, &context)?;
            let expected_value_type =
                self.render_ir_parameter_requirement(&value, &definition.param_type, &context)?;
            let expected_equality = format!("{name} = {value}");
            if self.render_fact(&type_fact.proposition, &context)? != expected_type
                || self.render_fact(&equality_fact.proposition, &context)? != expected_equality
            {
                return Err(universal_error(
                    &type_fact.proposition.line_file(),
                    "have-object equality facts do not match the retained definition",
                ));
            }
            let LitexToLeanFactProofIr::ObjectDefinition {
                definition: type_definition,
                value: type_value,
                value_check: Some(value_check),
            } = &type_fact.proof
            else {
                return Err(universal_error(
                    &type_fact.proposition.line_file(),
                    "have-object type fact has no checked value-membership proof",
                ));
            };
            if lean_name(type_definition) != name
                || type_value != &definition.value
                || self.render_fact(&value_check.proposition, &context)? != expected_value_type
            {
                return Err(universal_error(
                    &type_fact.proposition.line_file(),
                    "have-object type proof changed its definition, value, or required type",
                ));
            }
            let LitexToLeanFactProofIr::ObjectDefinition {
                definition: equality_definition,
                value: equality_value,
                value_check: None,
            } = &equality_fact.proof
            else {
                return Err(universal_error(
                    &equality_fact.proposition.line_file(),
                    "have-object defining equality has malformed proof evidence",
                ));
            };
            if lean_name(equality_definition) != name || equality_value != &definition.value {
                return Err(universal_error(
                    &equality_fact.proposition.line_file(),
                    "have-object equality proof changed its definition or value",
                ));
            }

            let mut local_well_definedness_steps = Vec::new();
            self.prepare_local_owned_set_builder_audits(
                &mut context,
                &definition.value,
                &mut local_well_definedness_steps,
            )?;
            let value_proof = self.render_proof_term(value_check, &context)?;
            let mut type_proof = vec!["by".to_string()];
            type_proof.extend(
                local_well_definedness_steps
                    .iter()
                    .map(render_local_proof_step),
            );
            type_proof.push(format!("  simpa only [{name}] using ({value_proof})"));
            self.emit_named_fact(type_fact, type_proof.join("\n"))?;
            self.emit_named_fact(equality_fact, "by\n  rfl".to_string())?;
        }
        Ok(())
    }

    /// Emit a kernel-checked but term-neutral audit for each set builder owned
    /// by this definition.  The object value stays `Litex.setBuilder ...`;
    /// parameter and predicate assumptions exist only inside this local `have`.
    fn prepare_local_owned_set_builder_audits(
        &mut self,
        context: &mut RenderContext,
        value: &LitexToLeanObjectIr,
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let certificate = context.well_definedness.clone();
        let objects_by_id = certificate
            .objects
            .iter()
            .map(|object| (object.well_defined_obj_id, object))
            .collect::<HashMap<_, _>>();
        let mut audited_scope_ids = HashSet::new();
        for root_id in certificate.root_obj_ids.iter().copied() {
            let object = objects_by_id.get(&root_id).ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!("root WellDefinedObjId {} is missing", root_id.value()),
                )
            })?;
            let lowered = LitexToLeanObjectIr::lower(&object.source_object)
                .map_err(|message| universal_error(&default_line_file(), message))?;
            if &lowered != value || !matches!(object.source_object, Obj::SetBuilder(_)) {
                continue;
            }
            let scope_id = object.owned_binder_scope_id.ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "set-builder obj_{} has no owned binder scope",
                        object.well_defined_obj_id.value()
                    ),
                )
            })?;
            if !audited_scope_ids.insert(scope_id) {
                continue;
            }
            let scope = certificate
                .binder_scopes
                .iter()
                .find(|scope| scope.scope_id == scope_id)
                .ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!("set-builder scope {} is missing", scope_id.value()),
                    )
                })?;
            let Obj::SetBuilder(builder) = &scope.owner_object else {
                return Err(universal_error(
                    &default_line_file(),
                    format!("scope {} changed its set-builder owner", scope_id.value()),
                ));
            };

            let mut nested = context.clone();
            nested.active_binder_scope_ids = scope.ambient_scope_ids.clone();
            nested.active_binder_scope_ids.push(scope_id);
            let parameter_name = format!("__wd_scope{}_arg1", scope_id.value());
            nested
                .symbol_names
                .insert(builder.param_binding.id(), parameter_name.clone());
            let mut binder_names = vec![parameter_name];
            let mut binder_types = vec!["Litex.Object".to_string()];
            for (premise_index, premise) in scope.premises.iter().enumerate() {
                let proof_name = format!(
                    "__wd_scope{}_premise{}",
                    scope_id.value(),
                    premise_index + 1
                );
                let proof_type = self.render_fact(&premise.proposition, &nested)?;
                binder_names.push(proof_name.clone());
                binder_types.push(proof_type);
                nested.local_fact_names.insert(premise.fact_id, proof_name);
                nested
                    .local_fact_propositions
                    .insert(premise.fact_id, premise.proposition.clone());
            }

            let mut nested_steps = Vec::new();
            for inferred in scope.inferred_premises.iter() {
                let fact_id = inferred.fact_id.ok_or_else(|| {
                    universal_error(
                        &inferred.proposition.line_file(),
                        format!(
                            "set-builder scope {} has an inferred premise without FactId",
                            scope_id.value()
                        ),
                    )
                })?;
                let name = format!("__scope{}_fact{}", scope_id.value(), fact_id.value());
                let proposition = self.render_fact(&inferred.proposition, &nested)?;
                let proof = self.render_proof_term(inferred, &nested)?;
                push_unique_local_proof_step(
                    &mut nested_steps,
                    LocalProofStep {
                        name: name.clone(),
                        proposition,
                        proof,
                    },
                )?;
                nested.local_fact_names.insert(fact_id, name);
                nested
                    .local_fact_propositions
                    .insert(fact_id, inferred.proposition.clone());
            }

            let child_ids = object
                .child_uses
                .iter()
                .map(|child| child.obj_id)
                .collect::<HashSet<_>>();
            self.prepare_local_scoped_well_defined_facts(
                &mut nested,
                &certificate,
                &HashSet::new(),
                &child_ids,
                &mut nested_steps,
            )?;
            if nested_steps.is_empty() {
                continue;
            }

            let binders = render_explicit_binders(&binder_names, &binder_types)?;
            let bundled_proposition = right_associated(
                nested_steps
                    .iter()
                    .map(|step| step.proposition.clone())
                    .collect(),
                " ∧ ",
                "True",
            );
            let mut proof_lines = vec![
                "by".to_string(),
                format!("  intro {}", binder_names.join(" ")),
            ];
            proof_lines.extend(nested_steps.iter().map(render_local_proof_step));
            proof_lines.push(format!(
                "  exact {}",
                right_associated_conjunction_proof(
                    nested_steps.iter().map(|step| step.name.clone()).collect(),
                )
                .expect("a nonempty set-builder audit has a conjunction proof")
            ));
            let scope_name = format!("__set_builder_scope{}", scope_id.value());
            push_unique_local_proof_step(
                local_steps,
                LocalProofStep {
                    name: scope_name,
                    proposition: format!("∀ {}, {bundled_proposition}", binders.join(" ")),
                    proof: proof_lines.join("\n"),
                },
            )?;
        }
        Ok(())
    }

    fn emit_let_object(&mut self, ir: &LitexToLeanLetObjStmtIr) -> Result<(), RuntimeError> {
        let name = lean_name(&ir.name);
        if !self.global_names.insert(name.clone()) {
            return Err(universal_error(
                &ir.line_file,
                format!("Lean declaration name `{name}` is already in use"),
            ));
        }
        let context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            well_definedness: ir.well_definedness.clone(),
            ..RenderContext::default()
        };
        let value = self.render_obj_ir(&ir.value, &context)?;
        let LitexToLeanFactProofIr::ObjectDefinition {
            definition,
            value: proof_value,
            value_check: None,
        } = &ir.defining_equality.proof
        else {
            return Err(universal_error(
                &ir.line_file,
                "a `let` defining equality has malformed proof evidence",
            ));
        };
        if lean_name(definition) != name
            || proof_value != &ir.value
            || self.render_fact(&ir.defining_equality.proposition, &context)?
                != format!("{name} = {value}")
        {
            return Err(universal_error(
                &ir.line_file,
                "a `let` defining equality changed its retained name or value",
            ));
        }
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.Object := {value}"
        ));
        self.emit_named_fact(&ir.defining_equality, "by\n  rfl".to_string())?;
        for inferred in ir.inferred_facts.iter() {
            self.emit_stored_fact(inferred, &ir.well_definedness)?;
        }
        Ok(())
    }

    fn scoped_context_with_substitutions(
        &self,
        source: &RenderContext,
        substitutions: &HashMap<String, String>,
        description: &str,
    ) -> RenderContext {
        let mut target = source.clone();
        for name in target.symbol_names.values_mut() {
            if let Some(replacement) = substitutions.get(name) {
                *name = replacement.clone();
            }
        }
        for name in target.local_fact_names.values_mut() {
            if let Some(replacement) = substitutions.get(name) {
                *name = replacement.clone();
            }
        }
        for binding in target.function_bindings.values_mut() {
            if let Some(replacement) = substitutions.get(&binding.membership_proof_name) {
                binding.membership_proof_name = replacement.clone();
            }
        }

        let selected_well_defined_facts = source
            .well_defined_fact_names
            .keys()
            .copied()
            .collect::<Vec<_>>();
        target.well_defined_fact_names.clear();
        for fact_id in selected_well_defined_facts {
            let Some(helper) = self.well_defined_helpers.get(&fact_id) else {
                continue;
            };
            if let Ok(applied) = apply_scoped_declaration_with_substitutions(
                &helper.theorem_name,
                &helper.binder_names,
                &helper.binder_types,
                substitutions,
                description,
            ) {
                target.well_defined_fact_names.insert(fact_id, applied);
            }
        }

        let selected_objects = source
            .well_defined_object_names
            .keys()
            .copied()
            .collect::<Vec<_>>();
        target.well_defined_object_names.clear();
        target.well_defined_applicable_names.clear();
        target.well_defined_result_membership_names.clear();
        for obj_id in selected_objects {
            let Some(binding) = self.global_objects.get(&obj_id) else {
                continue;
            };
            let Ok(applied) = apply_scoped_declaration_with_substitutions(
                &binding.name,
                &binding.binder_names,
                &binding.binder_types,
                substitutions,
                description,
            ) else {
                continue;
            };
            target.well_defined_object_names.insert(obj_id, applied);
            if let Some(name) = &binding.applicable_name {
                if let Ok(applied) = apply_scoped_declaration_with_substitutions(
                    name,
                    &binding.binder_names,
                    &binding.binder_types,
                    substitutions,
                    description,
                ) {
                    target.well_defined_applicable_names.insert(obj_id, applied);
                }
            }
            if let Some(name) = &binding.result_membership_name {
                if let Ok(applied) = apply_scoped_declaration_with_substitutions(
                    name,
                    &binding.binder_names,
                    &binding.binder_types,
                    substitutions,
                    description,
                ) {
                    target
                        .well_defined_result_membership_names
                        .insert(obj_id, applied);
                }
            }
        }
        target
    }

    fn emit_have_function_equal(
        &mut self,
        ir: &LitexToLeanHaveFnEqualStmtIr,
    ) -> Result<(), RuntimeError> {
        let name = lean_name(&ir.name);
        let spec_name = format!("__{name}_spec");
        let body_name = format!("__{name}_body");
        let closed_name = format!("__{name}_closed");
        let implementation_name = format!("__{name}_impl");
        for declaration_name in [
            spec_name.as_str(),
            body_name.as_str(),
            closed_name.as_str(),
            implementation_name.as_str(),
            name.as_str(),
        ] {
            if !self.global_names.insert(declaration_name.to_string()) {
                return Err(universal_error(
                    &ir.membership.proposition.line_file(),
                    format!("Lean declaration name `{declaration_name}` is already in use"),
                ));
            }
        }

        if ir.membership.proposition.to_string() != ir.membership.expected_proposition.to_string()
            || ir.defining_equality.proposition.to_string()
                != ir.defining_equality.expected_proposition.to_string()
        {
            return Err(universal_error(
                &ir.membership.proposition.line_file(),
                "named-function stored effects changed their exact propositions",
            ));
        }
        let lowered_function_set = LitexToLeanObjectIr::lower(&ir.source_function_set)
            .map_err(|message| universal_error(&ir.membership.proposition.line_file(), message))?;
        if lowered_function_set
            != (LitexToLeanObjectIr::FunctionSet {
                function: Box::new(ir.function.clone()),
            })
            || LitexToLeanObjectIr::lower(&ir.source_body).map_err(|message| {
                universal_error(&ir.membership.proposition.line_file(), message)
            })? != ir.body
        {
            return Err(universal_error(
                &ir.membership.proposition.line_file(),
                "named-function signature or body changed after verifier lowering",
            ));
        }

        let base_context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            well_definedness: ir.well_definedness.clone(),
            ..RenderContext::default()
        };
        let expected_requirement_count =
            ir.function.parameters.len() + ir.function.domain_facts.len();
        if ir.parameter_premises.len() != ir.function.parameters.len()
            || ir.domain_premises.len() != ir.function.domain_facts.len()
            || expected_requirement_count == 0
        {
            return Err(universal_error(
                &ir.return_check.proposition.line_file(),
                "named-function binder requirements changed their retained source arity",
            ));
        }

        let lowered_return_set =
            LitexToLeanObjectIr::lower(&ir.source_return_set).map_err(|message| {
                universal_error(&ir.return_check.proposition.line_file(), message)
            })?;
        if lowered_return_set != *ir.function.return_set {
            return Err(universal_error(
                &ir.return_check.proposition.line_file(),
                "named-function return set changed after verifier lowering",
            ));
        }

        // First expose the verifier's local binder scope directly. Every local
        // __wd<depth>_<id> step below is interpreted under this exact ordered
        // telescope, never by a reconstructed proposition search in Lean.
        let mut scoped_context = base_context.clone();
        let mut scoped_binder_names =
            Vec::with_capacity(ir.function.parameters.len() + expected_requirement_count);
        let mut scoped_binder_types = Vec::with_capacity(scoped_binder_names.capacity());
        let mut parameter_binder_names = Vec::with_capacity(ir.function.parameters.len());
        for (index, parameter) in ir.function.parameters.iter().enumerate() {
            let binder_name = format!("__arg_{index}");
            scoped_context
                .symbol_names
                .insert(parameter.symbol_id, binder_name.clone());
            parameter_binder_names.push(binder_name.clone());
            scoped_binder_names.push(binder_name);
            scoped_binder_types.push("Litex.Object".to_string());
        }

        let ordered_premises = ir
            .parameter_premises
            .iter()
            .chain(ir.domain_premises.iter())
            .collect::<Vec<_>>();
        let mut premise_binder_names = Vec::with_capacity(expected_requirement_count);
        for (requirement_index, premise) in ordered_premises.iter().enumerate() {
            let expected = if requirement_index < ir.function.parameters.len() {
                let parameter = &ir.function.parameters[requirement_index];
                let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premise.fact else {
                    return Err(universal_error(
                        &premise.fact.line_file(),
                        "named-function parameter premise is not a membership fact",
                    ));
                };
                let LitexToLeanObjectIr::Symbol {
                    symbol_id: premise_symbol_id,
                    ..
                } = LitexToLeanObjectIr::lower(&membership.element)
                    .map_err(|message| universal_error(&premise.fact.line_file(), message))?
                else {
                    return Err(universal_error(
                        &premise.fact.line_file(),
                        "named-function parameter premise targets a non-symbol object",
                    ));
                };
                if premise_symbol_id != parameter.symbol_id {
                    return Err(universal_error(
                        &premise.fact.line_file(),
                        "named-function parameter premise changed its retained SymbolId",
                    ));
                }
                format!(
                    "Litex.In {} {}",
                    parameter_binder_names[requirement_index],
                    self.render_obj_ir(&parameter.set, &scoped_context)?
                )
            } else {
                self.render_fact(
                    &ir.function.domain_facts[requirement_index - ir.function.parameters.len()],
                    &scoped_context,
                )?
            };
            let rendered = self.render_fact(&premise.fact, &scoped_context)?;
            if rendered != expected {
                return Err(universal_error(
                    &premise.fact.line_file(),
                    format!(
                        "named-function local premise changed its parameter/domain position: expected `{expected}`, got `{rendered}`"
                    ),
                ));
            }
            let proof_name = if requirement_index < ir.function.parameters.len() {
                format!("__h_arg{requirement_index}")
            } else {
                format!(
                    "__h_dom{}",
                    requirement_index - ir.function.parameters.len()
                )
            };
            premise_binder_names.push(proof_name.clone());
            scoped_binder_names.push(proof_name.clone());
            scoped_binder_types.push(expected);
            scoped_context
                .local_fact_names
                .insert(premise.fact_id, proof_name.clone());
            scoped_context
                .local_fact_propositions
                .insert(premise.fact_id, premise.fact.clone());

            if requirement_index < ir.function.parameters.len() {
                if let LitexToLeanObjectIr::FunctionSet { function } =
                    &ir.function.parameters[requirement_index].set
                {
                    scoped_context.function_bindings.insert(
                        premise.fact_id,
                        FunctionBinding {
                            function: function.as_ref().clone(),
                            membership_proof_name: proof_name,
                            uses_fn_space: function_ir_uses_fn_space(function.as_ref()),
                        },
                    );
                }
            }
        }

        let arguments_name = "__fn_arg";
        let length_name = "__fn_arg_len";
        let requirements_name = "__fn_arg_req";
        let mut body_substitutions = HashMap::new();
        for (index, binder_name) in parameter_binder_names.iter().enumerate() {
            body_substitutions.insert(
                binder_name.clone(),
                format!("(Litex.arg {arguments_name} {index})"),
            );
        }
        for (index, binder_name) in premise_binder_names.iter().enumerate() {
            body_substitutions.insert(
                binder_name.clone(),
                dependent_requirement_projection(requirements_name, index),
            );
        }
        let mut body_context = self.scoped_context_with_substitutions(
            &scoped_context,
            &body_substitutions,
            "named-function body/range",
        );
        for (index, premise) in ordered_premises.iter().enumerate() {
            body_context.local_fact_names.insert(
                premise.fact_id,
                dependent_requirement_projection(requirements_name, index),
            );
        }
        let mut local_proof_steps = Vec::new();
        for (index, inferred) in ir.inferred_premises.iter().enumerate() {
            let fact_id = inferred.fact_id.ok_or_else(|| {
                universal_error(
                    &inferred.proposition.line_file(),
                    "named-function inferred premise reached emission without a FactId",
                )
            })?;
            self.prepare_local_well_defined_facts_for_fact_type(
                &mut body_context,
                &inferred.proposition,
                &[],
                &[],
                &mut local_proof_steps,
            )?;
            self.prepare_local_well_defined_facts_for_fact_proof(
                &mut body_context,
                inferred,
                &[],
                &[],
                &mut local_proof_steps,
            )?;
            let proposition = self.render_fact(&inferred.proposition, &body_context)?;
            let proof = self.render_proof_term(inferred, &body_context)?;
            let local_name = format!("__inferred{index}");
            push_unique_local_proof_step(
                &mut local_proof_steps,
                LocalProofStep {
                    name: local_name.clone(),
                    proposition,
                    proof,
                },
            )?;
            body_context.local_fact_names.insert(fact_id, local_name);
            body_context
                .local_fact_propositions
                .insert(fact_id, inferred.proposition.clone());
        }

        let mut source_occurrence_ids = HashSet::new();
        collect_proof_carrying_object_occurrence_ids(&ir.body, &mut source_occurrence_ids)?;
        collect_proof_carrying_object_occurrence_ids(
            ir.function.return_set.as_ref(),
            &mut source_occurrence_ids,
        )?;
        let well_definedness = ir.well_definedness.clone();
        self.prepare_local_scoped_well_defined_facts(
            &mut body_context,
            &well_definedness,
            &source_occurrence_ids,
            &HashSet::new(),
            &mut local_proof_steps,
        )?;
        self.prepare_local_well_defined_facts_for_fact_type(
            &mut body_context,
            &ir.return_check.proposition,
            &[],
            &[],
            &mut local_proof_steps,
        )?;
        self.prepare_local_well_defined_facts_for_fact_proof(
            &mut body_context,
            &ir.return_check,
            &[],
            &[],
            &mut local_proof_steps,
        )?;

        let body = self.render_obj(&ir.source_body, &body_context)?;
        let range = self.render_obj(&ir.source_return_set, &body_context)?;

        // Render the requirement proposition under its own dependent proof
        // binders. This is separate from the body projection context because
        // the telescope is defining `requirements`, not consuming it.
        let mut requirement_substitutions = HashMap::new();
        for (index, binder_name) in parameter_binder_names.iter().enumerate() {
            requirement_substitutions.insert(
                binder_name.clone(),
                format!("(Litex.arg {arguments_name} {index})"),
            );
        }
        let mut rendered_requirements = Vec::with_capacity(expected_requirement_count);
        for (index, premise) in ordered_premises.iter().enumerate() {
            let mut requirement_context = self.scoped_context_with_substitutions(
                &scoped_context,
                &requirement_substitutions,
                "named-function requirement telescope",
            );
            for earlier in 0..index {
                requirement_context.local_fact_names.insert(
                    ordered_premises[earlier].fact_id,
                    premise_binder_names[earlier].clone(),
                );
            }
            let proposition = self.render_fact(&premise.fact, &requirement_context)?;
            rendered_requirements.push((premise_binder_names[index].clone(), proposition));
            requirement_substitutions.insert(
                premise_binder_names[index].clone(),
                premise_binder_names[index].clone(),
            );
        }
        let requirements = dependent_requirement_telescope(&rendered_requirements);
        let spec = format!(
            "({{ arity := {}, requirements := fun {arguments_name} => {requirements}, range := fun {arguments_name} {length_name} {requirements_name} => {range} }} : Litex.FnSpec)",
            ir.function.parameters.len()
        );
        self.declarations.push(format!(
            "noncomputable def {spec_name} : Litex.FnSpec :=\n  {spec}"
        ));
        self.declarations.push(format!(
            "noncomputable def {body_name}\n    ({arguments_name} : List Litex.Object)\n    ({length_name} : {arguments_name}.length = {spec_name}.arity)\n    ({requirements_name} : {spec_name}.requirements {arguments_name}) : Litex.Object :=\n  {body}"
        ));

        let return_type = self.render_fact(&ir.return_check.proposition, &body_context)?;
        let expected_return_type = format!("Litex.In {body} {range}");
        if return_type != expected_return_type {
            return Err(universal_error(
                &ir.return_check.proposition.line_file(),
                format!(
                    "named-function return proof changed its checked body or range: expected `{expected_return_type}`, got `{return_type}`"
                ),
            ));
        }
        let return_proof = self.render_proof_term(&ir.return_check, &body_context)?;
        let mut closed_proof_lines = vec![format!(
            "  intro {arguments_name} {length_name} {requirements_name}"
        )];
        for step in local_proof_steps.iter() {
            closed_proof_lines.push(render_local_proof_step(step));
        }
        closed_proof_lines.push(format!("  change {expected_return_type}"));
        closed_proof_lines.push(format!("  exact {return_proof}"));
        self.declarations.push(format!(
            "theorem {closed_name} :\n    ∀ {arguments_name} {length_name} {requirements_name},\n      Litex.In\n        ({body_name} {arguments_name} {length_name} {requirements_name})\n        ({spec_name}.range {arguments_name} {length_name} {requirements_name}) := by\n{}",
            closed_proof_lines.join("\n")
        ));
        self.declarations.push(format!(
            "noncomputable def {implementation_name} : Litex.Object :=\n  Litex.functionObject {spec_name} {body_name}"
        ));
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.Object := {implementation_name}"
        ));

        let membership_type = format!("Litex.In {name} (Litex.FnSet {spec})");
        let membership_name = generated_fact_name(ir.membership.fact_id);
        if !self.global_names.insert(membership_name.clone()) {
            return Err(universal_error(
                &ir.membership.proposition.line_file(),
                format!("Lean declaration name `{membership_name}` is already in use"),
            ));
        }
        self.declarations.push(format!(
            "theorem {membership_name} : {membership_type} := by\n  simpa only [{name}, {implementation_name}, {spec_name}] using\n    (Litex.functionObjectInFnSet {spec_name} {body_name} {closed_name})"
        ));
        let membership_binding = GlobalFactBinding {
            theorem_name: membership_name.clone(),
            proposition: ir.membership.proposition.clone(),
            parameter_symbol_ids: Vec::new(),
            parameter_fact_ids: Vec::new(),
            domain_fact_ids: Vec::new(),
        };
        self.global_facts
            .insert(ir.membership.fact_id, membership_binding);
        self.global_function_bindings.insert(
            ir.membership.fact_id,
            FunctionBinding {
                function: ir.function.clone(),
                membership_proof_name: membership_name,
                // A named function is introduced through its implementation
                // `FnSpec`, even when its public type is nondependent.
                uses_fn_space: false,
            },
        );

        let equality_name = generated_fact_name(ir.defining_equality.fact_id);
        if !self.global_names.insert(equality_name.clone()) {
            return Err(universal_error(
                &ir.defining_equality.proposition.line_file(),
                format!("Lean declaration name `{equality_name}` is already in use"),
            ));
        }
        self.declarations.push(format!(
            "theorem {equality_name} : {name} = {implementation_name} := by\n  rfl"
        ));
        self.global_facts.insert(
            ir.defining_equality.fact_id,
            GlobalFactBinding {
                theorem_name: equality_name,
                proposition: ir.defining_equality.proposition.clone(),
                parameter_symbol_ids: Vec::new(),
                parameter_fact_ids: Vec::new(),
                domain_fact_ids: Vec::new(),
            },
        );
        self.named_function_helpers.insert(
            ir.name.clone(),
            NamedFunctionHelpers {
                implementation_name,
                body_name,
                body_object_definition_names: Vec::new(),
            },
        );
        Ok(())
    }

    fn emit_have_tuple(&mut self, ir: &LitexToLeanHaveTupleStmtIr) -> Result<(), RuntimeError> {
        if ir.dimension_checks.len() != 2
            || ir.stored_facts.len() != 3
            || ir.stored_facts[0].role != LitexToLeanStoredTupleFactRoleIr::IsTuple
            || ir.stored_facts[1].role != LitexToLeanStoredTupleFactRoleIr::Dimension
            || ir.stored_facts[2].role != LitexToLeanStoredTupleFactRoleIr::Coordinate
        {
            return Err(universal_error(
                &ir.stored_facts
                    .first()
                    .map(|fact| fact.proposition.line_file())
                    .unwrap_or_else(default_line_file),
                "indexed tuple changed its two checks or three ordered stored-effect roles",
            ));
        }
        let name = lean_name(&ir.name);
        let value_name = format!("__{name}_value");
        let positive_name = format!("__{name}_dim_pos");
        let at_least_two_name = format!("__{name}_dim_ge2");
        for declaration_name in [
            value_name.as_str(),
            positive_name.as_str(),
            at_least_two_name.as_str(),
            name.as_str(),
        ] {
            if !self.global_names.insert(declaration_name.to_string()) {
                return Err(universal_error(
                    &ir.stored_facts[0].proposition.line_file(),
                    format!("Lean declaration name `{declaration_name}` is already in use"),
                ));
            }
        }
        let context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            ..RenderContext::default()
        };
        let dimension = self.render_obj_ir(&ir.dimension, &context)?;
        let expected_checks = [
            format!("Litex.In {dimension} Litex.NPos"),
            format!("Litex.Le 2 {dimension}"),
        ];
        let mut check_proofs = Vec::with_capacity(2);
        for (check, expected) in ir.dimension_checks.iter().zip(expected_checks.iter()) {
            if self.render_fact(&check.proposition, &context)? != *expected {
                return Err(universal_error(
                    &check.proposition.line_file(),
                    "indexed tuple dimension check changed its retained role",
                ));
            }
            check_proofs.push(self.render_proof_term(check, &context)?);
        }
        self.declarations.push(format!(
            "theorem {positive_name} : {} := by\n  exact {}",
            expected_checks[0], check_proofs[0]
        ));
        self.declarations.push(format!(
            "theorem {at_least_two_name} : {} := by\n  exact {}",
            expected_checks[1], check_proofs[1]
        ));

        let index_name = format!("__index{}", ir.index_symbol_id.value());
        let mut value_context = context.clone();
        value_context
            .symbol_names
            .insert(ir.index_symbol_id, index_name.clone());
        let value = self.render_obj_ir(&ir.value, &value_context)?;
        self.declarations.push(format!(
            "noncomputable def {value_name} ({index_name} : Litex.Object) : Litex.Object :=\n  {value}"
        ));
        self.declarations.push(format!(
            "noncomputable def {name} : Litex.Object :=\n  Litex.tupleObject {dimension} {value_name}"
        ));

        let mut named_context = context.clone();
        named_context
            .symbol_names
            .insert(ir.symbol_id, name.clone());
        let mut seen_ids = HashSet::new();
        for stored in ir.stored_facts.iter() {
            if !seen_ids.insert(stored.fact_id) {
                return Err(universal_error(
                    &stored.proposition.line_file(),
                    "indexed tuple reused one FactId for multiple stored effects",
                ));
            }
            let theorem_name = generated_fact_name(stored.fact_id);
            if !self.global_names.insert(theorem_name.clone()) {
                return Err(universal_error(
                    &stored.proposition.line_file(),
                    format!("Lean declaration name `{theorem_name}` is already in use"),
                ));
            }
            let theorem_type = self.render_fact(&stored.proposition, &named_context)?;
            let proof = match stored.role {
                LitexToLeanStoredTupleFactRoleIr::IsTuple => {
                    if theorem_type != format!("Litex.IsTuple {name}") {
                        return Err(universal_error(
                            &stored.proposition.line_file(),
                            "indexed tuple sethood effect changed its target",
                        ));
                    }
                    format!(
                        "by\n  unfold {name}\n  exact Litex.tupleObjectIsTuple {dimension} {value_name}"
                    )
                }
                LitexToLeanStoredTupleFactRoleIr::Dimension => {
                    let expected = format!("(Litex.tupleDim {name}) = {dimension}");
                    if theorem_type != expected {
                        return Err(universal_error(
                            &stored.proposition.line_file(),
                            "indexed tuple dimension effect changed its target",
                        ));
                    }
                    format!(
                        "by\n  simpa only [{name}] using\n    (Litex.tupleObject_dim {dimension} {value_name})"
                    )
                }
                LitexToLeanStoredTupleFactRoleIr::Coordinate => format!(
                    "by\n  intro __coord __coord_in_range\n  simpa only [{name}, {value_name}] using\n    (Litex.tupleObject_at {dimension} {value_name} __coord)"
                ),
            };
            self.declarations.push(format!(
                "theorem {theorem_name} : {theorem_type} :=\n{proof}"
            ));
            self.global_facts.insert(
                stored.fact_id,
                GlobalFactBinding {
                    theorem_name,
                    proposition: stored.proposition.clone(),
                    parameter_symbol_ids: Vec::new(),
                    parameter_fact_ids: Vec::new(),
                    domain_fact_ids: Vec::new(),
                },
            );
        }
        Ok(())
    }

    fn emit_proof(
        &mut self,
        facts: &[LitexToLeanFactIr],
        inferred_facts: &[LitexToLeanFactIr],
        certificate: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<(), RuntimeError> {
        for fact in facts.iter().chain(inferred_facts.iter()) {
            self.emit_direct_stored_fact(fact, certificate)?;
        }
        Ok(())
    }

    fn emit_fact_statement(&mut self, ir: &LitexToLeanFactStatementIr) -> Result<(), RuntimeError> {
        if ir.source.fact_id.is_some() {
            if !ir.stored_projections.is_empty() {
                return Err(universal_error(
                    &ir.source.proposition.line_file(),
                    "a completely stored Fact statement also retained projected facts",
                ));
            }
            self.emit_stored_fact(&ir.source, &ir.well_definedness)?;
        } else {
            self.emit_projected_forall(
                &ir.source.proposition,
                &ir.stored_projections,
                &ir.inferred_facts,
                &ir.well_definedness,
            )?;
            return Ok(());
        }
        for inferred in ir.inferred_facts.iter() {
            self.emit_stored_fact(inferred, &ir.well_definedness)?;
        }
        Ok(())
    }

    fn emit_named_fact(
        &mut self,
        fact: &LitexToLeanFactIr,
        proof: String,
    ) -> Result<(), RuntimeError> {
        let fact_id = fact.fact_id.ok_or_else(|| {
            universal_error(
                &fact.proposition.line_file(),
                "a stored statement effect has no FactId",
            )
        })?;
        if self.fact_id_is_already_emitted(fact)? {
            return Ok(());
        }
        let theorem_name = generated_fact_name(fact_id);
        let theorem_type = self.render_top_level_fact_type(&fact.proposition)?;
        self.declarations.push(format!(
            "{} := {proof}",
            render_declaration_head(&format!("theorem {theorem_name}"), &theorem_type)
        ));
        self.register_global_function_binding(fact_id, &fact.proposition, theorem_name.clone())?;
        self.global_facts.insert(
            fact_id,
            GlobalFactBinding {
                theorem_name,
                proposition: fact.proposition.clone(),
                parameter_symbol_ids: Vec::new(),
                parameter_fact_ids: Vec::new(),
                domain_fact_ids: Vec::new(),
            },
        );
        Ok(())
    }

    fn emit_trust(&mut self, ir: &LitexToLeanTrustStmtIr) -> Result<(), RuntimeError> {
        for (index, fact) in ir.facts.iter().enumerate() {
            if !matches!(fact.proof, LitexToLeanFactProofIr::Trusted) {
                return Err(universal_error(
                    &fact.proposition.line_file(),
                    "explicit trust statement lost its trusted proof marker",
                ));
            }
            if self.fact_id_is_already_emitted(fact)? {
                continue;
            }
            let theorem_name = fact
                .fact_id
                .map(generated_fact_name)
                .unwrap_or_else(|| format!("__trusted_fact{}", index + 1));
            let theorem_type = self.render_top_level_fact_type(&fact.proposition)?;
            self.declarations.push(render_declaration_head(
                &format!("axiom {theorem_name}"),
                &theorem_type,
            ));
            if let Some(fact_id) = fact.fact_id {
                self.register_global_function_binding(
                    fact_id,
                    &fact.proposition,
                    theorem_name.clone(),
                )?;
                self.global_facts.insert(
                    fact_id,
                    GlobalFactBinding {
                        theorem_name,
                        proposition: fact.proposition.clone(),
                        parameter_symbol_ids: Vec::new(),
                        parameter_fact_ids: Vec::new(),
                        domain_fact_ids: Vec::new(),
                    },
                );
            }
        }
        let certificate = LitexToLeanWellDefinednessCertificateIr::default();
        for inferred in ir.inferred_facts.iter() {
            self.emit_direct_stored_fact(inferred, &certificate)?;
        }
        Ok(())
    }

    fn register_global_function_binding(
        &mut self,
        fact_id: FactId,
        proposition: &Fact,
        membership_proof_name: String,
    ) -> Result<(), RuntimeError> {
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Ok(());
        };
        let Obj::FnSet(function_set) = &membership.set else {
            return Ok(());
        };
        let function = LitexToLeanFunctionTypeIr::lower(function_set)
            .map_err(|message| universal_error(&proposition.line_file(), message))?;
        if let Some(existing) = self.global_function_bindings.get(&fact_id) {
            if existing.function != function
                || existing.membership_proof_name != membership_proof_name
            {
                return Err(universal_error(
                    &proposition.line_file(),
                    format!(
                        "function membership FactId {} was registered with two different Lean contracts",
                        fact_id.value()
                    ),
                ));
            }
            return Ok(());
        }
        let uses_fn_space = function_ir_uses_fn_space(&function);
        self.global_function_bindings.insert(
            fact_id,
            FunctionBinding {
                function,
                membership_proof_name,
                uses_fn_space,
            },
        );
        Ok(())
    }

    fn render_top_level_fact_type(&self, fact: &Fact) -> Result<String, RuntimeError> {
        match fact {
            Fact::ForallFact(forall) => {
                let mut context = RenderContext {
                    function_bindings: self.global_function_bindings.clone(),
                    forall_depth: Some(0),
                    ..RenderContext::default()
                };
                let mut binders = Vec::new();
                let mut parameter_index = 0;
                for group in forall.params_def_with_type.groups.iter() {
                    for binding in group.params.iter() {
                        let name = lean_name(binding.name());
                        context.symbol_names.insert(binding.id(), name.clone());
                        binders.push(format!("({name} : Litex.Object)"));
                        parameter_index += 1;
                        binders.push(format!(
                            "({} : {})",
                            generated_hypothesis_name(0, parameter_index),
                            self.render_parameter_requirement(&name, &group.param_type, &context,)?
                        ));
                    }
                }
                for (index, domain) in forall.dom_facts.iter().enumerate() {
                    binders.push(format!(
                        "({} : {})",
                        generated_hypothesis_name(0, parameter_index + index + 1),
                        self.render_fact(&domain.clone().into(), &context)?
                    ));
                }
                let mut conclusions = Vec::new();
                for conclusion in forall.then_facts.iter() {
                    conclusions.push(self.render_fact(&conclusion.clone().to_fact(), &context)?);
                }
                let conclusion = right_associated(conclusions, " ∧ ", "True");
                if binders.is_empty() {
                    Ok(conclusion)
                } else {
                    Ok(render_top_level_forall_type(&binders, &conclusion))
                }
            }
            _ => self.render_fact(
                fact,
                &RenderContext {
                    function_bindings: self.global_function_bindings.clone(),
                    ..RenderContext::default()
                },
            ),
        }
    }

    fn render_parameter_requirement(
        &self,
        name: &str,
        param_type: &ParamType,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match param_type {
            ParamType::Obj(set) => Ok(format!(
                "Litex.In {name} {}",
                self.render_obj(set, context)?
            )),
            ParamType::Set(_) => Ok(format!("Litex.IsSet {name}")),
            ParamType::NonemptySet(_) => Ok(format!("Litex.IsNonemptySet {name}")),
            ParamType::FiniteSet(_) => Ok(format!("Litex.IsFiniteSet {name}")),
        }
    }

    fn render_ir_parameter_requirement(
        &self,
        value: &str,
        param_type: &LitexToLeanParameterTypeIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match param_type {
            LitexToLeanParameterTypeIr::Set => Ok(format!("Litex.IsSet {value}")),
            LitexToLeanParameterTypeIr::MemberOf { set } => Ok(format!(
                "Litex.In {value} {}",
                self.render_obj_ir(set, context)?
            )),
            LitexToLeanParameterTypeIr::NonemptySet => Ok(format!("Litex.IsNonemptySet {value}")),
            LitexToLeanParameterTypeIr::FiniteSet => Ok(format!("Litex.IsFiniteSet {value}")),
            LitexToLeanParameterTypeIr::Unsupported(reason) => Err(universal_error(
                &default_line_file(),
                format!("unsupported concrete prop parameter type: {reason}"),
            )),
        }
    }

    fn emit_projected_forall(
        &mut self,
        source: &Fact,
        facts: &[LitexToLeanFactIr],
        inferred_facts: &[LitexToLeanFactIr],
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<(), RuntimeError> {
        let Fact::ForallFact(source_forall) = source else {
            return Err(universal_error(
                &source.line_file(),
                "projected-forall IR does not retain a forall source",
            ));
        };
        let mut ordered = facts
            .iter()
            .map(|fact| Ok((projection_source_index(source_forall, fact)?, fact)))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        ordered.sort_by_key(|(index, _)| *index);
        for (_, fact) in ordered {
            self.emit_stored_fact(fact, well_definedness)?;
        }
        if !inferred_facts.is_empty() {
            return Err(universal_error(
                &source.line_file(),
                "the universal-object MVP does not yet emit projected-forall inferred facts",
            ));
        }
        Ok(())
    }

    fn emit_stored_fact(
        &mut self,
        fact: &LitexToLeanFactIr,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<(), RuntimeError> {
        let fact_id = fact.fact_id.ok_or_else(|| {
            universal_error(
                &fact.proposition.line_file(),
                "a stored universal-object fact has no FactId",
            )
        })?;
        if self.fact_id_is_already_emitted(fact)? {
            return Ok(());
        }
        let Fact::ForallFact(forall) = &fact.proposition else {
            return self.emit_direct_stored_fact(fact, well_definedness);
        };
        if !matches!(
            fact.proof,
            LitexToLeanFactProofIr::ForallIntroduction { .. }
        ) {
            return self.emit_direct_stored_fact(fact, well_definedness);
        }
        let emission = self.prepare_forall_emission(forall, &fact.proof, well_definedness)?;
        let theorem_name = generated_fact_name(fact_id);
        let conclusion_text = if emission.conclusions.len() == 1 {
            self.render_fact(&emission.conclusions[0].proposition, &emission.context)?
        } else {
            let mut parts = Vec::with_capacity(emission.conclusions.len());
            for conclusion in emission.conclusions.iter() {
                parts.push(self.render_fact(&conclusion.proposition, &emission.context)?);
            }
            right_associated(parts, " ∧ ", "True")
        };
        let mut binders = Vec::with_capacity(emission.binder_names.len());
        for (name, binder_type) in emission
            .binder_names
            .iter()
            .zip(emission.binder_types.iter())
        {
            binders.push(format!("({name} : {binder_type})"));
        }
        let theorem_type = render_top_level_forall_type(&binders, &conclusion_text);
        let mut proof_lines = vec!["by".to_string()];
        if !emission.binder_names.is_empty() {
            proof_lines.push(format!("  intro {}", emission.binder_names.join(" ")));
        }
        for step in emission.local_proof_steps.iter() {
            proof_lines.push(render_local_proof_step(step));
        }
        for inferred in emission.inferred_facts.iter() {
            proof_lines.push(format!(
                "  have {} : {} := by\n    exact {}",
                inferred.name, inferred.proposition, inferred.proof
            ));
        }
        if emission.conclusions.len() == 1 {
            let proof = self.render_proof_term(&emission.conclusions[0], &emission.context)?;
            proof_lines.push(format!("  exact {proof}"));
        } else {
            return Err(universal_error(
                &fact.proposition.line_file(),
                "multi-conclusion stored foralls are not yet emitted as one target theorem",
            ));
        }
        self.declarations.push(format!(
            "{} :=\n{}",
            render_declaration_head(&format!("theorem {theorem_name}"), &theorem_type),
            proof_lines.join("\n")
        ));

        let binding = GlobalFactBinding {
            theorem_name,
            proposition: fact.proposition.clone(),
            parameter_symbol_ids: emission.parameter_symbol_ids,
            parameter_fact_ids: emission.parameter_fact_ids,
            domain_fact_ids: emission.domain_fact_ids,
        };
        self.global_facts.insert(fact_id, binding.clone());
        for conclusion in emission.conclusions {
            if let Some(conclusion_id) = conclusion.fact_id {
                self.global_facts.insert(conclusion_id, binding.clone());
            }
        }
        Ok(())
    }

    fn emit_direct_stored_fact(
        &mut self,
        fact: &LitexToLeanFactIr,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<(), RuntimeError> {
        let fact_id = fact.fact_id.ok_or_else(|| {
            universal_error(
                &fact.proposition.line_file(),
                "a direct stored universal-object fact has no FactId",
            )
        })?;
        if self.fact_id_is_already_emitted(fact)? {
            return Ok(());
        }
        let theorem_name = generated_fact_name(fact_id);
        let mut context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            well_definedness: well_definedness.clone(),
            ..RenderContext::default()
        };
        let mut local_proof_steps = Vec::new();
        self.prepare_local_well_defined_facts_for_fact_type(
            &mut context,
            &fact.proposition,
            &[],
            &[],
            &mut local_proof_steps,
        )?;
        self.prepare_local_well_defined_facts_for_fact_proof(
            &mut context,
            fact,
            &[],
            &[],
            &mut local_proof_steps,
        )?;
        let theorem_type = self.render_fact(&fact.proposition, &context)?;
        let proof = self.render_proof_term(fact, &context)?;
        let mut proof_lines = local_proof_steps
            .iter()
            .map(render_local_proof_step)
            .collect::<Vec<_>>();
        proof_lines.push(format!("  exact {proof}"));
        self.declarations.push(format!(
            "theorem {theorem_name} : {theorem_type} := by\n{}",
            proof_lines.join("\n")
        ));
        self.register_global_function_binding(fact_id, &fact.proposition, theorem_name.clone())?;
        self.global_facts.insert(
            fact_id,
            GlobalFactBinding {
                theorem_name,
                proposition: fact.proposition.clone(),
                parameter_symbol_ids: Vec::new(),
                parameter_fact_ids: Vec::new(),
                domain_fact_ids: Vec::new(),
            },
        );
        Ok(())
    }

    fn fact_id_is_already_emitted(&self, fact: &LitexToLeanFactIr) -> Result<bool, RuntimeError> {
        let Some(fact_id) = fact.fact_id else {
            return Ok(false);
        };
        let Some(existing) = self.global_facts.get(&fact_id) else {
            return Ok(false);
        };
        if existing.proposition.to_string() != fact.proposition.to_string() {
            return Err(universal_error(
                &fact.proposition.line_file(),
                format!(
                    "FactId {fact_id} was reused for a different proposition: emitted `{}` but received `{}`",
                    existing.proposition, fact.proposition
                ),
            ));
        }
        Ok(true)
    }

    fn prepare_forall_emission(
        &mut self,
        forall: &ForallFact,
        proof: &LitexToLeanFactProofIr,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    ) -> Result<ForallEmission, RuntimeError> {
        let LitexToLeanFactProofIr::ForallIntroduction {
            parameter_premises,
            premises,
            inferred_premises,
            conclusions,
        } = proof
        else {
            return Err(universal_error(
                &forall.line_file,
                "a universal-object forall has no forall-introduction evidence",
            ));
        };
        let parameter_count = forall.params_def_with_type.number_of_params();
        if parameter_count != parameter_premises.len() || forall.dom_facts.len() != premises.len() {
            return Err(universal_error(
                &forall.line_file,
                "forall evidence does not match its parameter or domain arity",
            ));
        }

        let mut context = RenderContext {
            function_bindings: self.global_function_bindings.clone(),
            well_definedness: well_definedness.clone(),
            forall_depth: Some(0),
            ..RenderContext::default()
        };
        let mut binder_names = Vec::new();
        let mut binder_types = Vec::new();
        let mut parameter_symbol_ids = Vec::new();
        let mut parameter_fact_ids = Vec::new();
        let mut parameter_index = 0;
        for group in forall.params_def_with_type.groups.iter() {
            for binding in group.params.iter() {
                let name = lean_name(binding.name());
                context.symbol_names.insert(binding.id(), name.clone());
                binder_names.push(name.clone());
                binder_types.push("Litex.Object".to_string());
                parameter_symbol_ids.push(binding.id());

                let premise = &parameter_premises[parameter_index];
                let proof_name = generated_hypothesis_name(0, parameter_index + 1);
                let proof_type = self.render_fact(&premise.fact, &context)?;
                binder_names.push(proof_name.clone());
                binder_types.push(proof_type);
                context
                    .local_fact_names
                    .insert(premise.fact_id, proof_name.clone());
                context
                    .local_fact_propositions
                    .insert(premise.fact_id, premise.fact.clone());
                parameter_fact_ids.push(premise.fact_id);

                if let ParamType::Obj(Obj::FnSet(function_set)) = &group.param_type {
                    let function = LitexToLeanFunctionTypeIr::lower(function_set)
                        .map_err(|message| universal_error(&forall.line_file, message))?;
                    let uses_fn_space = function_ir_uses_fn_space(&function);
                    context.function_bindings.insert(
                        premise.fact_id,
                        FunctionBinding {
                            function,
                            membership_proof_name: proof_name,
                            uses_fn_space,
                        },
                    );
                }
                parameter_index += 1;
            }
        }

        let mut domain_fact_ids = Vec::new();
        let mut local_proof_steps = Vec::new();
        for premise in premises.iter() {
            self.prepare_local_well_defined_facts_for_fact_type(
                &mut context,
                &premise.fact,
                &binder_names,
                &binder_types,
                &mut local_proof_steps,
            )?;
        }
        for (index, premise) in premises.iter().enumerate() {
            let proof_name = generated_hypothesis_name(0, parameter_index + index + 1);
            let proof_type = self.render_fact(&premise.fact, &context)?;
            binder_names.push(proof_name.clone());
            binder_types.push(proof_type);
            context.local_fact_names.insert(premise.fact_id, proof_name);
            context
                .local_fact_propositions
                .insert(premise.fact_id, premise.fact.clone());
            if matches!(premise.fact, Fact::ForallFact(_)) {
                context
                    .local_forall_facts
                    .insert(premise.fact_id, premise.fact.clone());
            }
            domain_fact_ids.push(premise.fact_id);
        }

        let mut inferred_facts = Vec::new();
        for (index, inferred) in inferred_premises.iter().enumerate() {
            let fact_id = inferred.fact_id.ok_or_else(|| {
                universal_error(
                    &inferred.proposition.line_file(),
                    "an inferred forall premise reached emission without a FactId",
                )
            })?;
            self.prepare_local_well_defined_facts_for_fact_type(
                &mut context,
                &inferred.proposition,
                &binder_names,
                &binder_types,
                &mut local_proof_steps,
            )?;
            self.prepare_local_well_defined_facts_for_fact_proof(
                &mut context,
                inferred,
                &binder_names,
                &binder_types,
                &mut local_proof_steps,
            )?;
            let proposition = self.render_fact(&inferred.proposition, &context)?;
            let proof = self.render_proof_term(inferred, &context)?;
            let name = format!("__inferred{index}");
            context.local_fact_names.insert(fact_id, name.clone());
            context
                .local_fact_propositions
                .insert(fact_id, inferred.proposition.clone());
            if matches!(inferred.proposition, Fact::ForallFact(_)) {
                context
                    .local_forall_facts
                    .insert(fact_id, inferred.proposition.clone());
            }
            inferred_facts.push(InferredFactEmission {
                name,
                proposition,
                proof,
            });
        }

        for conclusion in conclusions.iter() {
            self.prepare_local_well_defined_facts_for_fact_type(
                &mut context,
                &conclusion.proposition,
                &binder_names,
                &binder_types,
                &mut local_proof_steps,
            )?;
            self.prepare_local_well_defined_facts_for_fact_proof(
                &mut context,
                conclusion,
                &binder_names,
                &binder_types,
                &mut local_proof_steps,
            )?;
        }

        Ok(ForallEmission {
            context,
            binder_names,
            binder_types,
            parameter_symbol_ids,
            parameter_fact_ids,
            domain_fact_ids,
            local_proof_steps,
            inferred_facts,
            conclusions: conclusions.clone(),
        })
    }

    fn prepare_binder_scope_emissions(
        &mut self,
        context: &RenderContext,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
        binder_names: &[String],
        binder_types: &[String],
    ) -> Result<HashMap<WellDefinedBinderScopeId, BinderScopeEmission>, RuntimeError> {
        let mut scopes = well_definedness.binder_scopes.iter().collect::<Vec<_>>();
        scopes.sort_by_key(|scope| (scope.ambient_scope_ids.len(), scope.scope_id.value()));
        let mut emissions = HashMap::new();
        for scope in scopes {
            let mut emission = if let Some(parent_scope_id) = scope.ambient_scope_ids.last() {
                emissions.get(parent_scope_id).cloned().ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!(
                            "WellDefinedBinderScopeId {} has unavailable ambient scope {}",
                            scope.scope_id.value(),
                            parent_scope_id.value()
                        ),
                    )
                })?
            } else {
                BinderScopeEmission {
                    context: context.clone(),
                    binder_names: binder_names.to_vec(),
                    binder_types: binder_types.to_vec(),
                }
            };
            let Obj::AnonymousFn(source_function) = &scope.owner_object else {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedBinderScopeId {} has unsupported owner `{}`",
                        scope.scope_id.value(),
                        scope.owner_object
                    ),
                ));
            };
            let function = LitexToLeanFunctionTypeIr::lower_anonymous(source_function)
                .map_err(|message| universal_error(&default_line_file(), message))?;
            for (parameter_index, parameter) in function.parameters.iter().enumerate() {
                let name = format!(
                    "__wd_scope{}_arg{}",
                    scope.scope_id.value(),
                    parameter_index + 1
                );
                emission
                    .context
                    .symbol_names
                    .insert(parameter.symbol_id, name.clone());
                emission.binder_names.push(name);
                emission.binder_types.push("Litex.Object".to_string());
            }
            for (premise_index, premise) in scope.premises.iter().enumerate() {
                let proof_name = format!(
                    "__wd_scope{}_premise{}",
                    scope.scope_id.value(),
                    premise_index + 1
                );
                let proof_type = self.render_fact(&premise.proposition, &emission.context)?;
                emission.binder_names.push(proof_name.clone());
                emission.binder_types.push(proof_type);
                emission
                    .context
                    .local_fact_names
                    .insert(premise.fact_id, proof_name);
                emission
                    .context
                    .local_fact_propositions
                    .insert(premise.fact_id, premise.proposition.clone());
            }

            for (inferred_index, inferred) in scope.inferred_premises.iter().enumerate() {
                let fact_id = inferred.fact_id.ok_or_else(|| {
                    universal_error(
                        &inferred.proposition.line_file(),
                        format!(
                            "WellDefinedBinderScopeId {} retained an inferred premise without FactId",
                            scope.scope_id.value()
                        ),
                    )
                })?;
                let key = (scope.scope_id, fact_id);
                let applied_name = if let Some(helper) =
                    self.binder_scope_inferred_helpers.get(&key)
                {
                    apply_scoped_declaration(
                        &helper.theorem_name,
                        &helper.binder_names,
                        &helper.binder_types,
                        &emission.binder_names,
                        &emission.binder_types,
                        &format!("binder-scope inference FactId {}", fact_id.value()),
                    )?
                } else {
                    let theorem_name = format!(
                        "__wd_scope{}_inferred{}_fact{}",
                        scope.scope_id.value(),
                        inferred_index + 1,
                        fact_id.value()
                    );
                    if !self.global_names.insert(theorem_name.clone()) {
                        return Err(universal_error(
                            &inferred.proposition.line_file(),
                            format!("Lean declaration name `{theorem_name}` is already in use"),
                        ));
                    }
                    let proposition = self.render_fact(&inferred.proposition, &emission.context)?;
                    let proof = self.render_proof_term(inferred, &emission.context)?;
                    let binders =
                        render_explicit_binders(&emission.binder_names, &emission.binder_types)?;
                    let theorem_type = render_top_level_forall_type(&binders, &proposition);
                    let theorem_proof = if emission.binder_names.is_empty() {
                        format!("by\n  exact {proof}")
                    } else {
                        format!(
                            "by\n  intro {}\n  exact {proof}",
                            emission.binder_names.join(" ")
                        )
                    };
                    self.declarations.push(format!(
                        "{} :=\n{theorem_proof}",
                        render_declaration_head(&format!("theorem {theorem_name}"), &theorem_type,)
                    ));
                    self.binder_scope_inferred_helpers.insert(
                        key,
                        WellDefinedHelperBinding {
                            theorem_name: theorem_name.clone(),
                            binder_names: emission.binder_names.clone(),
                            binder_types: emission.binder_types.clone(),
                        },
                    );
                    apply_scoped_declaration(
                        &theorem_name,
                        &emission.binder_names,
                        &emission.binder_types,
                        &emission.binder_names,
                        &emission.binder_types,
                        &theorem_name,
                    )?
                };
                emission
                    .context
                    .local_fact_names
                    .insert(fact_id, applied_name);
                emission
                    .context
                    .local_fact_propositions
                    .insert(fact_id, inferred.proposition.clone());
            }
            emissions.insert(scope.scope_id, emission);
        }
        Ok(emissions)
    }

    fn prepare_scoped_well_defined_facts(
        &mut self,
        context: &mut RenderContext,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
        application_occurrence_ids: &HashSet<SourceObjectOccurrenceId>,
        initial_object_proof_ids: &HashSet<WellDefinedObjId>,
        binder_names: &[String],
        binder_types: &[String],
    ) -> Result<(), RuntimeError> {
        if application_occurrence_ids.is_empty() && initial_object_proof_ids.is_empty() {
            return Ok(());
        }
        let mut canonical_proof_ids = initial_object_proof_ids.clone();
        canonical_proof_ids.extend(resolve_source_occurrence_object_ids(
            well_definedness,
            application_occurrence_ids,
            context,
            &default_line_file(),
        )?);
        let mut selected_ids = HashSet::new();
        let mut selected_roles = HashSet::new();
        for requirement in well_definedness.target_requirements.iter() {
            if !application_occurrence_ids.contains(&requirement.source_occurrence_id)
                || !selected_roles.insert((requirement.source_occurrence_id, requirement.role))
            {
                continue;
            }
            canonical_proof_ids.insert(requirement.well_defined_obj_id);
            selected_ids.insert(requirement.well_defined_fact_id);
        }

        let objects_by_id = well_definedness
            .objects
            .iter()
            .map(|object| (object.well_defined_obj_id, object))
            .collect::<HashMap<_, _>>();
        let mut pending_object_ids = canonical_proof_ids.into_iter().collect::<Vec<_>>();
        let mut selected_object_ids = HashSet::new();
        add_well_defined_object_proof_closure(
            &objects_by_id,
            &mut pending_object_ids,
            &mut selected_object_ids,
            &mut selected_ids,
        )?;

        // Audit facts can mention another certificate-bearing arithmetic cache node
        // (for example a normalization witness). Preserve those checks too by
        // closing the selected DAG over every retained fact proof tree.
        loop {
            let mut referenced_occurrence_ids = HashSet::new();
            for fact in well_definedness
                .facts
                .iter()
                .filter(|fact| selected_ids.contains(&fact.well_defined_fact_id))
            {
                collect_proof_carrying_object_occurrence_ids_from_fact(
                    &fact.expected_proposition,
                    &mut referenced_occurrence_ids,
                )?;
                collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                    &fact.fact,
                    &mut referenced_occurrence_ids,
                )?;
            }
            let mut added = false;
            for source_occurrence_id in referenced_occurrence_ids {
                if context
                    .well_defined_object_ids
                    .contains_key(&source_occurrence_id)
                {
                    continue;
                }
                let proof_ids = resolve_source_occurrence_object_ids(
                    well_definedness,
                    &HashSet::from([source_occurrence_id]),
                    context,
                    &default_line_file(),
                )?;
                pending_object_ids.extend(proof_ids);
                added = true;
            }
            if !added {
                break;
            }
            add_well_defined_object_proof_closure(
                &objects_by_id,
                &mut pending_object_ids,
                &mut selected_object_ids,
                &mut selected_ids,
            )?;
        }

        for selected_id in selected_ids.iter() {
            if !well_definedness
                .facts
                .iter()
                .any(|fact| fact.well_defined_fact_id == *selected_id)
            {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedFactId {} is missing from its frozen compiler certificate",
                        selected_id.value()
                    ),
                ));
            }
        }

        let binder_scope_emissions = self.prepare_binder_scope_emissions(
            context,
            well_definedness,
            binder_names,
            binder_types,
        )?;

        let mut pending = well_definedness
            .facts
            .iter()
            .filter(|fact| selected_ids.contains(&fact.well_defined_fact_id))
            .collect::<Vec<_>>();
        pending.sort_by_key(|fact| fact.well_defined_fact_id.value());
        for fact in pending.iter() {
            if !facts_are_canonically_equal(&fact.expected_proposition, &fact.fact.proposition)? {
                return Err(universal_error(
                    &fact.expected_proposition.line_file(),
                    format!(
                        "WellDefinedFactId {} changed proposition during universal-object emission",
                        fact.well_defined_fact_id.value()
                    ),
                ));
            }
        }

        let mut remaining = pending;
        loop {
            let mut next = Vec::new();
            let mut made_progress = false;
            for fact in remaining {
                let (mut fact_context, fact_binder_names, fact_binder_types) =
                    if let Some(scope_id) = fact.ambient_binder_scope_ids.last() {
                        let emission = binder_scope_emissions.get(scope_id).ok_or_else(|| {
                            universal_error(
                                &fact.expected_proposition.line_file(),
                                format!(
                                    "WellDefinedFactId {} requires unavailable binder scope {}",
                                    fact.well_defined_fact_id.value(),
                                    scope_id.value()
                                ),
                            )
                        })?;
                        (
                            emission.context.clone(),
                            emission.binder_names.clone(),
                            emission.binder_types.clone(),
                        )
                    } else {
                        (
                            context.clone(),
                            binder_names.to_vec(),
                            binder_types.to_vec(),
                        )
                    };
                for (fact_id, helper) in self.well_defined_helpers.iter() {
                    if let Ok(applied_name) = apply_scoped_declaration(
                        &helper.theorem_name,
                        &helper.binder_names,
                        &helper.binder_types,
                        &fact_binder_names,
                        &fact_binder_types,
                        &format!("WellDefinedFactId {}", fact_id.value()),
                    ) {
                        fact_context
                            .well_defined_fact_names
                            .insert(*fact_id, applied_name);
                    }
                }
                if let Some(helper) = self.well_defined_helpers.get(&fact.well_defined_fact_id) {
                    if let Ok(applied_name) = apply_scoped_declaration(
                        &helper.theorem_name,
                        &helper.binder_names,
                        &helper.binder_types,
                        &fact_binder_names,
                        &fact_binder_types,
                        &format!("WellDefinedFactId {}", fact.well_defined_fact_id.value()),
                    ) {
                        fact_context
                            .well_defined_fact_names
                            .insert(fact.well_defined_fact_id, applied_name.clone());
                        if fact.ambient_binder_scope_ids.is_empty() {
                            context
                                .well_defined_fact_names
                                .insert(fact.well_defined_fact_id, applied_name);
                        }
                        made_progress = true;
                        continue;
                    }
                }
                let rendered = self
                    .render_fact(&fact.expected_proposition, &fact_context)
                    .and_then(|proof_type| {
                        self.render_proof_term(&fact.fact, &fact_context)
                            .map(|proof| (proof_type, proof))
                    });
                match rendered {
                    Ok((proof_type, proof)) => {
                        let name = well_defined_fact_name(&fact_context, fact.well_defined_fact_id);
                        let binders =
                            render_explicit_binders(&fact_binder_names, &fact_binder_types)?;
                        let helper_type = render_top_level_forall_type(&binders, &proof_type);
                        let helper_proof = if fact_binder_names.is_empty() {
                            format!("by\n  exact {proof}")
                        } else {
                            format!(
                                "by\n  intro {}\n  exact {proof}",
                                fact_binder_names.join(" ")
                            )
                        };
                        self.declarations.push(format!(
                            "{} :=\n{helper_proof}",
                            render_declaration_head(&format!("theorem {name}"), &helper_type)
                        ));
                        self.well_defined_helpers.insert(
                            fact.well_defined_fact_id,
                            WellDefinedHelperBinding {
                                theorem_name: name.clone(),
                                binder_names: fact_binder_names.clone(),
                                binder_types: fact_binder_types.clone(),
                            },
                        );
                        let applied_name = apply_scoped_declaration(
                            &name,
                            &fact_binder_names,
                            &fact_binder_types,
                            &fact_binder_names,
                            &fact_binder_types,
                            &name,
                        )?;
                        if fact.ambient_binder_scope_ids.is_empty() {
                            context
                                .well_defined_fact_names
                                .insert(fact.well_defined_fact_id, applied_name);
                        }
                        made_progress = true;
                    }
                    Err(_) => next.push(fact),
                }
            }
            if next.is_empty() {
                break;
            }
            if !made_progress {
                let blocked = next
                    .iter()
                    .map(|fact| fact.well_defined_fact_id.value().to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let first_error = self
                    .render_fact(&next[0].expected_proposition, context)
                    .and_then(|_| self.render_proof_term(&next[0].fact, context))
                    .expect_err("a blocked WD fact must still fail on diagnostic replay");
                return Err(universal_error(
                    &next[0].expected_proposition.line_file(),
                    format!(
                        "could not replay selected well-defined facts [{blocked}] in dependency order: {}",
                        first_error.trace_message()
                    ),
                ));
            }
            remaining = next;
        }
        self.emit_scoped_well_defined_objects(
            context,
            &objects_by_id,
            &selected_object_ids,
            binder_names,
            binder_types,
            &binder_scope_emissions,
        )?;
        Ok(())
    }

    fn emit_anonymous_function_object(
        &mut self,
        object: &LitexToLeanWellDefinednessObjectIr,
        object_context: &RenderContext,
        available_binder_names: &[String],
        available_binder_types: &[String],
        binder_scope_emissions: &HashMap<WellDefinedBinderScopeId, BinderScopeEmission>,
    ) -> Result<GlobalObjectBinding, RuntimeError> {
        let Obj::AnonymousFn(source_function) = &object.source_object else {
            return Err(universal_error(
                &default_line_file(),
                "anonymous-function emitter received a non-anonymous WD object",
            ));
        };
        let scope_id = object.owned_binder_scope_id.ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!(
                    "anonymous-function obj_{} has no owned binder scope",
                    object.well_defined_obj_id.value()
                ),
            )
        })?;
        let scope = object_context
            .well_definedness
            .binder_scopes
            .iter()
            .find(|scope| scope.scope_id == scope_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "anonymous-function obj_{} owns missing binder scope {}",
                        object.well_defined_obj_id.value(),
                        scope_id.value()
                    ),
                )
            })?;
        let scope_emission = binder_scope_emissions.get(&scope_id).ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!(
                    "anonymous-function obj_{} cannot emit binder scope {}",
                    object.well_defined_obj_id.value(),
                    scope_id.value()
                ),
            )
        })?;
        let anonymous = LitexToLeanAnonymousFunctionIr {
            source_occurrence_id: source_function.source_occurrence_id,
            semantic_key: obj_equality_key(&object.source_object),
            function: LitexToLeanFunctionTypeIr::lower_anonymous(source_function)
                .map_err(|message| universal_error(&default_line_file(), message))?,
            body: Box::new(
                LitexToLeanObjectIr::lower(source_function.equal_to.as_ref())
                    .map_err(|message| universal_error(&default_line_file(), message))?,
            ),
        };
        let expected_requirement_count =
            anonymous.function.parameters.len() + anonymous.function.domain_facts.len();
        if scope.premises.len() != expected_requirement_count {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "anonymous-function obj_{} retained {} binder premises for {} source requirements",
                    object.well_defined_obj_id.value(),
                    scope.premises.len(),
                    expected_requirement_count
                ),
            ));
        }
        let expected_scope_binder_count = available_binder_names.len()
            + anonymous.function.parameters.len()
            + scope.premises.len();
        if scope_emission.binder_names.len() != expected_scope_binder_count
            || scope_emission.binder_types.len() != expected_scope_binder_count
            || scope_emission.binder_names[..available_binder_names.len()]
                != *available_binder_names
        {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "anonymous-function obj_{} changed its emitted binder telescope",
                    object.well_defined_obj_id.value()
                ),
            ));
        }

        let (object_binder_names, object_binder_types) = object_declaration_binders(
            &object.source_object,
            object_context,
            available_binder_names,
            available_binder_types,
        )?;
        let lean_binders = render_explicit_binders(&object_binder_names, &object_binder_types)?;
        let object_id = object.well_defined_obj_id.value();
        let name = format!("__obj{object_id}");
        let spec_name = format!("__obj{object_id}_spec");
        let body_name = format!("__obj{object_id}_body");
        let closed_name = format!("__obj{object_id}_closed");
        let membership_name = format!("__obj{object_id}_in_fn_space");
        for declaration_name in [
            spec_name.as_str(),
            body_name.as_str(),
            closed_name.as_str(),
            name.as_str(),
            membership_name.as_str(),
        ] {
            if !self.global_names.insert(declaration_name.to_string()) {
                return Err(universal_error(
                    &default_line_file(),
                    format!("Lean declaration name `{declaration_name}` is already in use"),
                ));
            }
        }

        let declaration_head = |declaration_name: &str| {
            if lean_binders.is_empty() {
                declaration_name.to_string()
            } else {
                format!("{declaration_name} {}", lean_binders.join(" "))
            }
        };
        let spec = self.render_function_spec(&anonymous.function, object_context)?;
        self.declarations.push(format!(
            "noncomputable def {} : Litex.FnSpec :=\n  {spec}",
            declaration_head(&spec_name)
        ));
        let applied_spec = apply_scoped_declaration(
            &spec_name,
            &object_binder_names,
            &object_binder_types,
            &object_binder_names,
            &object_binder_types,
            &spec_name,
        )?;

        let body_child = object
            .child_uses
            .iter()
            .filter(|child| child.role == WellDefinedObjChildRole::BinderBody)
            .collect::<Vec<_>>();
        if body_child.len() != 1 {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "anonymous-function obj_{object_id} retained {} body children; expected exactly one",
                    body_child.len()
                ),
            ));
        }
        let arguments_name = format!("__obj{object_id}_arg");
        let length_name = format!("__obj{object_id}_arg_len");
        let requirements_name = format!("__obj{object_id}_arg_req");
        let mut body_substitutions = HashMap::new();
        for name in available_binder_names {
            body_substitutions.insert(name.clone(), name.clone());
        }
        let mut body_context = object_context.clone();
        for (parameter_index, parameter) in anonymous.function.parameters.iter().enumerate() {
            body_substitutions.insert(
                scope_emission.binder_names[available_binder_names.len() + parameter_index].clone(),
                format!("(Litex.arg {arguments_name} {parameter_index})"),
            );
            body_context.symbol_names.insert(
                parameter.symbol_id,
                format!("(Litex.arg {arguments_name} {parameter_index})"),
            );
        }
        // The constructor consumes only the proof-free body value.  Its WD
        // child certificate is replayed below in `closed`; proof binders must
        // never become arguments of this object definition.
        let body_value = self.render_obj_ir(anonymous.body.as_ref(), &body_context)?;
        let body_prefix = if lean_binders.is_empty() {
            body_name.clone()
        } else {
            format!("{body_name} {}", lean_binders.join(" "))
        };
        let body_head = format!(
            "{body_prefix} ({arguments_name} : List Litex.Object) \
             (__arg_len : {arguments_name}.length = ({applied_spec}).arity) \
             (__arg_req : ({applied_spec}).requirements {arguments_name})"
        );
        self.declarations.push(format!(
            "noncomputable def {body_head} : Litex.Object :=\n  {body_value}"
        ));
        let applied_body = apply_scoped_declaration(
            &body_name,
            &object_binder_names,
            &object_binder_types,
            &object_binder_names,
            &object_binder_types,
            &body_name,
        )?;

        let mut closed_substitutions = body_substitutions.clone();
        let premise_binder_offset =
            available_binder_names.len() + anonymous.function.parameters.len();
        for premise_index in 0..scope.premises.len() {
            closed_substitutions.insert(
                scope_emission.binder_names[premise_binder_offset + premise_index].clone(),
                dependent_requirement_projection(&requirements_name, premise_index),
            );
        }
        let mut closed_context = object_context.clone();
        for (parameter_index, parameter) in anonymous.function.parameters.iter().enumerate() {
            closed_context.symbol_names.insert(
                parameter.symbol_id,
                format!("(Litex.arg {arguments_name} {parameter_index})"),
            );
        }
        for (premise_index, premise) in scope.premises.iter().enumerate() {
            let proof = dependent_requirement_projection(&requirements_name, premise_index);
            closed_context
                .local_fact_names
                .insert(premise.fact_id, proof);
            closed_context
                .local_fact_propositions
                .insert(premise.fact_id, premise.proposition.clone());
        }
        for child in object.child_uses.iter() {
            let binding = self.global_objects.get(&child.obj_id).ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "anonymous-function obj_{object_id} cannot resolve child obj_{} at role {:?}",
                        child.obj_id.value(),
                        child.role
                    ),
                )
            })?;
            if let Ok(child_name) = apply_scoped_declaration_with_substitutions(
                &binding.name,
                &binding.binder_names,
                &binding.binder_types,
                &closed_substitutions,
                &format!("anonymous-function obj_{object_id} child"),
            ) {
                closed_context
                    .well_defined_object_names
                    .insert(child.obj_id, child_name);
                if let Some(source_occurrence_id) = child.source_object.source_occurrence_id() {
                    closed_context
                        .well_defined_object_ids
                        .insert(source_occurrence_id, child.obj_id);
                }
            }
        }

        let requirement = object.target_requirements.first().ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!("anonymous-function obj_{object_id} has no return-closure requirement"),
            )
        })?;
        if object.target_requirements.len() != 1 {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "anonymous-function obj_{object_id} retained {} return-closure requirements",
                    object.target_requirements.len()
                ),
            ));
        }
        let helper = self
            .well_defined_helpers
            .get(&requirement.well_defined_fact_id)
            .ok_or_else(|| {
                universal_error(
                    &requirement.expected_proposition.line_file(),
                    format!(
                        "anonymous-function obj_{object_id} cannot resolve WellDefinedFactId {}",
                        requirement.well_defined_fact_id.value()
                    ),
                )
            })?;
        let closure_proof = apply_scoped_declaration_with_substitutions(
            &helper.theorem_name,
            &helper.binder_names,
            &helper.binder_types,
            &closed_substitutions,
            &format!("anonymous-function obj_{object_id} closure"),
        )?;
        let body_at_arguments =
            format!("({applied_body} {arguments_name} {length_name} {requirements_name})");
        let range_at_arguments =
            format!("(({applied_spec}).range {arguments_name} {length_name} {requirements_name})");
        let expected_target = format!("Litex.In {body_at_arguments} {range_at_arguments}");
        let proof_tail = match requirement.role {
            WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
                let replay_target =
                    self.render_fact(&requirement.expected_proposition, &closed_context)?;
                format!("  change {replay_target}\n  exact {closure_proof}")
            }
            WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
                parameter_group_index,
                parameter_index,
            } => {
                let mut flat_parameter_index = parameter_index;
                for group in source_function
                    .body
                    .params_def_with_set
                    .iter()
                    .take(parameter_group_index)
                {
                    flat_parameter_index += group.params.len();
                }
                let premise_index = scope
                    .premises
                    .iter()
                    .position(|premise| {
                        premise.role
                            == WellDefinedBinderPremiseRole::ParameterMembership {
                                parameter_group_index,
                                parameter_index,
                            }
                    })
                    .ok_or_else(|| {
                        universal_error(
                            &requirement.expected_proposition.line_file(),
                            "anonymous-function subset route lost its parameter membership premise",
                        )
                    })?;
                let parameter_proof =
                    dependent_requirement_projection(&requirements_name, premise_index);
                let parameter = format!("(Litex.arg {arguments_name} {flat_parameter_index})");
                format!(
                    "  change Litex.In {parameter} {range_at_arguments}\n  exact ({closure_proof}) {parameter} ({parameter_proof})"
                )
            }
            _ => {
                return Err(universal_error(
                    &requirement.expected_proposition.line_file(),
                    "anonymous-function return closure retained an incompatible requirement role",
                ))
            }
        };
        let closed_type = format!(
            "∀ ({arguments_name} : List Litex.Object)\n      ({length_name} : {arguments_name}.length = ({applied_spec}).arity)\n      ({requirements_name} : ({applied_spec}).requirements {arguments_name}),\n      {expected_target}"
        );
        let closed_proof =
            format!("by\n  intro {arguments_name} {length_name} {requirements_name}\n{proof_tail}");
        self.declarations.push(format!(
            "theorem {} :\n    {closed_type} :=\n{closed_proof}",
            declaration_head(&closed_name)
        ));
        let applied_closed = apply_scoped_declaration(
            &closed_name,
            &object_binder_names,
            &object_binder_types,
            &object_binder_names,
            &object_binder_types,
            &closed_name,
        )?;
        self.declarations.push(format!(
            "noncomputable def {} : Litex.Object :=\n  Litex.functionObject {applied_spec} {applied_body}",
            declaration_head(&name)
        ));
        let applied_object = apply_scoped_declaration(
            &name,
            &object_binder_names,
            &object_binder_types,
            &object_binder_names,
            &object_binder_types,
            &name,
        )?;
        self.declarations.push(format!(
            "theorem {} :\n    Litex.In {applied_object} (Litex.FnSet {applied_spec}) := by\n  unfold {name}\n  exact Litex.functionObjectInFnSet {applied_spec} {applied_body} {applied_closed}",
            declaration_head(&membership_name)
        ));

        Ok(GlobalObjectBinding {
            name,
            source_object: object.source_object.clone(),
            binder_names: object_binder_names,
            binder_types: object_binder_types,
            applicable_name: None,
            result_membership_name: None,
            function_membership_name: Some(membership_name),
        })
    }

    fn emit_scoped_well_defined_objects(
        &mut self,
        context: &mut RenderContext,
        objects_by_id: &HashMap<WellDefinedObjId, &LitexToLeanWellDefinednessObjectIr>,
        selected_object_ids: &HashSet<WellDefinedObjId>,
        binder_names: &[String],
        binder_types: &[String],
        binder_scope_emissions: &HashMap<WellDefinedBinderScopeId, BinderScopeEmission>,
    ) -> Result<(), RuntimeError> {
        let mut remaining = selected_object_ids.iter().copied().collect::<Vec<_>>();
        remaining.sort_by_key(|obj_id| obj_id.value());
        while !remaining.is_empty() {
            let mut next = Vec::new();
            let mut made_progress = false;
            for obj_id in remaining {
                let object = objects_by_id.get(&obj_id).ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!(
                            "WellDefinedObjId {} has no frozen object record",
                            obj_id.value()
                        ),
                    )
                })?;
                let (mut object_context, available_binder_names, available_binder_types) =
                    if let Some(scope_id) = object.ambient_binder_scope_ids.last() {
                        let emission = binder_scope_emissions.get(scope_id).ok_or_else(|| {
                            universal_error(
                                &default_line_file(),
                                format!(
                                    "obj_{} requires unavailable binder scope {}",
                                    obj_id.value(),
                                    scope_id.value()
                                ),
                            )
                        })?;
                        (
                            emission.context.clone(),
                            emission.binder_names.clone(),
                            emission.binder_types.clone(),
                        )
                    } else {
                        (
                            context.clone(),
                            binder_names.to_vec(),
                            binder_types.to_vec(),
                        )
                    };
                for (fact_id, helper) in self.well_defined_helpers.iter() {
                    if let Ok(applied_name) = apply_scoped_declaration(
                        &helper.theorem_name,
                        &helper.binder_names,
                        &helper.binder_types,
                        &available_binder_names,
                        &available_binder_types,
                        &format!("WellDefinedFactId {}", fact_id.value()),
                    ) {
                        object_context
                            .well_defined_fact_names
                            .insert(*fact_id, applied_name);
                    }
                }
                if let Some(binding) = self.global_objects.get(&obj_id) {
                    if obj_equality_key(&binding.source_object)
                        != obj_equality_key(&object.source_object)
                    {
                        return Err(universal_error(
                            &default_line_file(),
                            format!(
                                "WellDefinedObjId {} was reused for a different source object",
                                obj_id.value()
                            ),
                        ));
                    }
                    let object_name = apply_scoped_declaration(
                        &binding.name,
                        &binding.binder_names,
                        &binding.binder_types,
                        &available_binder_names,
                        &available_binder_types,
                        &format!("obj_{}", obj_id.value()),
                    )?;
                    object_context
                        .well_defined_object_names
                        .insert(obj_id, object_name.clone());
                    if object.ambient_binder_scope_ids.is_empty() {
                        context
                            .well_defined_object_names
                            .insert(obj_id, object_name);
                    }
                    if let Some(applicable_name) = &binding.applicable_name {
                        let applicable_name = apply_scoped_declaration(
                            applicable_name,
                            &binding.binder_names,
                            &binding.binder_types,
                            &available_binder_names,
                            &available_binder_types,
                            &format!("obj_{}_applicable", obj_id.value()),
                        )?;
                        object_context
                            .well_defined_applicable_names
                            .insert(obj_id, applicable_name.clone());
                        if object.ambient_binder_scope_ids.is_empty() {
                            context
                                .well_defined_applicable_names
                                .insert(obj_id, applicable_name);
                        }
                    }
                    if let Some(result_membership_name) = &binding.result_membership_name {
                        let result_membership_name = apply_scoped_declaration(
                            result_membership_name,
                            &binding.binder_names,
                            &binding.binder_types,
                            &available_binder_names,
                            &available_binder_types,
                            &format!("obj_{}_result", obj_id.value()),
                        )?;
                        object_context
                            .well_defined_result_membership_names
                            .insert(obj_id, result_membership_name.clone());
                        if object.ambient_binder_scope_ids.is_empty() {
                            context
                                .well_defined_result_membership_names
                                .insert(obj_id, result_membership_name);
                        }
                    }
                    made_progress = true;
                    continue;
                }
                if object.child_uses.iter().any(|child| {
                    selected_object_ids.contains(&child.obj_id)
                        && !self.global_objects.contains_key(&child.obj_id)
                }) {
                    next.push(obj_id);
                    continue;
                }
                if matches!(object.source_object, Obj::AnonymousFn(_)) {
                    let binding = self.emit_anonymous_function_object(
                        object,
                        &object_context,
                        &available_binder_names,
                        &available_binder_types,
                        binder_scope_emissions,
                    )?;
                    let applied_name = apply_scoped_declaration(
                        &binding.name,
                        &binding.binder_names,
                        &binding.binder_types,
                        &available_binder_names,
                        &available_binder_types,
                        &binding.name,
                    )?;
                    object_context
                        .well_defined_object_names
                        .insert(obj_id, applied_name.clone());
                    if object.ambient_binder_scope_ids.is_empty() {
                        context
                            .well_defined_object_names
                            .insert(obj_id, applied_name);
                    }
                    self.global_objects.insert(obj_id, binding);
                    made_progress = true;
                    continue;
                }
                for child in object.child_uses.iter() {
                    let binding = self.global_objects.get(&child.obj_id).ok_or_else(|| {
                        universal_error(
                            &default_line_file(),
                            format!(
                                "obj_{} depends on missing child obj_{} at role {:?}",
                                obj_id.value(),
                                child.obj_id.value(),
                                child.role
                            ),
                        )
                    })?;
                    let child_name = apply_scoped_declaration(
                        &binding.name,
                        &binding.binder_names,
                        &binding.binder_types,
                        &available_binder_names,
                        &available_binder_types,
                        &format!("obj_{}", child.obj_id.value()),
                    )?;
                    object_context
                        .well_defined_object_names
                        .insert(child.obj_id, child_name);
                }

                // This legacy generalized path still needs the exact frozen
                // node ID to validate a certificate-bearing source object's
                // construction recipe. Temporarily bind the embedded
                // occurrence, then remove it; source statements must still
                // carry their own explicit use edge and cannot inherit this
                // declaration-only binding.
                let temporary_source_binding = if is_proof_carrying_object(&object.source_object) {
                    let source_occurrence_id =
                        object.source_object.source_occurrence_id().ok_or_else(|| {
                            universal_error(
                                &default_line_file(),
                                format!(
                                    "proof-carrying WellDefinedObjId {} has no parser-owned source occurrence ID",
                                    obj_id.value()
                                ),
                            )
                        })?;
                    let previous = object_context
                        .well_defined_object_ids
                        .insert(source_occurrence_id, obj_id);
                    Some((source_occurrence_id, previous))
                } else {
                    None
                };

                let (object_binder_names, object_binder_types) = object_declaration_binders(
                    &object.source_object,
                    &object_context,
                    &available_binder_names,
                    &available_binder_types,
                )?;

                let mut applicable_name = None;
                let mut result_membership_name = None;
                let mut application_value = None;
                let mut application_result_proof: Option<(
                    String,
                    String,
                    String,
                    String,
                    &'static str,
                )> = None;
                if let Obj::FnObj(_) = &object.source_object {
                    let LitexToLeanObjectIr::FunctionApplication(application) =
                        LitexToLeanObjectIr::lower(&object.source_object)
                            .map_err(|message| universal_error(&default_line_file(), message))?
                    else {
                        unreachable!("function object lowering must retain an application")
                    };
                    let layer_index = application
                        .argument_layers
                        .len()
                        .checked_sub(1)
                        .ok_or_else(|| {
                            universal_error(
                                &default_line_file(),
                                "named application object has no source argument layer",
                            )
                        })?;
                    let (
                        initial_function,
                        initial_head,
                        initial_membership,
                        initial_uses_fn_space,
                    ) =
                        match application.head.as_ref() {
                            LitexToLeanObjectIr::Symbol { .. } => {
                                let Some(
                                    WellDefinedFunctionContract::StoredMembershipFact(
                                        contract_fact_id,
                                    ),
                                ) = object.function_contracts.first()
                                else {
                                    return Err(universal_error(
                                        &default_line_file(),
                                        "named application object has no exact function membership FactId",
                                    ));
                                };
                                let function_binding = object_context
                                    .function_bindings
                                    .get(contract_fact_id)
                                    .ok_or_else(|| {
                                        universal_error(
                                            &default_line_file(),
                                            format!(
                                                "obj_{} cannot resolve function contract FactId {}",
                                                obj_id.value(),
                                                contract_fact_id.value()
                                            ),
                                        )
                                    })?;
                                (
                                    function_binding.function.clone(),
                                    self.render_obj_ir(
                                        application.head.as_ref(),
                                        &object_context,
                                    )?,
                                    function_binding.membership_proof_name.clone(),
                                    function_binding.uses_fn_space,
                                )
                            }
                            LitexToLeanObjectIr::AnonymousFunction(anonymous) => {
                                let head_uses = object
                                    .child_uses
                                    .iter()
                                    .filter(|child| {
                                        child.role == WellDefinedObjChildRole::FunctionHead
                                    })
                                    .collect::<Vec<_>>();
                                if head_uses.len() != 1 {
                                    return Err(universal_error(
                                        &default_line_file(),
                                        format!(
                                            "obj_{} anonymous application retains {} function-head edges; expected exactly one",
                                            obj_id.value(),
                                            head_uses.len()
                                        ),
                                    ));
                                }
                                let head_id = head_uses[0].obj_id;
                                let head_binding =
                                    self.global_objects.get(&head_id).ok_or_else(|| {
                                        universal_error(
                                            &default_line_file(),
                                            format!(
                                                "obj_{} cannot resolve anonymous head obj_{}",
                                                obj_id.value(),
                                                head_id.value()
                                            ),
                                        )
                                    })?;
                                let membership_name = head_binding
                                    .function_membership_name
                                    .as_ref()
                                    .ok_or_else(|| {
                                        universal_error(
                                            &default_line_file(),
                                            format!(
                                                "anonymous head obj_{} has no checked function-set membership theorem",
                                                head_id.value()
                                            ),
                                        )
                                    })?;
                                let membership = apply_scoped_declaration(
                                    membership_name,
                                    &head_binding.binder_names,
                                    &head_binding.binder_types,
                                    &available_binder_names,
                                    &available_binder_types,
                                    membership_name,
                                )?;
                                let head = object_context
                                    .well_defined_object_names
                                    .get(&head_id)
                                    .cloned()
                                    .ok_or_else(|| {
                                        universal_error(
                                            &default_line_file(),
                                            format!(
                                                "obj_{} cannot resolve emitted anonymous head obj_{}",
                                                obj_id.value(),
                                                head_id.value()
                                            ),
                                        )
                                    })?;
                                // Anonymous function objects are introduced by
                                // an exact implementation `FnSpec`.
                                (anonymous.function.clone(), head, membership, false)
                            }
                            _ => {
                                return Err(universal_error(
                                    &default_line_file(),
                                    "the universal-object application emitter does not support this structured head",
                                ))
                            }
                        };
                    let mut current_function = initial_function;
                    let mut current_uses_fn_space = initial_uses_fn_space;
                    for previous_layer in 0..layer_index {
                        let LitexToLeanObjectIr::FunctionSet { function: next } =
                            current_function.return_set.as_ref()
                        else {
                            return Err(universal_error(
                                &default_line_file(),
                                format!(
                                    "obj_{} retains application layer {} after a non-function return",
                                    obj_id.value(),
                                    previous_layer + 2
                                ),
                            ));
                        };
                        current_function = next.as_ref().clone();
                        current_uses_fn_space = function_ir_uses_fn_space(&current_function);
                    }

                    let (head, current_membership) = if layer_index == 0 {
                        (initial_head, initial_membership)
                    } else {
                        let prefix_uses = object
                            .child_uses
                            .iter()
                            .filter(|child| {
                                matches!(
                                    child.role,
                                    WellDefinedObjChildRole::FunctionPrefix {
                                        through_layer_index
                                    } if through_layer_index + 1 == layer_index
                                )
                            })
                            .collect::<Vec<_>>();
                        if prefix_uses.len() != 1 {
                            return Err(universal_error(
                                &default_line_file(),
                                format!(
                                    "obj_{} layer {} retains {} callable-prefix edges; expected exactly one",
                                    obj_id.value(),
                                    layer_index + 1,
                                    prefix_uses.len()
                                ),
                            ));
                        }
                        let prefix_id = prefix_uses[0].obj_id;
                        let prefix_name = object_context
                            .well_defined_object_names
                            .get(&prefix_id)
                            .cloned()
                            .ok_or_else(|| {
                                universal_error(
                                    &default_line_file(),
                                    format!(
                                        "obj_{} cannot resolve callable prefix obj_{}",
                                        obj_id.value(),
                                        prefix_id.value()
                                    ),
                                )
                            })?;
                        let prefix_membership = object_context
                            .well_defined_result_membership_names
                            .get(&prefix_id)
                            .cloned()
                            .ok_or_else(|| {
                                universal_error(
                                    &default_line_file(),
                                    format!(
                                        "obj_{} callable prefix obj_{} has no result-membership theorem",
                                        obj_id.value(),
                                        prefix_id.value()
                                    ),
                                )
                            })?;
                        (prefix_name, prefix_membership)
                    };
                    let arguments = application.source_argument_layers[layer_index]
                        .iter()
                        .enumerate()
                        .map(|(argument_index, argument)| {
                            self.render_function_argument_child(
                                object,
                                layer_index,
                                argument_index,
                                argument,
                                &object_context,
                            )
                        })
                        .collect::<Result<Vec<_>, RuntimeError>>()?;
                    let requirements = self.render_application_requirements(
                        &application,
                        layer_index,
                        &current_function,
                        &arguments,
                        &object_context,
                    )?;
                    let argument_list = format!("[{}]", arguments.join(", "));
                    let (applicable_rule, result_rule) = if current_uses_fn_space {
                        ("Litex.fnSpaceApplicable", "Litex.fnSpaceResult")
                    } else {
                        ("Litex.fnSetApplicable", "Litex.fnSetResult")
                    };
                    let helper_name = generated_object_applicable_name(obj_id);
                    if !self.global_names.insert(helper_name.clone()) {
                        return Err(universal_error(
                            &default_line_file(),
                            format!("Lean declaration name `{helper_name}` is already in use"),
                        ));
                    }
                    let proof_type = format!("Litex.Applicable {head} {argument_list}");
                    let lean_binders =
                        render_explicit_binders(&object_binder_names, &object_binder_types)?;
                    let helper_type = render_top_level_forall_type(&lean_binders, &proof_type);
                    let helper_proof = if object_binder_names.is_empty() {
                        format!(
                            "by\n  exact {applicable_rule} (args := {argument_list}) {} rfl ({requirements})",
                            current_membership,
                        )
                    } else {
                        format!(
                            "by\n  intro {}\n  exact {applicable_rule} (args := {argument_list}) {} rfl ({requirements})",
                            object_binder_names.join(" "),
                            current_membership,
                        )
                    };
                    self.declarations.push(format!(
                        "{} :=\n{helper_proof}",
                        render_declaration_head(&format!("theorem {helper_name}"), &helper_type)
                    ));
                    let applied_helper_name = apply_scoped_declaration(
                        &helper_name,
                        &object_binder_names,
                        &object_binder_types,
                        &available_binder_names,
                        &available_binder_types,
                        &helper_name,
                    )?;
                    object_context
                        .well_defined_applicable_names
                        .insert(obj_id, applied_helper_name.clone());
                    if object.ambient_binder_scope_ids.is_empty() {
                        context
                            .well_defined_applicable_names
                            .insert(obj_id, applied_helper_name.clone());
                    }
                    application_value = Some(format!("{head} {argument_list}"));
                    let mut result_context = object_context.clone();
                    for (parameter, argument) in
                        current_function.parameters.iter().zip(arguments.iter())
                    {
                        result_context
                            .symbol_names
                            .insert(parameter.symbol_id, argument.clone());
                    }
                    let result_set =
                        self.render_obj_ir(current_function.return_set.as_ref(), &result_context)?;
                    application_result_proof = Some((
                        current_membership,
                        requirements,
                        result_set,
                        argument_list,
                        result_rule,
                    ));
                    applicable_name = Some(helper_name);
                }

                let name = generated_object_name(obj_id);
                if !self.global_names.insert(name.clone()) {
                    return Err(universal_error(
                        &default_line_file(),
                        format!("Lean declaration name `{name}` is already in use"),
                    ));
                }
                let value = if let Some(value) = application_value {
                    value
                } else {
                    self.render_obj(&object.source_object, &object_context)?
                };
                let lean_binders =
                    render_explicit_binders(&object_binder_names, &object_binder_types)?;
                let declaration_head = if lean_binders.is_empty() {
                    name.clone()
                } else {
                    format!("{name} {}", lean_binders.join(" "))
                };
                self.declarations.push(format!(
                    "noncomputable def {declaration_head} : Litex.Object :=\n  {value}"
                ));
                let applied_name = apply_scoped_declaration(
                    &name,
                    &object_binder_names,
                    &object_binder_types,
                    &available_binder_names,
                    &available_binder_types,
                    &name,
                )?;
                object_context
                    .well_defined_object_names
                    .insert(obj_id, applied_name.clone());
                if object.ambient_binder_scope_ids.is_empty() {
                    context
                        .well_defined_object_names
                        .insert(obj_id, applied_name);
                }

                if let Some((
                    current_membership,
                    requirements,
                    result_set,
                    argument_list,
                    result_rule,
                )) = application_result_proof
                {
                    let theorem_name = generated_object_result_name(obj_id);
                    if !self.global_names.insert(theorem_name.clone()) {
                        return Err(universal_error(
                            &default_line_file(),
                            format!("Lean declaration name `{theorem_name}` is already in use"),
                        ));
                    }
                    let declared_object = apply_scoped_declaration(
                        &name,
                        &object_binder_names,
                        &object_binder_types,
                        &object_binder_names,
                        &object_binder_types,
                        &name,
                    )?;
                    let proposition = format!("Litex.In {declared_object} {result_set}");
                    let theorem_type = render_top_level_forall_type(&lean_binders, &proposition);
                    let theorem_proof = if object_binder_names.is_empty() {
                        format!(
                            "by\n  simpa [{name}] using ({result_rule} (args := {argument_list}) {current_membership} rfl ({requirements}))"
                        )
                    } else {
                        format!(
                            "by\n  intro {}\n  simpa [{name}] using ({result_rule} (args := {argument_list}) {current_membership} rfl ({requirements}))",
                            object_binder_names.join(" ")
                        )
                    };
                    self.declarations.push(format!(
                        "{} :=\n{theorem_proof}",
                        render_declaration_head(&format!("theorem {theorem_name}"), &theorem_type,)
                    ));
                    let applied_theorem_name = apply_scoped_declaration(
                        &theorem_name,
                        &object_binder_names,
                        &object_binder_types,
                        &available_binder_names,
                        &available_binder_types,
                        &theorem_name,
                    )?;
                    object_context
                        .well_defined_result_membership_names
                        .insert(obj_id, applied_theorem_name.clone());
                    if object.ambient_binder_scope_ids.is_empty() {
                        context
                            .well_defined_result_membership_names
                            .insert(obj_id, applied_theorem_name);
                    }
                    result_membership_name = Some(theorem_name);
                }

                if let Some((source_occurrence_id, previous)) = temporary_source_binding {
                    if let Some(previous) = previous {
                        object_context
                            .well_defined_object_ids
                            .insert(source_occurrence_id, previous);
                    } else {
                        object_context
                            .well_defined_object_ids
                            .remove(&source_occurrence_id);
                    }
                }

                self.global_objects.insert(
                    obj_id,
                    GlobalObjectBinding {
                        name: name.clone(),
                        source_object: object.source_object.clone(),
                        binder_names: object_binder_names.clone(),
                        binder_types: object_binder_types.clone(),
                        applicable_name,
                        result_membership_name,
                        function_membership_name: None,
                    },
                );
                made_progress = true;
            }
            if next.is_empty() {
                break;
            }
            if !made_progress {
                let blocked = next
                    .iter()
                    .map(|obj_id| format!("obj_{}", obj_id.value()))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(universal_error(
                    &default_line_file(),
                    format!("well-defined object dependency cycle or missing child: {blocked}"),
                ));
            }
            remaining = next;
        }
        Ok(())
    }

    fn render_function_argument_child(
        &self,
        parent: &LitexToLeanWellDefinednessObjectIr,
        layer_index: usize,
        argument_index: usize,
        source_argument: &Obj,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let matches = parent
            .child_uses
            .iter()
            .filter(|child| {
                child.role
                    == WellDefinedObjChildRole::FunctionArgument {
                        layer_index,
                        argument_index,
                    }
            })
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "obj_{} application layer {} argument {} retains {} child edges; expected exactly one",
                    parent.well_defined_obj_id.value(),
                    layer_index + 1,
                    argument_index + 1,
                    matches.len()
                ),
            ));
        }
        let child = context
            .well_defined_object_names
            .get(&matches[0].obj_id)
            .cloned()
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "obj_{} cannot resolve application child obj_{}",
                        parent.well_defined_obj_id.value(),
                        matches[0].obj_id.value()
                    ),
                )
            })?;
        let child_object = context
            .well_definedness
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == matches[0].obj_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "application child is absent from the frozen WD certificate",
                )
            })?;
        if obj_equality_key(&child_object.source_object) != obj_equality_key(source_argument) {
            return Err(universal_error(
                &default_line_file(),
                "application child edge changed its ordered source argument",
            ));
        }
        Ok(child)
    }

    fn prepare_local_well_defined_facts_for_fact_type(
        &mut self,
        context: &mut RenderContext,
        fact: &Fact,
        binder_names: &[String],
        binder_types: &[String],
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let mut scopes = Vec::new();
        self.collect_application_scopes_from_fact(
            fact,
            context,
            binder_names,
            binder_types,
            &mut scopes,
        )?;
        let well_definedness = context.well_definedness.clone();
        for mut scope in scopes {
            merge_local_well_defined_context(&mut scope.context, context)?;
            let occurrence_ids = HashSet::from([scope.source_occurrence_id]);
            let proof_ids = resolve_source_occurrence_object_ids(
                &well_definedness,
                &occurrence_ids,
                &mut scope.context,
                &fact.line_file(),
            )?;
            if well_defined_closure_uses_binder_scope(&well_definedness, &proof_ids)? {
                self.prepare_scoped_well_defined_facts(
                    &mut scope.context,
                    &well_definedness,
                    &occurrence_ids,
                    &HashSet::new(),
                    &scope.binder_names,
                    &scope.binder_types,
                )?;
                merge_well_defined_object_ids(context, &scope.context)?;
                context
                    .well_defined_fact_names
                    .extend(scope.context.well_defined_fact_names);
                continue;
            }
            if scope.binder_names != binder_names || scope.binder_types != binder_types {
                self.prepare_local_generalized_well_defined_scope(
                    context,
                    &mut scope.context,
                    &well_definedness,
                    &occurrence_ids,
                    &HashSet::new(),
                    binder_names,
                    binder_types,
                    &scope.binder_names,
                    &scope.binder_types,
                    local_steps,
                )?;
                continue;
            }
            self.prepare_local_scoped_well_defined_facts(
                &mut scope.context,
                &well_definedness,
                &occurrence_ids,
                &HashSet::new(),
                local_steps,
            )?;
            merge_local_well_defined_context(context, &scope.context)?;
        }

        let mut proof_carrying_scopes = Vec::new();
        self.collect_proof_carrying_object_scopes_from_fact(
            fact,
            context,
            binder_names,
            binder_types,
            &mut proof_carrying_scopes,
        )?;
        for mut scope in proof_carrying_scopes {
            merge_local_well_defined_context(&mut scope.context, context)?;
            let proof_ids = resolve_source_occurrence_object_ids(
                &well_definedness,
                &scope.source_occurrence_ids,
                &mut scope.context,
                &fact.line_file(),
            )?;
            if well_defined_closure_uses_binder_scope(&well_definedness, &proof_ids)? {
                self.prepare_scoped_well_defined_facts(
                    &mut scope.context,
                    &well_definedness,
                    &HashSet::new(),
                    &proof_ids,
                    &scope.binder_names,
                    &scope.binder_types,
                )?;
                merge_well_defined_object_ids(context, &scope.context)?;
                context
                    .well_defined_fact_names
                    .extend(scope.context.well_defined_fact_names);
                continue;
            }
            if scope.binder_names != binder_names || scope.binder_types != binder_types {
                self.prepare_local_generalized_well_defined_scope(
                    context,
                    &mut scope.context,
                    &well_definedness,
                    &HashSet::new(),
                    &proof_ids,
                    binder_names,
                    binder_types,
                    &scope.binder_names,
                    &scope.binder_types,
                    local_steps,
                )?;
                continue;
            }
            self.prepare_local_scoped_well_defined_facts(
                &mut scope.context,
                &well_definedness,
                &HashSet::new(),
                &proof_ids,
                local_steps,
            )?;
            merge_local_well_defined_context(context, &scope.context)?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_local_generalized_well_defined_scope(
        &mut self,
        outer_context: &mut RenderContext,
        nested_context: &mut RenderContext,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
        application_occurrence_ids: &HashSet<SourceObjectOccurrenceId>,
        initial_object_proof_ids: &HashSet<WellDefinedObjId>,
        outer_binder_names: &[String],
        outer_binder_types: &[String],
        nested_binder_names: &[String],
        nested_binder_types: &[String],
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        if nested_binder_names.len() < outer_binder_names.len()
            || nested_binder_types.len() < outer_binder_types.len()
            || nested_binder_names[..outer_binder_names.len()] != *outer_binder_names
            || nested_binder_types[..outer_binder_types.len()] != *outer_binder_types
        {
            return Err(universal_error(
                &default_line_file(),
                "a nested WD environment changed its visible outer Lean binders",
            ));
        }
        let extra_names = &nested_binder_names[outer_binder_names.len()..];
        let extra_types = &nested_binder_types[outer_binder_types.len()..];
        if extra_names.is_empty() {
            return Err(universal_error(
                &default_line_file(),
                "a generalized local WD environment has no additional binders",
            ));
        }

        let mut nested_steps = Vec::new();
        self.prepare_local_scoped_well_defined_facts(
            nested_context,
            well_definedness,
            application_occurrence_ids,
            initial_object_proof_ids,
            &mut nested_steps,
        )?;
        if nested_steps.is_empty() {
            return merge_local_well_defined_context(outer_context, nested_context);
        }

        let binders = render_explicit_binders(extra_names, extra_types)?;
        let bundled_proposition = right_associated(
            nested_steps
                .iter()
                .map(|step| step.proposition.clone())
                .collect(),
            " ∧ ",
            "True",
        );
        let generalized_proposition = format!("∀ {}, {bundled_proposition}", binders.join(" "));
        let mut proof_lines = vec![
            "by".to_string(),
            format!("  intro {}", extra_names.join(" ")),
        ];
        for step in nested_steps.iter() {
            proof_lines.push(render_local_proof_step(step));
        }
        let bundled_value = right_associated_conjunction_proof(
            nested_steps.iter().map(|step| step.name.clone()).collect(),
        )
        .expect("nonempty nested WD steps have a conjunction proof");
        proof_lines.push(format!("  exact {bundled_value}"));
        let scope_name = format!("__scope{}", self.next_local_scope_id);
        self.next_local_scope_id += 1;
        push_unique_local_proof_step(
            local_steps,
            LocalProofStep {
                name: scope_name.clone(),
                proposition: generalized_proposition,
                proof: proof_lines.join("\n"),
            },
        )?;

        let scope_application = format!("{scope_name} {}", extra_names.join(" "));
        for (index, step) in nested_steps.iter().enumerate() {
            let projection = conjunction_projection(&scope_application, index, nested_steps.len());
            replace_local_proof_name(nested_context, &step.name, &projection);
        }
        merge_local_well_defined_context(outer_context, nested_context)
    }

    fn prepare_local_well_defined_facts_for_fact_proof(
        &mut self,
        context: &mut RenderContext,
        fact: &LitexToLeanFactIr,
        binder_names: &[String],
        binder_types: &[String],
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let mut source_occurrence_ids = HashSet::new();
        collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
            fact,
            &mut source_occurrence_ids,
        )?;
        source_occurrence_ids.retain(|source_occurrence_id| {
            !context
                .well_defined_object_ids
                .contains_key(source_occurrence_id)
        });
        if source_occurrence_ids.is_empty() {
            return Ok(());
        }
        let well_definedness = context.well_definedness.clone();
        let proof_ids = resolve_source_occurrence_object_ids(
            &well_definedness,
            &source_occurrence_ids,
            context,
            &fact.proposition.line_file(),
        )?;
        let mut scope = context.clone();
        if well_defined_closure_uses_binder_scope(&well_definedness, &proof_ids)? {
            self.prepare_scoped_well_defined_facts(
                &mut scope,
                &well_definedness,
                &HashSet::new(),
                &proof_ids,
                binder_names,
                binder_types,
            )?;
        } else {
            self.prepare_local_scoped_well_defined_facts(
                &mut scope,
                &well_definedness,
                &HashSet::new(),
                &proof_ids,
                local_steps,
            )?;
        }
        merge_local_well_defined_context(context, &scope)
    }

    fn prepare_local_scoped_well_defined_facts(
        &mut self,
        context: &mut RenderContext,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
        application_occurrence_ids: &HashSet<SourceObjectOccurrenceId>,
        initial_object_proof_ids: &HashSet<WellDefinedObjId>,
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        if application_occurrence_ids.is_empty() && initial_object_proof_ids.is_empty() {
            return Ok(());
        }
        let mut canonical_proof_ids = initial_object_proof_ids.clone();
        canonical_proof_ids.extend(resolve_source_occurrence_object_ids(
            well_definedness,
            application_occurrence_ids,
            context,
            &default_line_file(),
        )?);
        let mut selected_ids = HashSet::new();
        let mut selected_roles = HashSet::new();
        for requirement in well_definedness.target_requirements.iter() {
            if !application_occurrence_ids.contains(&requirement.source_occurrence_id)
                || !selected_roles.insert((requirement.source_occurrence_id, requirement.role))
            {
                continue;
            }
            canonical_proof_ids.insert(requirement.well_defined_obj_id);
            selected_ids.insert(requirement.well_defined_fact_id);
        }

        let objects_by_id = well_definedness
            .objects
            .iter()
            .map(|object| (object.well_defined_obj_id, object))
            .collect::<HashMap<_, _>>();
        let mut pending_object_ids = canonical_proof_ids.into_iter().collect::<Vec<_>>();
        let mut selected_object_ids = HashSet::new();
        add_well_defined_object_proof_closure(
            &objects_by_id,
            &mut pending_object_ids,
            &mut selected_object_ids,
            &mut selected_ids,
        )?;

        loop {
            let mut referenced_occurrence_ids = HashSet::new();
            for fact in well_definedness
                .facts
                .iter()
                .filter(|fact| selected_ids.contains(&fact.well_defined_fact_id))
            {
                collect_proof_carrying_object_occurrence_ids_from_fact(
                    &fact.expected_proposition,
                    &mut referenced_occurrence_ids,
                )?;
                collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                    &fact.fact,
                    &mut referenced_occurrence_ids,
                )?;
            }
            let mut added = false;
            for source_occurrence_id in referenced_occurrence_ids {
                if context
                    .well_defined_object_ids
                    .contains_key(&source_occurrence_id)
                {
                    continue;
                }
                pending_object_ids.extend(resolve_source_occurrence_object_ids(
                    well_definedness,
                    &HashSet::from([source_occurrence_id]),
                    context,
                    &default_line_file(),
                )?);
                added = true;
            }
            if !added {
                break;
            }
            add_well_defined_object_proof_closure(
                &objects_by_id,
                &mut pending_object_ids,
                &mut selected_object_ids,
                &mut selected_ids,
            )?;
        }

        let mut remaining = well_definedness
            .facts
            .iter()
            .filter(|fact| {
                selected_ids.contains(&fact.well_defined_fact_id)
                    && !context
                        .well_defined_fact_names
                        .contains_key(&fact.well_defined_fact_id)
            })
            .collect::<Vec<_>>();
        remaining.sort_by_key(|fact| fact.well_defined_fact_id.value());
        for fact in remaining.iter() {
            if !context
                .active_binder_scope_ids
                .starts_with(&fact.ambient_binder_scope_ids)
            {
                return Err(universal_error(
                    &fact.expected_proposition.line_file(),
                    format!(
                        "WellDefinedFactId {} requires binder scopes {:?}, outside the active local chain {:?}",
                        fact.well_defined_fact_id.value(),
                        fact.ambient_binder_scope_ids,
                        context.active_binder_scope_ids
                    ),
                ));
            }
            if !facts_are_canonically_equal(&fact.expected_proposition, &fact.fact.proposition)? {
                return Err(universal_error(
                    &fact.expected_proposition.line_file(),
                    format!(
                        "WellDefinedFactId {} changed proposition during local Lean emission",
                        fact.well_defined_fact_id.value()
                    ),
                ));
            }
        }

        while !remaining.is_empty() {
            let mut next = Vec::new();
            let mut made_progress = false;
            for fact in remaining {
                let rendered = self
                    .render_fact(&fact.expected_proposition, context)
                    .and_then(|proposition| {
                        self.render_proof_term(&fact.fact, context)
                            .map(|proof| (proposition, proof))
                    });
                match rendered {
                    Ok((proposition, proof)) => {
                        let name = well_defined_fact_name(context, fact.well_defined_fact_id);
                        push_unique_local_proof_step(
                            local_steps,
                            LocalProofStep {
                                name: name.clone(),
                                proposition,
                                proof,
                            },
                        )?;
                        context
                            .well_defined_fact_names
                            .insert(fact.well_defined_fact_id, name);
                        made_progress = true;
                    }
                    Err(_) => next.push(fact),
                }
            }
            if next.is_empty() {
                break;
            }
            if !made_progress {
                let blocked = next
                    .iter()
                    .map(|fact| fact.well_defined_fact_id.value().to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let first_error = self
                    .render_fact(&next[0].expected_proposition, context)
                    .and_then(|_| self.render_proof_term(&next[0].fact, context))
                    .expect_err("a blocked local WD fact must still fail diagnostic replay");
                return Err(universal_error(
                    &next[0].expected_proposition.line_file(),
                    format!(
                        "could not replay local well-defined facts [{blocked}] in dependency order; first blocked proposition is `{}`: {}",
                        next[0].expected_proposition,
                        first_error.trace_message()
                    ),
                ));
            }
            remaining = next;
        }

        self.prepare_local_well_defined_objects(
            context,
            &objects_by_id,
            &selected_object_ids,
            local_steps,
        )
    }

    fn prepare_local_well_defined_objects(
        &self,
        context: &mut RenderContext,
        objects_by_id: &HashMap<WellDefinedObjId, &LitexToLeanWellDefinednessObjectIr>,
        selected_object_ids: &HashSet<WellDefinedObjId>,
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let mut remaining = selected_object_ids
            .iter()
            .filter(|obj_id| !context.well_defined_object_names.contains_key(obj_id))
            .copied()
            .collect::<Vec<_>>();
        remaining.sort_by_key(|obj_id| obj_id.value());
        while !remaining.is_empty() {
            let mut next = Vec::new();
            let mut made_progress = false;
            for obj_id in remaining {
                let object = objects_by_id.get(&obj_id).ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!(
                            "WellDefinedObjId {} has no frozen object record",
                            obj_id.value()
                        ),
                    )
                })?;
                if !context
                    .active_binder_scope_ids
                    .starts_with(&object.ambient_binder_scope_ids)
                    || object.owned_binder_scope_id.is_some()
                {
                    return Err(universal_error(
                        &default_line_file(),
                        format!(
                            "obj_{} requires binder scopes {:?} or owns a nested scope unavailable to the active local chain {:?}",
                            obj_id.value(),
                            object.ambient_binder_scope_ids,
                            context.active_binder_scope_ids
                        ),
                    ));
                }
                if object.child_uses.iter().any(|child| {
                    selected_object_ids.contains(&child.obj_id)
                        && !context
                            .well_defined_object_names
                            .contains_key(&child.obj_id)
                }) {
                    next.push(obj_id);
                    continue;
                }

                if let Obj::FnObj(_) = &object.source_object {
                    self.prepare_local_function_application_object(context, object, local_steps)?;
                } else {
                    let value = self.render_obj(&object.source_object, context)?;
                    context
                        .well_defined_object_names
                        .insert(obj_id, value.clone());
                    if is_proof_carrying_arithmetic_obj(&object.source_object) {
                        self.prepare_local_arithmetic_result_membership_object(
                            context,
                            object,
                            &value,
                            local_steps,
                        )?;
                    }
                }
                made_progress = true;
            }
            if next.is_empty() {
                break;
            }
            if !made_progress {
                let blocked = next
                    .iter()
                    .map(|obj_id| format!("obj_{}", obj_id.value()))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(universal_error(
                    &default_line_file(),
                    format!("local WD object dependency cycle or missing child: {blocked}"),
                ));
            }
            remaining = next;
        }
        Ok(())
    }

    fn prepare_local_arithmetic_result_membership_object(
        &self,
        context: &mut RenderContext,
        object: &LitexToLeanWellDefinednessObjectIr,
        value: &str,
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let Some(result_set) = object.intrinsic_result_set.as_ref() else {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "proof-carrying arithmetic obj_{} has no frozen intrinsic result carrier",
                    object.well_defined_obj_id.value()
                ),
            ));
        };
        if !matches!(
            result_set,
            LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Complex)
        ) {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "proof-carrying arithmetic obj_{} changed its intrinsic result carrier",
                    object.well_defined_obj_id.value()
                ),
            ));
        }

        let already_named = context
            .well_defined_fact_names
            .iter()
            .find_map(|(fact_id, name)| {
                context
                    .well_definedness
                    .facts
                    .iter()
                    .find(|fact| fact.well_defined_fact_id == *fact_id)
                    .filter(|fact| {
                        matches!(
                            &fact.expected_proposition,
                            Fact::AtomicFact(AtomicFact::InFact(membership))
                                if obj_equality_key(&membership.element)
                                    == obj_equality_key(&object.source_object)
                                    && matches!(
                                        &membership.set,
                                        Obj::StandardSet(StandardSet::C)
                                    )
                        )
                    })
                    .map(|_| name.clone())
            });
        if let Some(name) = already_named {
            context
                .well_defined_result_membership_names
                .insert(object.well_defined_obj_id, name);
            return Ok(());
        }

        let LitexToLeanObjectIr::BuiltinApp {
            source_occurrence_id,
            semantic_key,
            operator,
            arguments,
        } = LitexToLeanObjectIr::lower(&object.source_object)
            .map_err(|message| universal_error(&default_line_file(), message))?
        else {
            return Err(universal_error(
                &default_line_file(),
                "proof-carrying arithmetic WD object lowered to a non-builtin object",
            ));
        };
        let theorem_name = match operator {
            LitexToLeanBuiltinObjectOperatorIr::Add => "complexAddClosure",
            LitexToLeanBuiltinObjectOperatorIr::Sub => "complexSubClosure",
            LitexToLeanBuiltinObjectOperatorIr::Mul => "complexMulClosure",
            LitexToLeanBuiltinObjectOperatorIr::Div => "complexDivClosure",
            _ => {
                return Err(universal_error(
                    &default_line_file(),
                    "a proof-carrying arithmetic result used an unsupported builtin operator",
                ));
            }
        };
        let membership_proofs = self.resolve_builtin_argument_membership_proofs(
            source_occurrence_id,
            &semantic_key,
            operator,
            &arguments,
            context,
        )?;
        let theorem = rule_theorem_name(theorem_name);
        let proof = if operator == LitexToLeanBuiltinObjectOperatorIr::Div {
            let nonzero_proof = self.resolve_builtin_argument_nonzero_proof(
                source_occurrence_id,
                &semantic_key,
                operator,
                &arguments,
                context,
            )?;
            format!(
                "({theorem} ({}) ({}) ({nonzero_proof}))",
                membership_proofs[0], membership_proofs[1]
            )
        } else {
            format!(
                "({theorem} ({}) ({}))",
                membership_proofs[0], membership_proofs[1]
            )
        };
        let result_name = generated_object_result_name(object.well_defined_obj_id);
        push_unique_local_proof_step(
            local_steps,
            LocalProofStep {
                name: result_name.clone(),
                proposition: format!(
                    "Litex.In {value} {}",
                    self.render_obj_ir(result_set, context)?
                ),
                proof,
            },
        )?;
        context
            .well_defined_result_membership_names
            .insert(object.well_defined_obj_id, result_name);
        Ok(())
    }

    fn prepare_local_function_application_object(
        &self,
        context: &mut RenderContext,
        object: &LitexToLeanWellDefinednessObjectIr,
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let obj_id = object.well_defined_obj_id;
        let LitexToLeanObjectIr::FunctionApplication(application) =
            LitexToLeanObjectIr::lower(&object.source_object)
                .map_err(|message| universal_error(&default_line_file(), message))?
        else {
            return Err(universal_error(
                &default_line_file(),
                "function WD object lowered to a non-application",
            ));
        };
        let layer_index = application
            .argument_layers
            .len()
            .checked_sub(1)
            .ok_or_else(|| universal_error(&default_line_file(), "application has no layer"))?;
        let Some(WellDefinedFunctionContract::StoredMembershipFact(contract_fact_id)) =
            object.function_contracts.first()
        else {
            return Err(universal_error(
                &default_line_file(),
                "local named application has no exact function membership FactId",
            ));
        };
        let binding = context
            .function_bindings
            .get(contract_fact_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "obj_{} cannot resolve function contract FactId {}",
                        obj_id.value(),
                        contract_fact_id.value()
                    ),
                )
            })?;
        let mut current_function = binding.function.clone();
        let mut current_uses_fn_space = binding.uses_fn_space;
        for previous_layer in 0..layer_index {
            let LitexToLeanObjectIr::FunctionSet { function: next } =
                current_function.return_set.as_ref()
            else {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "obj_{} retains layer {} after a non-function return",
                        obj_id.value(),
                        previous_layer + 2
                    ),
                ));
            };
            current_function = next.as_ref().clone();
            current_uses_fn_space = function_ir_uses_fn_space(&current_function);
        }

        let (head, current_membership) = if layer_index == 0 {
            (
                self.render_obj_ir(application.head.as_ref(), context)?,
                binding.membership_proof_name.clone(),
            )
        } else {
            let prefixes = object
                .child_uses
                .iter()
                .filter(|child| {
                    matches!(
                        child.role,
                        WellDefinedObjChildRole::FunctionPrefix { through_layer_index }
                            if through_layer_index + 1 == layer_index
                    )
                })
                .collect::<Vec<_>>();
            if prefixes.len() != 1 {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "obj_{} layer {} has {} callable-prefix edges",
                        obj_id.value(),
                        layer_index + 1,
                        prefixes.len()
                    ),
                ));
            }
            let prefix_id = prefixes[0].obj_id;
            (
                context
                    .well_defined_object_names
                    .get(&prefix_id)
                    .cloned()
                    .ok_or_else(|| {
                        universal_error(
                            &default_line_file(),
                            format!(
                                "obj_{} cannot resolve prefix obj_{}",
                                obj_id.value(),
                                prefix_id.value()
                            ),
                        )
                    })?,
                context
                    .well_defined_result_membership_names
                    .get(&prefix_id)
                    .cloned()
                    .ok_or_else(|| {
                        universal_error(
                            &default_line_file(),
                            format!(
                                "obj_{} prefix obj_{} has no local result proof",
                                obj_id.value(),
                                prefix_id.value()
                            ),
                        )
                    })?,
            )
        };
        let arguments = application.source_argument_layers[layer_index]
            .iter()
            .enumerate()
            .map(|(argument_index, argument)| {
                self.render_function_argument_child(
                    object,
                    layer_index,
                    argument_index,
                    argument,
                    context,
                )
            })
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        let requirements = self.render_application_requirements(
            &application,
            layer_index,
            &current_function,
            &arguments,
            context,
        )?;
        let argument_list = format!("[{}]", arguments.join(", "));
        let (applicable_rule, result_rule) = if current_uses_fn_space {
            ("Litex.fnSpaceApplicable", "Litex.fnSpaceResult")
        } else {
            ("Litex.fnSetApplicable", "Litex.fnSetResult")
        };
        let applicable_name = generated_object_applicable_name(obj_id);
        push_unique_local_proof_step(
            local_steps,
            LocalProofStep {
                name: applicable_name.clone(),
                proposition: format!("Litex.Applicable ({head}) {argument_list}"),
                proof: format!(
                    "{applicable_rule} (args := {argument_list}) {current_membership} rfl ({requirements})"
                ),
            },
        )?;
        context
            .well_defined_applicable_names
            .insert(obj_id, applicable_name);

        let value = format!("{head} {argument_list}");
        context
            .well_defined_object_names
            .insert(obj_id, format!("({value})"));
        let mut result_context = context.clone();
        for (parameter, argument) in current_function.parameters.iter().zip(arguments.iter()) {
            result_context
                .symbol_names
                .insert(parameter.symbol_id, argument.clone());
        }
        let result_set =
            self.render_obj_ir(current_function.return_set.as_ref(), &result_context)?;
        let result_name = generated_object_result_name(obj_id);
        push_unique_local_proof_step(
            local_steps,
            LocalProofStep {
                name: result_name.clone(),
                proposition: format!("Litex.In ({value}) {result_set}"),
                proof: format!(
                    "by simpa using ({result_rule} (args := {argument_list}) {current_membership} rfl ({requirements}))"
                ),
            },
        )?;
        context
            .well_defined_result_membership_names
            .insert(obj_id, result_name);
        Ok(())
    }

    fn collect_proof_carrying_object_scopes_from_fact(
        &self,
        fact: &Fact,
        context: &RenderContext,
        binder_names: &[String],
        binder_types: &[String],
        scopes: &mut Vec<ProofCarryingObjectScope>,
    ) -> Result<(), RuntimeError> {
        match fact {
            Fact::AtomicFact(atomic) => {
                let mut source_occurrence_ids = HashSet::new();
                for object in atomic.args_ref() {
                    let object = LitexToLeanObjectIr::lower(object)
                        .map_err(|message| universal_error(&fact.line_file(), message))?;
                    collect_proof_carrying_object_occurrence_ids(
                        &object,
                        &mut source_occurrence_ids,
                    )?;
                }
                if !source_occurrence_ids.is_empty() {
                    scopes.push(ProofCarryingObjectScope {
                        source_occurrence_ids,
                        context: context.clone(),
                        binder_names: binder_names.to_vec(),
                        binder_types: binder_types.to_vec(),
                    });
                }
                Ok(())
            }
            Fact::ForallFact(forall) => {
                if !forall.dom_facts.is_empty() {
                    return Err(universal_error(
                        &forall.line_file,
                        "nested forall domain premises need explicit retained binder FactIds before To-Lean emission",
                    ));
                }
                let (nested, nested_names, nested_types) = self.extend_forall_parameter_scope(
                    forall,
                    context,
                    binder_names,
                    binder_types,
                )?;
                for conclusion in forall.then_facts.iter() {
                    self.collect_proof_carrying_object_scopes_from_fact(
                        &conclusion.clone().to_fact(),
                        &nested,
                        &nested_names,
                        &nested_types,
                        scopes,
                    )?;
                }
                Ok(())
            }
            Fact::ExistFact(existential) if existential.is_plain_exist() => {
                let mut nested = context.clone();
                let mut nested_names = binder_names.to_vec();
                let mut nested_types = binder_types.to_vec();
                for group in existential.params_def_with_type().groups.iter() {
                    for binding in group.params.iter() {
                        let name = lean_name(binding.name());
                        nested.symbol_names.insert(binding.id(), name.clone());
                        nested_names.push(name);
                        nested_types.push("Litex.Object".to_string());
                    }
                }
                let mut source_occurrence_ids = HashSet::new();
                for object in existential.get_args_from_fact_ref() {
                    let object = LitexToLeanObjectIr::lower(object)
                        .map_err(|message| universal_error(&fact.line_file(), message))?;
                    collect_proof_carrying_object_occurrence_ids(
                        &object,
                        &mut source_occurrence_ids,
                    )?;
                }
                if !source_occurrence_ids.is_empty() {
                    scopes.push(ProofCarryingObjectScope {
                        source_occurrence_ids,
                        context: nested,
                        binder_names: nested_names,
                        binder_types: nested_types,
                    });
                }
                Ok(())
            }
            _ => Err(universal_error(
                &fact.line_file(),
                format!(
                    "the universal-object MVP does not collect proof-carrying object scopes from fact kind `{}`",
                    fact.fact_type_string()
                ),
            )),
        }
    }

    fn collect_application_scopes_from_fact(
        &self,
        fact: &Fact,
        context: &RenderContext,
        binder_names: &[String],
        binder_types: &[String],
        scopes: &mut Vec<ApplicationScope>,
    ) -> Result<(), RuntimeError> {
        match fact {
            Fact::AtomicFact(atomic) => {
                for object in atomic.args_ref() {
                    let object = LitexToLeanObjectIr::lower(object)
                        .map_err(|message| universal_error(&fact.line_file(), message))?;
                    self.collect_application_scopes_from_object(
                        &object,
                        context,
                        binder_names,
                        binder_types,
                        scopes,
                    );
                }
                Ok(())
            }
            Fact::ForallFact(forall) => {
                if !forall.dom_facts.is_empty() {
                    return Err(universal_error(
                        &forall.line_file,
                        "nested forall domain premises need explicit retained binder FactIds before To-Lean emission",
                    ));
                }
                let (nested, nested_names, nested_types) = self.extend_forall_parameter_scope(
                    forall,
                    context,
                    binder_names,
                    binder_types,
                )?;
                for conclusion in forall.then_facts.iter() {
                    self.collect_application_scopes_from_fact(
                        &conclusion.clone().to_fact(),
                        &nested,
                        &nested_names,
                        &nested_types,
                        scopes,
                    )?;
                }
                Ok(())
            }
            Fact::ExistFact(existential) if existential.is_plain_exist() => {
                let mut nested = context.clone();
                let mut nested_names = binder_names.to_vec();
                let mut nested_types = binder_types.to_vec();
                for group in existential.params_def_with_type().groups.iter() {
                    for binding in group.params.iter() {
                        let name = lean_name(binding.name());
                        nested.symbol_names.insert(binding.id(), name.clone());
                        nested_names.push(name);
                        nested_types.push("Litex.Object".to_string());
                    }
                }
                for object in existential.get_args_from_fact_ref() {
                    let object = LitexToLeanObjectIr::lower(object)
                        .map_err(|message| universal_error(&fact.line_file(), message))?;
                    self.collect_application_scopes_from_object(
                        &object,
                        &nested,
                        &nested_names,
                        &nested_types,
                        scopes,
                    );
                }
                Ok(())
            }
            _ => Err(universal_error(
                &fact.line_file(),
                format!(
                    "the universal-object MVP does not collect application scopes from fact kind `{}`",
                    fact.fact_type_string()
                ),
            )),
        }
    }

    fn collect_application_scopes_from_object(
        &self,
        object: &LitexToLeanObjectIr,
        context: &RenderContext,
        binder_names: &[String],
        binder_types: &[String],
        scopes: &mut Vec<ApplicationScope>,
    ) {
        match object {
            LitexToLeanObjectIr::FunctionApplication(application) => {
                for layer in application.argument_layers.iter() {
                    for argument in layer {
                        self.collect_application_scopes_from_object(
                            argument,
                            context,
                            binder_names,
                            binder_types,
                            scopes,
                        );
                    }
                }
                scopes.push(ApplicationScope {
                    source_occurrence_id: application.source_occurrence_id,
                    context: context.clone(),
                    binder_names: binder_names.to_vec(),
                    binder_types: binder_types.to_vec(),
                });
            }
            LitexToLeanObjectIr::BuiltinApp { arguments, .. }
            | LitexToLeanObjectIr::Collection {
                items: arguments, ..
            } => {
                for argument in arguments {
                    self.collect_application_scopes_from_object(
                        argument,
                        context,
                        binder_names,
                        binder_types,
                        scopes,
                    );
                }
            }
            LitexToLeanObjectIr::SetBuilder(set_builder) => self
                .collect_application_scopes_from_object(
                    set_builder.set.as_ref(),
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                ),
            // Applications inside an anonymous body live in the verifier-owned
            // binder scope of that function. Its WD object closure is selected
            // through the anonymous-function occurrence, not as if the body
            // were evaluated in the surrounding source scope.
            LitexToLeanObjectIr::AnonymousFunction(_) => {}
            LitexToLeanObjectIr::FunctionSet { function } => {
                for parameter in function.parameters.iter() {
                    self.collect_application_scopes_from_object(
                        &parameter.set,
                        context,
                        binder_names,
                        binder_types,
                        scopes,
                    );
                }
                self.collect_application_scopes_from_object(
                    function.return_set.as_ref(),
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                );
            }
            LitexToLeanObjectIr::ClosedRange { start, end }
            | LitexToLeanObjectIr::Range { start, end } => {
                self.collect_application_scopes_from_object(
                    start,
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                );
                self.collect_application_scopes_from_object(
                    end,
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                );
            }
            LitexToLeanObjectIr::GeneralCartesianProduct {
                index_set,
                family_set,
                family_function,
            } => {
                for argument in [index_set, family_set, family_function] {
                    self.collect_application_scopes_from_object(
                        argument,
                        context,
                        binder_names,
                        binder_types,
                        scopes,
                    );
                }
            }
            LitexToLeanObjectIr::SequenceSet { values, length } => {
                self.collect_application_scopes_from_object(
                    values,
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                );
                if let Some(length) = length {
                    self.collect_application_scopes_from_object(
                        length,
                        context,
                        binder_names,
                        binder_types,
                        scopes,
                    );
                }
            }
            LitexToLeanObjectIr::Aggregate { arguments, .. } => {
                for argument in arguments {
                    self.collect_application_scopes_from_object(
                        argument,
                        context,
                        binder_names,
                        binder_types,
                        scopes,
                    );
                }
            }
            LitexToLeanObjectIr::TupleDimension(object) => self
                .collect_application_scopes_from_object(
                    object,
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                ),
            LitexToLeanObjectIr::IndexedAccess { object, index } => {
                self.collect_application_scopes_from_object(
                    object,
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                );
                self.collect_application_scopes_from_object(
                    index,
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                );
            }
            LitexToLeanObjectIr::Symbol { .. }
            | LitexToLeanObjectIr::Number { .. }
            | LitexToLeanObjectIr::Constant(_)
            | LitexToLeanObjectIr::StandardSet(_) => {}
        }
    }

    fn extend_forall_parameter_scope(
        &self,
        forall: &ForallFact,
        context: &RenderContext,
        binder_names: &[String],
        binder_types: &[String],
    ) -> Result<(RenderContext, Vec<String>, Vec<String>), RuntimeError> {
        let mut nested = context.clone();
        let mut names = binder_names.to_vec();
        let mut types = binder_types.to_vec();
        let nested_depth = context.forall_depth.map_or(0, |depth| depth + 1);
        nested.forall_depth = Some(nested_depth);
        let mut assumption_index = 0;
        for group in forall.params_def_with_type.groups.iter() {
            for binding in group.params.iter() {
                let name = lean_name(binding.name());
                nested.symbol_names.insert(binding.id(), name.clone());
                names.push(name.clone());
                types.push("Litex.Object".to_string());

                assumption_index += 1;
                let proof_name = generated_hypothesis_name(nested_depth, assumption_index);
                let proof_type =
                    self.render_parameter_requirement(&name, &group.param_type, &nested)?;
                names.push(proof_name.clone());
                types.push(proof_type.clone());
                for evidence in nested
                    .well_definedness
                    .parameter_facts
                    .iter()
                    .filter(|evidence| evidence.symbol_id == binding.id())
                {
                    // The runtime records only the exact parameter-definition
                    // output here.  Repeated verification phases may assign
                    // several FactIds to that same assumption.  Its rendered
                    // proposition can mention `obj_N` aliases for the binder
                    // or carrier, so textual equality with `proof_type` is
                    // intentionally not required: those aliases reduce to the
                    // same Lean terms by definition.
                    nested
                        .local_fact_names
                        .insert(evidence.fact_id, proof_name.clone());
                    nested
                        .local_fact_propositions
                        .insert(evidence.fact_id, evidence.proposition.clone());
                }

                if let ParamType::Obj(Obj::FnSet(function_set)) = &group.param_type {
                    let function = LitexToLeanFunctionTypeIr::lower(function_set)
                        .map_err(|message| universal_error(&forall.line_file, message))?;
                    for evidence in nested
                        .well_definedness
                        .parameter_facts
                        .iter()
                        .filter(|evidence| evidence.symbol_id == binding.id())
                    {
                        nested.function_bindings.insert(
                            evidence.fact_id,
                            FunctionBinding {
                                function: function.clone(),
                                membership_proof_name: proof_name.clone(),
                                uses_fn_space: function_ir_uses_fn_space(&function),
                            },
                        );
                    }
                }
            }
        }
        Ok((nested, names, types))
    }

    fn render_proof_term(
        &mut self,
        fact: &LitexToLeanFactIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match &fact.proof {
            LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => {
                if fact.fact_id == Some(*source_fact_id)
                    && matches!(
                        &fact.proposition,
                        Fact::AtomicFact(AtomicFact::EqualFact(equality))
                            if obj_equality_key(&equality.left)
                                == obj_equality_key(&equality.right)
                    )
                {
                    return Ok("rfl".to_string());
                }
                self.resolve_fact_id(*source_fact_id, context)
            }
            LitexToLeanFactProofIr::ExistentialAlphaRenameCitation {
                source_fact_id,
                source_proposition,
            } => {
                let binding = self.global_facts.get(source_fact_id).ok_or_else(|| {
                    universal_error(
                        &fact.proposition.line_file(),
                        format!(
                            "existential citation references unavailable FactId {source_fact_id}"
                        ),
                    )
                })?;
                if binding.proposition.to_string() != source_proposition.to_string()
                    || !self.one_witness_existentials_are_alpha_equal(
                        source_proposition,
                        &fact.proposition,
                        context,
                    )?
                {
                    return Err(universal_error(
                        &fact.proposition.line_file(),
                        "existential citation changed its retained source or alpha-equivalent target",
                    ));
                }
                self.resolve_fact_id(*source_fact_id, context)
            }
            LitexToLeanFactProofIr::Memo { proof } => {
                self.render_proof_node(&fact.proposition, proof.as_ref(), context)
            }
            proof => self.render_proof_node(&fact.proposition, proof, context),
        }
    }

    fn render_proof_node(
        &mut self,
        proposition: &Fact,
        proof: &LitexToLeanFactProofIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match proof {
            LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => {
                self.resolve_fact_id(*source_fact_id, context)
            }
            LitexToLeanFactProofIr::ExistentialAlphaRenameCitation {
                source_fact_id,
                source_proposition,
            } => {
                let binding = self.global_facts.get(source_fact_id).ok_or_else(|| {
                    universal_error(
                        &proposition.line_file(),
                        format!(
                            "existential citation references unavailable FactId {source_fact_id}"
                        ),
                    )
                })?;
                if binding.proposition.to_string() != source_proposition.to_string()
                    || !self.one_witness_existentials_are_alpha_equal(
                        source_proposition,
                        proposition,
                        context,
                    )?
                {
                    return Err(universal_error(
                        &proposition.line_file(),
                        "existential citation changed its retained source or alpha-equivalent target",
                    ));
                }
                self.resolve_fact_id(*source_fact_id, context)
            }
            LitexToLeanFactProofIr::Memo { proof } => {
                self.render_proof_node(proposition, proof.as_ref(), context)
            }
            LitexToLeanFactProofIr::RuleApplication {
                rule,
                parameter_requirements,
                premises,
            } => match rule {
                LitexToLeanProofRuleIr::ObjectReflexivity
                    if parameter_requirements.is_empty() && premises.is_empty() =>
                {
                    Ok("rfl".to_string())
                }
                LitexToLeanProofRuleIr::TupleLiteralIsTuple {
                    tuple,
                    expected_target,
                } => {
                    if !parameter_requirements.is_empty()
                        || !premises.is_empty()
                        || !facts_are_canonically_equal(proposition, expected_target)?
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "tuple-literal shape proof changed its target or retained premises",
                        ));
                    }
                    let LitexToLeanObjectIr::Collection {
                        constructor: LitexToLeanCollectionObjectIr::Tuple,
                        items,
                        ..
                    } = tuple
                    else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "tuple-literal shape proof retained a non-tuple object",
                        ));
                    };
                    let rendered_items = items
                        .iter()
                        .map(|item| self.render_obj_ir(item, context))
                        .collect::<Result<Vec<_>, _>>()?;
                    let tuple_term = self.render_obj_ir(tuple, context)?;
                    if self.render_fact(proposition, context)?
                        != format!("Litex.IsTuple {tuple_term}")
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "tuple-literal shape proof changed its exact literal",
                        ));
                    }
                    Ok(format!(
                        "(Litex.tupleLiteralIsTuple [{}])",
                        rendered_items.join(", ")
                    ))
                }
                LitexToLeanProofRuleIr::TupleLiteralDimension {
                    tuple,
                    expected_target,
                } => {
                    if !parameter_requirements.is_empty()
                        || !premises.is_empty()
                        || !facts_are_canonically_equal(proposition, expected_target)?
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "tuple-literal dimension proof changed its target or retained premises",
                        ));
                    }
                    let LitexToLeanObjectIr::Collection {
                        constructor: LitexToLeanCollectionObjectIr::Tuple,
                        items,
                        ..
                    } = tuple
                    else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "tuple-literal dimension proof retained a non-tuple object",
                        ));
                    };
                    let rendered_items = items
                        .iter()
                        .map(|item| self.render_obj_ir(item, context))
                        .collect::<Result<Vec<_>, _>>()?;
                    let forward =
                        format!("(Litex.tupleLiteral_dim [{}])", rendered_items.join(", "));
                    let tuple_term = self.render_obj_ir(tuple, context)?;
                    let expected_forward =
                        format!("(Litex.tupleDim {tuple_term}) = {}", items.len());
                    let target = self.render_fact(proposition, context)?;
                    if target == expected_forward {
                        Ok(forward)
                    } else if target == format!("{} = (Litex.tupleDim {tuple_term})", items.len()) {
                        Ok(format!("Eq.symm {forward}"))
                    } else {
                        Err(universal_error(
                            &proposition.line_file(),
                            "tuple-literal dimension proof changed its exact literal or arity",
                        ))
                    }
                }
                LitexToLeanProofRuleIr::ClosedStandardMembership => {
                    if !parameter_requirements.is_empty() || !premises.is_empty() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "closed numeral membership unexpectedly retained premises",
                        ));
                    }
                    render_closed_standard_membership(self, proposition, context)
                }
                LitexToLeanProofRuleIr::ClosedRealMembership => {
                    if !parameter_requirements.is_empty()
                        || !premises.is_empty()
                        || !crate::litex_to_lean_ir::is_closed_real_membership(proposition)
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "closed real membership changed its target or retained unexpected premises",
                        ));
                    }
                    render_closed_standard_membership(self, proposition, context)
                }
                LitexToLeanProofRuleIr::ClosedNumericReflection { target_set } => self
                    .render_closed_numeric_reflection(
                        proposition,
                        *target_set,
                        parameter_requirements,
                        premises,
                        context,
                    ),
                LitexToLeanProofRuleIr::RealSetNonempty => {
                    if !parameter_requirements.is_empty()
                        || !premises.is_empty()
                        || self.render_fact(proposition, context)? != "Litex.IsNonemptySet Litex.R"
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "real-set nonemptiness changed its target or retained unexpected premises",
                        ));
                    }
                    Ok(rule_theorem_name("realSetNonempty"))
                }
                LitexToLeanProofRuleIr::ObjectIsSet => {
                    if !parameter_requirements.is_empty() || !premises.is_empty() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "object-sethood evidence retained unexpected premises",
                        ));
                    }
                    let Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) = proposition else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "object-sethood evidence targets a non-sethood proposition",
                        ));
                    };
                    Ok(format!(
                        "{} {}",
                        rule_theorem_name("objectIsSet"),
                        self.render_obj(&sethood.set, context)?
                    ))
                }
                LitexToLeanProofRuleIr::ClassicalExcludedMiddle => {
                    if !parameter_requirements.is_empty() || !premises.is_empty() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "excluded-middle evidence retained unexpected premises",
                        ));
                    }
                    let Fact::OrFact(disjunction) = proposition else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "excluded-middle evidence targets a non-disjunction",
                        ));
                    };
                    if disjunction.facts.len() != 2 {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "excluded-middle evidence requires two branches",
                        ));
                    }
                    let (
                        AndChainAtomicFact::AtomicFact(first),
                        AndChainAtomicFact::AtomicFact(second),
                    ) = (&disjunction.facts[0], &disjunction.facts[1])
                    else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "excluded-middle evidence requires atomic complementary branches",
                        ));
                    };
                    let negated = first.logical_negation().map_err(|_| {
                        universal_error(
                            &proposition.line_file(),
                            "excluded-middle first branch has no atomic logical negation",
                        )
                    })?;
                    if negated.to_string() != second.to_string() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "excluded-middle branches are not logical complements",
                        ));
                    }
                    let first = self.render_atomic_fact(first, context)?;
                    Ok(format!("Classical.em ({first})"))
                }
                LitexToLeanProofRuleIr::ClosedNumericComparison { expected_target } => self
                    .render_closed_numeric_comparison(
                        proposition,
                        expected_target,
                        parameter_requirements,
                        premises,
                        context,
                    ),
                LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::NotEqualSymmetry) => self
                    .render_not_equal_symmetry(
                        proposition,
                        parameter_requirements,
                        premises,
                        context,
                    ),
                LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::ComplexArithmeticMembershipClosure(rule),
                ) => self.render_complex_arithmetic_membership(
                    proposition,
                    *rule,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::IntegerMembershipClosure(rule),
                ) => self.render_integer_arithmetic_membership(
                    proposition,
                    *rule,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::StandardSetMembershipProjection,
                ) => self.render_standard_set_membership_projection(
                    proposition,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::NativeConstantMembership(rule),
                ) => self.render_native_constant_membership(
                    proposition,
                    *rule,
                    parameter_requirements,
                    premises,
                ),
                LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::PositiveRealMembership,
                ) => self.render_positive_real_membership(
                    proposition,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::Builtin(
                    LitexToLeanBuiltinRuleIr::RealArithmeticMembershipClosure(rule),
                ) => self.render_real_arithmetic_membership(
                    proposition,
                    *rule,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::FunctionApplicationReturnMembership {
                    source_application,
                    function_set,
                    typed_return_set,
                    expected_target,
                    expected_head_membership,
                } => self.render_function_application_return_membership(
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
                LitexToLeanProofRuleIr::SetBuilderMembership {
                    set_builder,
                    expected_target,
                    expected_premises,
                } => self.render_set_builder_membership(
                    proposition,
                    set_builder,
                    expected_target,
                    expected_premises,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::EqualityRewrite(rewrite) => {
                    if !parameter_requirements.is_empty() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "equality rewrite unexpectedly retained parameter requirements",
                        ));
                    }
                    if premises.len() != rewrite.steps.len() + 1 {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "equality-rewrite evidence has the wrong premise arity",
                        ));
                    }
                    let source = self.render_proof_term(&premises[0], context)?;
                    let mut equalities = Vec::new();
                    for equality in premises.iter().skip(1) {
                        equalities.push(self.render_proof_term(equality, context)?);
                    }
                    Ok(format!(
                        "by simpa only [{}] using ({source})",
                        equalities.join(", ")
                    ))
                }
                LitexToLeanProofRuleIr::KnownEqualityPath(path) => self.render_known_equality_path(
                    proposition,
                    path,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::KnownForallInstantiation {
                    source_fact_id,
                    arguments,
                } => self.render_known_forall_instantiation(
                    proposition,
                    *source_fact_id,
                    arguments,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::AndIntroduction => {
                    if !parameter_requirements.is_empty() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "conjunction introduction retained parameter requirements",
                        ));
                    }
                    let components = conjunction_components(proposition)?;
                    if components.len() != premises.len()
                        || components
                            .iter()
                            .zip(premises.iter())
                            .any(|(expected, actual)| {
                                expected.to_string() != actual.proposition.to_string()
                            })
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "conjunction introduction changed its ordered component proofs",
                        ));
                    }
                    let mut rendered = Vec::with_capacity(premises.len());
                    for premise in premises {
                        rendered.push(self.render_proof_term(premise, context)?);
                    }
                    right_associated_conjunction_proof(rendered).ok_or_else(|| {
                        universal_error(
                            &proposition.line_file(),
                            "conjunction introduction retained no component proofs",
                        )
                    })
                }
                LitexToLeanProofRuleIr::DisjunctionIntroduction {
                    expected_target,
                    expected_selected,
                    selected_index,
                } => {
                    if !parameter_requirements.is_empty()
                        || premises.len() != 1
                        || !facts_are_canonically_equal(proposition, expected_target)?
                        || !facts_are_canonically_equal(
                            &premises[0].proposition,
                            expected_selected,
                        )?
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "disjunction introduction changed its target, selected proof, or premise arity",
                        ));
                    }
                    let Fact::OrFact(disjunction) = expected_target else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "disjunction introduction retained a non-disjunction target",
                        ));
                    };
                    let Some(selected) = disjunction.facts.get(*selected_index) else {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "disjunction introduction selected an out-of-range branch",
                        ));
                    };
                    let selected: Fact = selected.clone().into();
                    if !facts_are_canonically_equal(&selected, expected_selected)? {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "disjunction introduction selected a different branch proposition",
                        ));
                    }
                    let proof = self.render_proof_term(&premises[0], context)?;
                    Ok(right_associated_disjunction_injection(
                        proof,
                        *selected_index,
                        disjunction.facts.len(),
                    ))
                }
                LitexToLeanProofRuleIr::ConjunctionProjection {
                    expected_source,
                    expected_target,
                    index,
                    count,
                } => {
                    if !parameter_requirements.is_empty()
                        || premises.len() != 1
                        || !facts_are_canonically_equal(proposition, expected_target)?
                        || !facts_are_canonically_equal(&premises[0].proposition, expected_source)?
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "conjunction projection changed its source, target, or premise arity",
                        ));
                    }
                    let components = match expected_source {
                        Fact::AndFact(and_fact) => and_fact
                            .facts
                            .iter()
                            .cloned()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                        Fact::ChainFact(chain_fact) => chain_fact
                            .facts()?
                            .into_iter()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                        _ => {
                            return Err(universal_error(
                                &expected_source.line_file(),
                                "conjunction projection retained a non-conjunctive source",
                            ));
                        }
                    };
                    if components.len() != *count
                        || *index >= components.len()
                        || !facts_are_canonically_equal(&components[*index], expected_target)?
                    {
                        return Err(universal_error(
                            &expected_target.line_file(),
                            "conjunction projection changed its retained component position",
                        ));
                    }
                    let source = self.render_proof_term(&premises[0], context)?;
                    Ok(conjunction_projection(
                        &format!("({source})"),
                        *index,
                        *count,
                    ))
                }
                LitexToLeanProofRuleIr::ExistIntroduction {
                    witnesses,
                    steps,
                    expected_parameter_requirements,
                    expected_body_facts,
                } => self.render_exist_introduction(
                    proposition,
                    witnesses,
                    steps,
                    expected_parameter_requirements,
                    expected_body_facts,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::ComparisonNotationDuality {
                    expected_source,
                    expected_target,
                } => {
                    if !parameter_requirements.is_empty()
                        || premises.len() != 1
                        || !facts_are_canonically_equal(proposition, expected_target)?
                        || !facts_are_canonically_equal(&premises[0].proposition, expected_source)?
                        || !crate::litex_to_lean_ir::facts_are_comparison_notation_duals(
                            expected_source,
                            expected_target,
                        )
                    {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "comparison-notation duality changed its exact source or target",
                        ));
                    }
                    let source_type = self.render_fact(expected_source, context)?;
                    let target_type = self.render_fact(expected_target, context)?;
                    if source_type != target_type {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "comparison-notation duals rendered to different Lean propositions",
                        ));
                    }
                    self.render_proof_term(&premises[0], context)
                }
                LitexToLeanProofRuleIr::CheckedFunctionDefinitionReduction {
                    definition,
                    defining_equality_fact_id,
                    defining_equality,
                    expected_target,
                    application_side,
                    reduced,
                    other_side,
                    application_is_left,
                    reduced_matches_other_by_alpha,
                } => self.render_checked_function_definition_reduction(
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
                LitexToLeanProofRuleIr::DefinitionReduction {
                    definition,
                    expected_parameter_requirements,
                    expected_clauses,
                } => self.render_definition_reduction(
                    proposition,
                    definition,
                    expected_parameter_requirements,
                    expected_clauses,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::DefinitionProjection {
                    definition,
                    expected_source,
                    expected_target,
                } => self.render_definition_projection(
                    proposition,
                    definition,
                    expected_source,
                    expected_target,
                    parameter_requirements,
                    premises,
                    context,
                ),
                LitexToLeanProofRuleIr::Normalization {
                    kind: LitexToLeanNormalizationKindIr::RationalExpressionSimplification,
                } => {
                    if !parameter_requirements.is_empty() || premises.len() != 1 {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "rational normalization requires one retained source proof and no parameter requirements",
                        ));
                    }
                    let source = self.render_proof_term(&premises[0], context)?;
                    let mut object_aliases = context
                        .well_defined_object_names
                        .values()
                        .filter_map(|applied_name| {
                            let trimmed = applied_name.trim_start_matches('(');
                            trimmed.strip_prefix("__obj").and_then(|rest| {
                                let digits = rest
                                    .chars()
                                    .take_while(|character| character.is_ascii_digit())
                                    .collect::<String>();
                                (!digits.is_empty()).then(|| format!("__obj{digits}"))
                            })
                        })
                        .collect::<Vec<_>>();
                    object_aliases.sort();
                    object_aliases.dedup();
                    let alias_simp = if object_aliases.is_empty() {
                        String::new()
                    } else {
                        format!(", {}", object_aliases.join(", "))
                    };
                    Ok(format!(
                        "(by\n  convert ({source}) using 1 <;>\n    simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex{alias_simp}] <;>\n    norm_num)"
                    ))
                }
                other => Err(universal_error(
                    &proposition.line_file(),
                    format!("the universal-object MVP does not yet emit proof rule `{other:?}`"),
                )),
            },
            LitexToLeanFactProofIr::CaseSplit { coverage, branches } => {
                self.render_case_split(proposition, coverage, branches, context)
            }
            LitexToLeanFactProofIr::ByContradiction {
                reverse_assumption,
                block,
                contradiction,
            } => self.render_by_contradiction(
                proposition,
                reverse_assumption,
                block,
                contradiction,
                context,
            ),
            LitexToLeanFactProofIr::Composite { steps } if steps.len() == 1 => {
                self.render_proof_term(&steps[0], context)
            }
            LitexToLeanFactProofIr::Trusted => Err(universal_error(
                &proposition.line_file(),
                "trusted universal-object facts require explicit axiom emission",
            )),
            other => Err(universal_error(
                &proposition.line_file(),
                format!("the universal-object MVP does not yet emit proof `{other:?}`"),
            )),
        }
    }

    fn render_local_proof_block(
        &mut self,
        block: &LitexToLeanLocalProofBlockIr,
        context: &mut RenderContext,
        name_prefix: &str,
    ) -> Result<Vec<LocalProofStep>, RuntimeError> {
        crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
            &block.well_definedness,
        )
        .map_err(|message| universal_error(&default_line_file(), message))?;

        for alias in block.premise_aliases.iter() {
            let parent_proposition = context
                .local_fact_propositions
                .get(&alias.parent_fact_id)
                .or_else(|| {
                    self.global_facts
                        .get(&alias.parent_fact_id)
                        .map(|binding| &binding.proposition)
                })
                .ok_or_else(|| {
                    universal_error(
                        &alias.expected_fact.line_file(),
                        format!(
                            "local premise alias references unavailable parent FactId {}",
                            alias.parent_fact_id.value()
                        ),
                    )
                })?;
            if !facts_are_canonically_equal(parent_proposition, &alias.expected_fact)? {
                return Err(universal_error(
                    &alias.expected_fact.line_file(),
                    "local premise alias changed its parent proposition",
                ));
            }
            let proof_name = self.resolve_fact_id(alias.parent_fact_id, context)?;
            context
                .local_fact_names
                .insert(alias.local_fact_id, proof_name.clone());
            context
                .local_fact_propositions
                .insert(alias.local_fact_id, alias.expected_fact.clone());
            self.register_local_function_binding(
                context,
                alias.local_fact_id,
                &alias.expected_fact,
                proof_name,
            )?;
        }

        let mut local_steps = Vec::new();
        let mut local_index = 0;
        for inferred in block.assumption_inferred_facts.iter() {
            local_index += 1;
            self.bind_local_proof_fact(
                inferred,
                &block.well_definedness,
                context,
                &mut local_steps,
                &format!("{name_prefix}_{local_index}"),
            )?;
        }
        for statement in block.steps.iter() {
            let facts = statement_proof_facts(statement).ok_or_else(|| {
                universal_error(
                    &statement_line_file(statement),
                    format!(
                        "local proof blocks do not yet emit statement `{}`",
                        statement_label(statement)
                    ),
                )
            })?;
            let default_certificate = LitexToLeanWellDefinednessCertificateIr::default();
            let certificate = match statement {
                LitexToLeanStatementIr::Fact(ir) => &ir.well_definedness,
                LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(ir)) => {
                    &ir.well_definedness
                }
                LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(ir)) => {
                    &ir.well_definedness
                }
                LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(ir)) => {
                    &ir.well_definedness
                }
                LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessExistFact(ir)) => {
                    &ir.well_definedness
                }
                LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessAtomicFact(
                    ir,
                )) => &ir.well_definedness,
                _ => &default_certificate,
            };
            crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                certificate,
            )
            .map_err(|message| universal_error(&statement_line_file(statement), message))?;
            for fact in facts {
                local_index += 1;
                self.bind_local_proof_fact(
                    fact,
                    certificate,
                    context,
                    &mut local_steps,
                    &format!("{name_prefix}_{local_index}"),
                )?;
            }
        }
        Ok(local_steps)
    }

    fn bind_local_proof_fact(
        &mut self,
        fact: &LitexToLeanFactIr,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
        context: &mut RenderContext,
        local_steps: &mut Vec<LocalProofStep>,
        name: &str,
    ) -> Result<(), RuntimeError> {
        let fact_id = fact.fact_id.ok_or_else(|| {
            universal_error(
                &fact.proposition.line_file(),
                "a local proof statement effect has no FactId",
            )
        })?;
        self.prepare_local_fact_well_definedness(fact, certificate, context, local_steps)?;
        let proposition = self.render_fact(&fact.proposition, context)?;
        let proof = self.render_proof_term(fact, context)?;
        push_unique_local_proof_step(
            local_steps,
            LocalProofStep {
                name: name.to_string(),
                proposition,
                proof,
            },
        )?;
        context.local_fact_names.insert(fact_id, name.to_string());
        context
            .local_fact_propositions
            .insert(fact_id, fact.proposition.clone());
        self.register_local_function_binding(context, fact_id, &fact.proposition, name.to_string())
    }

    fn prepare_local_fact_well_definedness(
        &mut self,
        fact: &LitexToLeanFactIr,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
        context: &mut RenderContext,
        local_steps: &mut Vec<LocalProofStep>,
    ) -> Result<(), RuntimeError> {
        let parent_certificate =
            std::mem::replace(&mut context.well_definedness, certificate.clone());
        let prepared = self
            .prepare_local_well_defined_facts_for_fact_type(
                context,
                &fact.proposition,
                &[],
                &[],
                local_steps,
            )
            .and_then(|_| {
                self.prepare_local_well_defined_facts_for_fact_proof(
                    context,
                    fact,
                    &[],
                    &[],
                    local_steps,
                )
            });
        context.well_definedness = parent_certificate;
        prepared
    }

    fn register_local_function_binding(
        &self,
        context: &mut RenderContext,
        fact_id: FactId,
        proposition: &Fact,
        proof_name: String,
    ) -> Result<(), RuntimeError> {
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Ok(());
        };
        let Obj::FnSet(function_set) = &membership.set else {
            return Ok(());
        };
        let function = LitexToLeanFunctionTypeIr::lower(function_set)
            .map_err(|message| universal_error(&proposition.line_file(), message))?;
        if let Some(existing) = context.function_bindings.get(&fact_id) {
            if existing.function != function || existing.membership_proof_name != proof_name {
                return Err(universal_error(
                    &proposition.line_file(),
                    format!(
                        "local function membership FactId {} was rebound to a different contract",
                        fact_id.value()
                    ),
                ));
            }
            return Ok(());
        }
        let uses_fn_space = function_ir_uses_fn_space(&function);
        context.function_bindings.insert(
            fact_id,
            FunctionBinding {
                function,
                membership_proof_name: proof_name,
                uses_fn_space,
            },
        );
        Ok(())
    }

    fn render_case_split(
        &mut self,
        proposition: &Fact,
        coverage: &LitexToLeanFactIr,
        branches: &[LitexToLeanCaseBranchIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let Fact::OrFact(disjunction) = &coverage.proposition else {
            return Err(universal_error(
                &coverage.proposition.line_file(),
                "case split retained non-disjunctive coverage",
            ));
        };
        if disjunction.facts.is_empty() || disjunction.facts.len() != branches.len() {
            return Err(universal_error(
                &proposition.line_file(),
                "case-split coverage and retained branch counts do not match",
            ));
        }
        let coverage_proof = if facts_are_canonically_equal(&coverage.proposition, proposition)?
            && matches!(
                proposition,
                Fact::AtomicFact(AtomicFact::EqualFact(equality))
                    if obj_equality_key(&equality.left) == obj_equality_key(&equality.right)
            ) {
            "rfl".to_string()
        } else {
            self.render_proof_term(coverage, context)?
        };
        let names = (0..branches.len())
            .map(|index| format!("__case{}", index + 1))
            .collect::<Vec<_>>();
        let mut lines = vec!["by".to_string()];
        if names.len() == 1 {
            let case_type = self.render_fact(&branches[0].assumption.fact, context)?;
            lines.push(format!(
                "  have {} : {case_type} := {coverage_proof}",
                names[0]
            ));
        } else {
            lines.push(format!(
                "  rcases ({coverage_proof}) with {}",
                names.join(" | ")
            ));
        }
        for (index, branch) in branches.iter().enumerate() {
            let expected_assumption: Fact = disjunction.facts[index].clone().into();
            if !facts_are_canonically_equal(&branch.assumption.fact, &expected_assumption)? {
                return Err(universal_error(
                    &branch.assumption.fact.line_file(),
                    "case branch assumption does not match its coverage position",
                ));
            }
            let mut nested = context.clone();
            nested
                .local_fact_names
                .insert(branch.assumption.fact_id, names[index].clone());
            nested
                .local_fact_propositions
                .insert(branch.assumption.fact_id, branch.assumption.fact.clone());
            self.register_local_function_binding(
                &mut nested,
                branch.assumption.fact_id,
                &branch.assumption.fact,
                names[index].clone(),
            )?;
            let mut local_steps = self.render_local_proof_block(
                &branch.block,
                &mut nested,
                &format!("__case{}_step", index + 1),
            )?;
            let exit = match &branch.exit {
                LitexToLeanCaseBranchExitIr::Conclusion(conclusion) => {
                    if !facts_are_canonically_equal(&conclusion.proposition, proposition)? {
                        return Err(universal_error(
                            &conclusion.proposition.line_file(),
                            "case branch conclusion changed the exported goal",
                        ));
                    }
                    self.prepare_local_fact_well_definedness(
                        conclusion,
                        &branch.block.well_definedness,
                        &mut nested,
                        &mut local_steps,
                    )?;
                    self.render_proof_term(conclusion, &nested)?
                }
                LitexToLeanCaseBranchExitIr::Contradiction(contradiction) => {
                    self.prepare_local_fact_well_definedness(
                        &contradiction.fact,
                        &branch.block.well_definedness,
                        &mut nested,
                        &mut local_steps,
                    )?;
                    self.prepare_local_fact_well_definedness(
                        &contradiction.negated_fact,
                        &branch.block.well_definedness,
                        &mut nested,
                        &mut local_steps,
                    )?;
                    format!(
                        "False.elim ({})",
                        self.render_contradiction_term(contradiction, &nested)?
                    )
                }
            };
            if names.len() == 1 {
                for step in local_steps.iter() {
                    lines.push(render_local_proof_step_at_indent(step, 2));
                }
                lines.push(format!("  exact {exit}"));
            } else {
                lines.push("  ·".to_string());
                for step in local_steps.iter() {
                    lines.push(render_local_proof_step_at_indent(step, 4));
                }
                lines.push(format!("    exact {exit}"));
            }
        }
        Ok(format!("({})", lines.join("\n")))
    }

    fn render_by_contradiction(
        &mut self,
        proposition: &Fact,
        reverse_assumption: &LitexToLeanReverseAssumptionIr,
        block: &LitexToLeanLocalProofBlockIr,
        contradiction: &LitexToLeanContradictionIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let Fact::AtomicFact(target) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "the current by-contradiction emitter requires an atomic goal",
            ));
        };
        let target_is_negated = matches!(
            target,
            AtomicFact::NotNormalAtomicFact(_)
                | AtomicFact::NotEqualFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessEqualFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
                | AtomicFact::NotIsSetFact(_)
                | AtomicFact::NotIsNonemptySetFact(_)
                | AtomicFact::NotIsFiniteSetFact(_)
                | AtomicFact::NotInFact(_)
                | AtomicFact::NotIsCartFact(_)
                | AtomicFact::NotIsTupleFact(_)
                | AtomicFact::NotSubsetFact(_)
                | AtomicFact::NotSupersetFact(_)
        );
        let expected_introduction = if target_is_negated {
            LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation
        } else {
            LitexToLeanReverseAssumptionIntroductionIr::DirectNegation
        };
        if reverse_assumption.introduction != expected_introduction {
            return Err(universal_error(
                &proposition.line_file(),
                "by-contradiction reverse-assumption introduction changed target polarity",
            ));
        }
        let negated = target.logical_negation().map_err(|_| {
            universal_error(
                &proposition.line_file(),
                "by-contradiction target has no atomic logical negation",
            )
        })?;
        if !facts_are_canonically_equal(
            &reverse_assumption.premise.fact,
            &Fact::AtomicFact(negated),
        )? {
            return Err(universal_error(
                &reverse_assumption.premise.fact.line_file(),
                "by-contradiction reverse assumption is not the negated target",
            ));
        }
        let name = "__reverse";
        let mut nested = context.clone();
        let mut lines = vec!["by".to_string(), "  classical".to_string()];
        let local_indent = match reverse_assumption.introduction {
            LitexToLeanReverseAssumptionIntroductionIr::DirectNegation => {
                lines.push(format!("  by_contra {name}"));
                2
            }
            LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation => {
                let negated_goal = "__negated_goal";
                let reverse_type = self.render_fact(&reverse_assumption.premise.fact, &nested)?;
                lines.push(format!(
                    "  exact Classical.byContradiction (fun {negated_goal} => by"
                ));
                lines.push(format!(
                    "    have {name} : {reverse_type} := Classical.byContradiction (fun __not_reverse => {negated_goal} __not_reverse)"
                ));
                4
            }
        };
        nested
            .local_fact_names
            .insert(reverse_assumption.premise.fact_id, name.to_string());
        nested.local_fact_propositions.insert(
            reverse_assumption.premise.fact_id,
            reverse_assumption.premise.fact.clone(),
        );
        self.register_local_function_binding(
            &mut nested,
            reverse_assumption.premise.fact_id,
            &reverse_assumption.premise.fact,
            name.to_string(),
        )?;
        let mut local_steps = self.render_local_proof_block(block, &mut nested, "__contra_step")?;
        self.prepare_local_fact_well_definedness(
            &contradiction.fact,
            &block.well_definedness,
            &mut nested,
            &mut local_steps,
        )?;
        self.prepare_local_fact_well_definedness(
            &contradiction.negated_fact,
            &block.well_definedness,
            &mut nested,
            &mut local_steps,
        )?;
        for step in local_steps.iter() {
            lines.push(render_local_proof_step_at_indent(step, local_indent));
        }
        let contradiction = self.render_contradiction_term(contradiction, &nested)?;
        let close_double_negation = if matches!(
            reverse_assumption.introduction,
            LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation
        ) {
            ")"
        } else {
            ""
        };
        lines.push(format!(
            "{}exact {contradiction}{close_double_negation}",
            " ".repeat(local_indent)
        ));
        Ok(format!("({})", lines.join("\n")))
    }

    fn render_contradiction_term(
        &mut self,
        contradiction: &LitexToLeanContradictionIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let Fact::AtomicFact(fact) = &contradiction.fact.proposition else {
            return Err(universal_error(
                &contradiction.fact.proposition.line_file(),
                "contradiction retained a non-atomic positive fact",
            ));
        };
        let expected_negation = fact.logical_negation().map_err(|_| {
            universal_error(
                &contradiction.fact.proposition.line_file(),
                "contradiction fact has no atomic logical negation",
            )
        })?;
        if !facts_are_canonically_equal(
            &contradiction.negated_fact.proposition,
            &Fact::AtomicFact(expected_negation),
        )? {
            return Err(universal_error(
                &contradiction.negated_fact.proposition.line_file(),
                "contradiction retained facts that are not logical complements",
            ));
        }
        let fact = self.render_proof_term(&contradiction.fact, context)?;
        let negated = self.render_proof_term(&contradiction.negated_fact, context)?;
        if matches!(
            &contradiction.fact.proposition,
            Fact::AtomicFact(AtomicFact::NotEqualFact(_))
        ) {
            let function_type = self.render_fact(&contradiction.fact.proposition, context)?;
            Ok(format!("(({fact}) : {function_type}) ({negated})"))
        } else {
            let function_type =
                self.render_fact(&contradiction.negated_fact.proposition, context)?;
            Ok(format!("(({negated}) : {function_type}) ({fact})"))
        }
    }

    fn render_exist_introduction(
        &mut self,
        proposition: &Fact,
        witnesses: &[Obj],
        steps: &[LitexToLeanStatementIr],
        expected_parameter_requirements: &[Fact],
        expected_body_facts: &[Fact],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let Fact::ExistFact(existential) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "existential introduction targets a non-existential proposition",
            ));
        };
        if !existential.is_plain_exist()
            || witnesses.len() != 1
            || existential.params_def_with_type().number_of_params() != 1
            || existential.facts().len() != 1
            || expected_parameter_requirements.len() != 1
            || expected_body_facts.len() != 1
            || parameter_requirements.len() != 1
            || premises.len() != 1
        {
            return Err(universal_error(
                &proposition.line_file(),
                "the current existential-introduction emitter requires one witness, one type proof, and one body proof",
            ));
        }
        if !facts_are_canonically_equal(
            &parameter_requirements[0].proposition,
            &expected_parameter_requirements[0],
        )? || !facts_are_canonically_equal(&premises[0].proposition, &expected_body_facts[0])?
        {
            return Err(universal_error(
                &proposition.line_file(),
                "existential-introduction evidence changed its retained type or body facts",
            ));
        }

        let group = &existential.params_def_with_type().groups[0];
        if group.params.len() != 1 {
            return Err(universal_error(
                &proposition.line_file(),
                "existential-introduction target has a nonsingleton parameter group",
            ));
        }
        let witness = self.render_obj(&witnesses[0], context)?;
        let mut instantiated = context.clone();
        instantiated
            .symbol_names
            .insert(group.params[0].id(), witness.clone());
        let expected_requirement =
            self.render_parameter_requirement(&witness, &group.param_type, &instantiated)?;
        let expected_body = self.render_fact(
            &existential.facts()[0].from_ref_to_cloned_fact(),
            &instantiated,
        )?;
        if self.render_fact(&parameter_requirements[0].proposition, context)?
            != expected_requirement
            || self.render_fact(&premises[0].proposition, context)? != expected_body
        {
            return Err(universal_error(
                &proposition.line_file(),
                "existential-introduction witness does not instantiate its retained target facts",
            ));
        }

        let mut nested = context.clone();
        let mut lines = vec!["by".to_string()];
        let mut step_index = 0;
        for step in steps {
            let facts = statement_proof_facts(step).ok_or_else(|| {
                universal_error(
                    &statement_line_file(step),
                    format!(
                        "existential-introduction proof steps do not yet emit statement `{}`",
                        statement_label(step)
                    ),
                )
            })?;
            for fact in facts {
                step_index += 1;
                let name = format!("__exist_step{step_index}");
                let fact_type = self.render_fact(&fact.proposition, &nested)?;
                let proof = self.render_proof_term(fact, &nested)?;
                lines.push(format!(
                    "  have {name} : {fact_type} := by\n    exact {proof}"
                ));
                if let Some(fact_id) = fact.fact_id {
                    nested.local_fact_names.insert(fact_id, name);
                    nested
                        .local_fact_propositions
                        .insert(fact_id, fact.proposition.clone());
                }
            }
        }
        let requirement_proof = self.render_proof_term(&parameter_requirements[0], &nested)?;
        let body_proof = self.render_proof_term(&premises[0], &nested)?;
        lines.push(format!(
            "  exact ⟨{witness}, ({requirement_proof}), ({body_proof})⟩"
        ));
        Ok(format!("({})", lines.join("\n")))
    }

    fn render_closed_numeric_comparison(
        &self,
        proposition: &Fact,
        expected_target: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || !premises.is_empty()
            || !facts_are_canonically_equal(proposition, expected_target)?
            || !crate::litex_to_lean_ir::is_closed_numeric_relation(proposition)
        {
            return Err(universal_error(
                &proposition.line_file(),
                "closed numeric comparison changed its target or retained unexpected premises",
            ));
        }
        self.render_fact(proposition, context)?;
        let Fact::AtomicFact(atomic) = proposition else {
            unreachable!("closed numeric comparisons were checked above")
        };
        let (theorem, left, right, negated) = match atomic {
            AtomicFact::NotEqualFact(fact) => ("numeralNe", &fact.left, &fact.right, false),
            AtomicFact::LessFact(fact) => ("numeralLt", &fact.left, &fact.right, false),
            AtomicFact::GreaterFact(fact) => ("numeralLt", &fact.right, &fact.left, false),
            AtomicFact::LessEqualFact(fact) => ("numeralLe", &fact.left, &fact.right, false),
            AtomicFact::GreaterEqualFact(fact) => ("numeralLe", &fact.right, &fact.left, false),
            AtomicFact::NotLessFact(fact) => ("numeralLt", &fact.left, &fact.right, true),
            AtomicFact::NotGreaterFact(fact) => ("numeralLt", &fact.right, &fact.left, true),
            AtomicFact::NotLessEqualFact(fact) => ("numeralLe", &fact.left, &fact.right, true),
            AtomicFact::NotGreaterEqualFact(fact) => ("numeralLe", &fact.right, &fact.left, true),
            _ => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "closed equality reflection needs a separate object-embedding proof adapter",
                ))
            }
        };
        let left = natural_number_literal(left).ok_or_else(|| {
            universal_error(
                &proposition.line_file(),
                "closed comparison reflection currently requires natural numeral operands",
            )
        })?;
        let right = natural_number_literal(right).ok_or_else(|| {
            universal_error(
                &proposition.line_file(),
                "closed comparison reflection currently requires natural numeral operands",
            )
        })?;
        let equivalence = format!("{} {left} {right}", rule_theorem_name(theorem));
        if negated {
            Ok(format!(
                "(by\n  exact (not_congr ({equivalence})).2 (by norm_num))"
            ))
        } else {
            Ok(format!("(by\n  exact ({equivalence}).2 (by norm_num))"))
        }
    }

    fn render_closed_numeric_reflection(
        &self,
        proposition: &Fact,
        target_set: LitexToLeanStandardSetIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || !premises.is_empty()
            || crate::litex_to_lean_ir::closed_compact_numeric_set_fact(proposition)
                != Some(target_set)
        {
            return Err(universal_error(
                &proposition.line_file(),
                "closed numeric reflection changed its target set or retained unexpected premises",
            ));
        }
        self.render_fact(proposition, context)?;
        if target_set != LitexToLeanStandardSetIr::PositiveNatural {
            return Err(universal_error(
                &proposition.line_file(),
                format!(
                    "closed numeric reflection for `{}` still needs a checked Lean theorem",
                    standard_set_name(target_set)
                ),
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "positive-natural reflection currently requires positive membership",
            ));
        };
        if !matches!(&membership.set, Obj::StandardSet(StandardSet::NPos)) {
            return Err(universal_error(
                &proposition.line_file(),
                "positive-natural reflection changed its exact target carrier",
            ));
        }
        let numeral = natural_number_literal(&membership.element).ok_or_else(|| {
            universal_error(
                &proposition.line_file(),
                "positive-natural reflection currently requires a natural numeral",
            )
        })?;
        Ok(format!(
            "({} {numeral} (by norm_num))",
            rule_theorem_name("numeralInNPos")
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn render_set_builder_membership(
        &mut self,
        proposition: &Fact,
        set_builder: &LitexToLeanObjectIr,
        expected_target: &Fact,
        expected_premises: &[Fact],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let LitexToLeanObjectIr::SetBuilder(builder) = set_builder else {
            return Err(universal_error(
                &proposition.line_file(),
                "set-builder membership retained a non-builder target object",
            ));
        };
        if !parameter_requirements.is_empty()
            || !facts_are_canonically_equal(proposition, expected_target)?
            || expected_premises.len() != premises.len()
            || premises.len() != builder.facts.len() + 1
        {
            return Err(universal_error(
                &proposition.line_file(),
                "set-builder membership changed its target or ordered premise arity",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "set-builder membership proof targets a non-membership fact",
            ));
        };
        if LitexToLeanObjectIr::lower(&target.set)
            .map_err(|message| universal_error(&proposition.line_file(), message))?
            != *set_builder
        {
            return Err(universal_error(
                &proposition.line_file(),
                "set-builder membership changed its exact builder object",
            ));
        }
        let mut rendered_proofs = Vec::with_capacity(premises.len());
        for (actual, expected) in premises.iter().zip(expected_premises.iter()) {
            if !facts_are_canonically_equal(&actual.proposition, expected)? {
                return Err(universal_error(
                    &proposition.line_file(),
                    "set-builder membership reordered or retargeted a premise",
                ));
            }
            rendered_proofs.push(self.render_proof_term(actual, context)?);
        }
        let base_proof = &rendered_proofs[0];
        let body_proof = if rendered_proofs.len() == 1 {
            "True.intro".to_string()
        } else {
            right_associated_conjunction_proof(rendered_proofs[1..].to_vec()).ok_or_else(|| {
                universal_error(
                    &proposition.line_file(),
                    "set-builder membership could not assemble its body conjunction",
                )
            })?
        };
        Ok(format!(
            "(Litex.inSetBuilder_iff.mpr (And.intro ({base_proof}) ({body_proof})))"
        ))
    }

    fn render_function_application_return_membership(
        &mut self,
        proposition: &Fact,
        source_application: &LitexToLeanObjectIr,
        function_set: &LitexToLeanObjectIr,
        typed_return_set: &LitexToLeanObjectIr,
        expected_target: &Fact,
        expected_head_membership: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || premises.len() != 1
            || !facts_are_canonically_equal(proposition, expected_target)?
            || !facts_are_canonically_equal(&premises[0].proposition, expected_head_membership)?
        {
            return Err(universal_error(
                &proposition.line_file(),
                "function-application return membership changed its target, head premise, or child-proof arity",
            ));
        }
        let LitexToLeanObjectIr::FunctionApplication(application) = source_application else {
            return Err(universal_error(
                &proposition.line_file(),
                "function-application return membership retained a non-application source",
            ));
        };
        let LitexToLeanObjectIr::FunctionSet {
            function: expected_function,
        } = function_set
        else {
            return Err(universal_error(
                &proposition.line_file(),
                "function-application return membership retained a non-function contract",
            ));
        };
        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = expected_target else {
            return Err(universal_error(
                &proposition.line_file(),
                "function-application return membership retained a non-membership target",
            ));
        };
        let lowered_target_element = LitexToLeanObjectIr::lower(&target_membership.element)
            .map_err(|message| universal_error(&proposition.line_file(), message))?;
        let lowered_target_set = LitexToLeanObjectIr::lower(&target_membership.set)
            .map_err(|message| universal_error(&proposition.line_file(), message))?;
        if &lowered_target_element != source_application || &lowered_target_set != typed_return_set
        {
            return Err(universal_error(
                &proposition.line_file(),
                "function-application return membership changed its source application or typed return set",
            ));
        }

        let head_membership_proof = self.render_proof_term(&premises[0], context)?;
        let rendered = self.render_function_application_with_result(
            application,
            context,
            Some(head_membership_proof),
        )?;
        if rendered.function != **expected_function {
            return Err(universal_error(
                &proposition.line_file(),
                format!(
                    "function-application return membership contract differs from verifier FactId {}",
                    rendered.contract_fact_id.value()
                ),
            ));
        }
        let retained_contract = context
            .local_fact_propositions
            .get(&rendered.contract_fact_id)
            .or_else(|| {
                self.global_facts
                    .get(&rendered.contract_fact_id)
                    .map(|binding| &binding.proposition)
            })
            .ok_or_else(|| {
                universal_error(
                    &proposition.line_file(),
                    format!(
                        "function contract FactId {} has no retained proposition",
                        rendered.contract_fact_id.value()
                    ),
                )
            })?;
        if !facts_are_canonically_equal(retained_contract, expected_head_membership)? {
            return Err(universal_error(
                &proposition.line_file(),
                format!(
                    "function contract FactId {} does not prove the retained head membership",
                    rendered.contract_fact_id.value()
                ),
            ));
        }
        Ok(rendered.result_membership)
    }

    #[allow(clippy::too_many_arguments)]
    fn render_checked_function_definition_reduction(
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
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || !premises.is_empty()
            || !facts_are_canonically_equal(proposition, expected_target)?
            || !reduced_matches_other_by_alpha
            || obj_equality_key(reduced) != obj_equality_key(other_side)
        {
            return Err(universal_error(
                &proposition.line_file(),
                "checked function reduction changed its target, result, or proof arity",
            ));
        }
        let LitexToLeanObjectIr::Symbol {
            name: source_name, ..
        } = definition
        else {
            return Err(universal_error(
                &proposition.line_file(),
                "checked function reduction retained a non-symbol definition",
            ));
        };
        let binding = self
            .global_facts
            .get(&defining_equality_fact_id)
            .ok_or_else(|| {
                universal_error(
                    &proposition.line_file(),
                    format!(
                        "checked function reduction cites unavailable defining FactId {defining_equality_fact_id}"
                    ),
                )
            })?;
        if !facts_are_canonically_equal(&binding.proposition, defining_equality)? {
            return Err(universal_error(
                &proposition.line_file(),
                "checked function reduction retargeted its defining equality FactId",
            ));
        }
        let helpers = self
            .named_function_helpers
            .get(source_name)
            .ok_or_else(|| {
                universal_error(
                    &proposition.line_file(),
                    format!("checked function reduction names unemitted function `{source_name}`"),
                )
            })?;
        let application_object_ir = LitexToLeanObjectIr::lower(application_side)
            .map_err(|message| universal_error(&proposition.line_file(), message))?;
        let LitexToLeanObjectIr::FunctionApplication(application_ir) = &application_object_ir
        else {
            return Err(universal_error(
                &proposition.line_file(),
                "checked function reduction retained a non-application side",
            ));
        };
        let object_id = context
            .well_defined_object_ids
            .get(&application_ir.source_occurrence_id)
            .copied()
            .ok_or_else(|| {
                universal_error(
                    &proposition.line_file(),
                    "checked function reduction has no exact application WellDefinedObjId",
                )
            })?;
        let applicable = context
            .well_defined_applicable_names
            .get(&object_id)
            .cloned()
            .ok_or_else(|| {
                universal_error(
                    &proposition.line_file(),
                    format!(
                        "checked function reduction has no local obj_{}_applicable proof",
                        object_id.value()
                    ),
                )
            })?;
        let application = self.render_obj_ir(&application_object_ir, context)?;
        let other = self.render_obj(other_side, context)?;
        let target = if application_is_left {
            format!("{application} = {other}")
        } else {
            format!("{other} = {application}")
        };
        let mut object_definition_names = helpers.body_object_definition_names.clone();
        for obj_id in context.well_defined_object_names.keys() {
            if let Some(object_binding) = self.global_objects.get(obj_id) {
                object_definition_names.push(object_binding.name.clone());
            }
        }
        object_definition_names.sort();
        object_definition_names.dedup();
        let mut simp_names = vec![helpers.body_name.clone()];
        simp_names.extend(object_definition_names);
        simp_names.extend([
            "Litex.arg".to_string(),
            "List.getD_cons_zero".to_string(),
            "List.getD_cons_succ".to_string(),
            "List.getD_nil".to_string(),
        ]);
        Ok(format!(
            "(by\n  change {target}\n  rw [{}]\n  unfold {}\n  rw [Litex.functionObject_apply _ _ _ (by\n    simpa only [{}, {}] using {})]\n  simp only [{}])",
            binding.theorem_name,
            helpers.implementation_name,
            binding.theorem_name,
            helpers.implementation_name,
            applicable,
            simp_names.join(", ")
        ))
    }

    fn render_definition_reduction(
        &mut self,
        proposition: &Fact,
        definition: &str,
        expected_parameter_requirements: &[Fact],
        expected_clauses: &[Fact],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if expected_parameter_requirements.len() != parameter_requirements.len()
            || expected_clauses.len() != premises.len()
        {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop reduction has the wrong child-proof arity",
            ));
        }
        let components =
            self.render_prop_application_components(proposition, definition, context)?;
        if components.len() != expected_parameter_requirements.len() + expected_clauses.len() {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop definition components changed before Lean emission",
            ));
        }

        let expected = expected_parameter_requirements
            .iter()
            .chain(expected_clauses.iter());
        let children = parameter_requirements.iter().chain(premises.iter());
        let mut proofs = Vec::with_capacity(components.len());
        for ((expected, child), component) in expected.zip(children).zip(components.iter()) {
            if self.render_fact(expected, context)? != *component
                || self.render_fact(&child.proposition, context)? != *component
            {
                return Err(universal_error(
                    &proposition.line_file(),
                    "concrete prop reduction child does not match its retained definition component",
                ));
            }
            proofs.push(self.render_proof_term(child, context)?);
        }
        let body = right_associated(components, " ∧ ", "True");
        let proof = right_associated_conjunction_proof(proofs).ok_or_else(|| {
            universal_error(
                &proposition.line_file(),
                "bodyless concrete prop reached definition reduction",
            )
        })?;
        Ok(format!("(by\n  change {body}\n  exact {proof})"))
    }

    fn render_definition_projection(
        &mut self,
        proposition: &Fact,
        definition: &str,
        expected_source: &Fact,
        expected_target: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || premises.len() != 1
            || !facts_are_canonically_equal(proposition, expected_target)?
            || !facts_are_canonically_equal(&premises[0].proposition, expected_source)?
        {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop projection changed its source, target, or premise arity",
            ));
        }
        let components =
            self.render_prop_application_components(expected_source, definition, context)?;
        let target = self.render_fact(expected_target, context)?;
        let Some(index) = components.iter().position(|component| component == &target) else {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop projection target is not one of its definition components",
            ));
        };
        let source = self.render_proof_term(&premises[0], context)?;
        let body = right_associated(components.clone(), " ∧ ", "True");
        let projection = conjunction_projection("__definition", index, components.len());
        Ok(format!(
            "(by\n  have __definition := ({source})\n  change {body} at __definition\n  exact {projection})"
        ))
    }

    fn render_prop_application_components(
        &self,
        proposition: &Fact,
        definition: &str,
        context: &RenderContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let Fact::AtomicFact(AtomicFact::NormalAtomicFact(application)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop proof targets a non-predicate proposition",
            ));
        };
        if application.predicate.to_string() != definition {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop proof names a different definition from its target",
            ));
        }
        let definition_ir = self.prop_definitions.get(definition).ok_or_else(|| {
            universal_error(
                &proposition.line_file(),
                format!("concrete prop definition `{definition}` was not emitted first"),
            )
        })?;
        let parameter_count = definition_ir
            .params
            .iter()
            .map(|group| group.names.len())
            .sum::<usize>();
        if parameter_count != application.body.len() {
            return Err(universal_error(
                &proposition.line_file(),
                "concrete prop application arity differs from its emitted definition",
            ));
        }
        let mut nested = context.clone();
        let mut components = Vec::new();
        let mut argument_index = 0;
        for group in definition_ir.params.iter() {
            if group.names.len() != group.symbol_ids.len() {
                return Err(universal_error(
                    &proposition.line_file(),
                    "concrete prop parameter names and SymbolIds have different lengths",
                ));
            }
            for symbol_id in group.symbol_ids.iter() {
                let argument = self.render_obj(&application.body[argument_index], context)?;
                nested.symbol_names.insert(*symbol_id, argument.clone());
                components.push(self.render_ir_parameter_requirement(
                    &argument,
                    &group.param_type,
                    &nested,
                )?);
                argument_index += 1;
            }
        }
        for clause in definition_ir.iff_facts.iter() {
            components.push(self.render_fact(clause, &nested)?);
        }
        Ok(components)
    }

    fn render_known_forall_instantiation(
        &mut self,
        proposition: &Fact,
        source_fact_id: FactId,
        arguments: &[LitexToLeanKnownForallArgumentIr],
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if arguments.len() != parameter_requirements.len() {
            return Err(universal_error(
                &proposition.line_file(),
                format!(
                    "known forall FactId {source_fact_id} has {} arguments but {} parameter requirements",
                    arguments.len(),
                    parameter_requirements.len()
                ),
            ));
        }
        let (theorem_name, source_proposition) = if let Some(binding) =
            self.global_facts.get(&source_fact_id)
        {
            (binding.theorem_name.clone(), &binding.proposition)
        } else if let Some(source) = context.local_forall_facts.get(&source_fact_id) {
            let theorem_name = context
                .local_fact_names
                .get(&source_fact_id)
                .ok_or_else(|| {
                    universal_error(
                        &proposition.line_file(),
                        format!("local known forall FactId {source_fact_id} has no Lean binder"),
                    )
                })?;
            (theorem_name.clone(), source)
        } else {
            return Err(universal_error(
                &proposition.line_file(),
                format!("known forall cites unavailable FactId {source_fact_id}"),
            ));
        };
        let Fact::ForallFact(source_forall) = source_proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                format!("known forall FactId {source_fact_id} is not a forall fact"),
            ));
        };
        if source_forall.params_def_with_type.number_of_params() != arguments.len()
            || source_forall.dom_facts.len() != premises.len()
            || source_forall.then_facts.len() != 1
        {
            return Err(universal_error(
                &proposition.line_file(),
                format!(
                    "known forall FactId {source_fact_id} does not match its retained argument, domain, or conclusion arity"
                ),
            ));
        }

        let mut terms = vec![theorem_name];
        for (argument, requirement) in arguments.iter().zip(parameter_requirements.iter()) {
            let argument_ir = LitexToLeanObjectIr::lower(&argument.argument)
                .map_err(|message| universal_error(&proposition.line_file(), message))?;
            terms.push(self.render_obj_ir(&argument_ir, context)?);
            terms.push(format!(
                "({})",
                self.render_proof_term(requirement, context)?
            ));
        }
        for premise in premises {
            terms.push(format!("({})", self.render_proof_term(premise, context)?));
        }
        Ok(format!("({})", terms.join(" ")))
    }

    fn render_not_equal_symmetry(
        &mut self,
        proposition: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 1 {
            return Err(universal_error(
                &proposition.line_file(),
                "not-equality symmetry requires exactly one factual premise and no parameter requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "not-equality symmetry targets a non-inequality proposition",
            ));
        };
        let Fact::AtomicFact(AtomicFact::NotEqualFact(source)) = &premises[0].proposition else {
            return Err(universal_error(
                &premises[0].proposition.line_file(),
                "not-equality symmetry retained a non-inequality premise",
            ));
        };
        if obj_equality_key(&source.left) != obj_equality_key(&target.right)
            || obj_equality_key(&source.right) != obj_equality_key(&target.left)
        {
            return Err(universal_error(
                &proposition.line_file(),
                "not-equality symmetry premise does not reverse the target objects",
            ));
        }
        let source_proof = self.render_proof_term(&premises[0], context)?;
        Ok(format!(
            "({} ({source_proof}))",
            rule_theorem_name("notEqualSymmetry")
        ))
    }

    fn render_positive_real_membership(
        &mut self,
        proposition: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 1 {
            return Err(universal_error(
                &proposition.line_file(),
                "positive-real membership requires one exact source proof",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(source)) = &premises[0].proposition else {
            return Err(universal_error(
                &premises[0].proposition.line_file(),
                "positive-real membership retained a non-membership premise",
            ));
        };
        if !matches!(&source.set, Obj::StandardSet(StandardSet::RPos)) {
            return Err(universal_error(
                &premises[0].proposition.line_file(),
                "positive-real membership retained a source carrier other than R+",
            ));
        }
        let target_object = match proposition {
            Fact::AtomicFact(AtomicFact::LessFact(target)) if target.left.to_string() == "0" => {
                &target.right
            }
            Fact::AtomicFact(AtomicFact::GreaterFact(target))
                if target.right.to_string() == "0" =>
            {
                &target.left
            }
            _ => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "positive-real membership targets a fact other than strict positivity",
                ));
            }
        };
        if obj_equality_key(&source.element) != obj_equality_key(target_object) {
            return Err(universal_error(
                &proposition.line_file(),
                "positive-real membership changed the inferred object",
            ));
        }
        let source_proof = self.render_proof_term(&premises[0], context)?;
        Ok(format!(
            "({} {source_proof})",
            rule_theorem_name("positiveRealMembership")
        ))
    }

    fn render_native_constant_membership(
        &self,
        proposition: &Fact,
        rule: LitexToLeanNativeConstantMembershipBuiltinRuleIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || !premises.is_empty() {
            return Err(universal_error(
                &proposition.line_file(),
                "native constant membership unexpectedly retained premises",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "native constant membership targets a non-membership fact",
            ));
        };
        let theorem = match rule {
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::ImaginaryUnitInComplex
                if matches!(&membership.element, Obj::ImaginaryUnit(_))
                    && matches!(&membership.set, Obj::StandardSet(StandardSet::C)) =>
            {
                "imaginaryUnitInC"
            }
            LitexToLeanNativeConstantMembershipBuiltinRuleIr::EulerNumberInReal
                if matches!(&membership.element, Obj::EulerNumber(_))
                    && matches!(&membership.set, Obj::StandardSet(StandardSet::R)) =>
            {
                "eInR"
            }
            _ => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "native constant membership evidence changed its constant or carrier",
                ));
            }
        };
        Ok(rule_theorem_name(theorem))
    }

    fn render_standard_set_membership_projection(
        &mut self,
        proposition: &Fact,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 1 {
            return Err(universal_error(
                &proposition.line_file(),
                "standard-set membership projection requires one exact source proof",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "standard-set membership projection targets a non-membership fact",
            ));
        };
        let Fact::AtomicFact(AtomicFact::InFact(source)) = &premises[0].proposition else {
            return Err(universal_error(
                &premises[0].proposition.line_file(),
                "standard-set membership projection retained a non-membership premise",
            ));
        };
        if obj_equality_key(&source.element) != obj_equality_key(&target.element) {
            return Err(universal_error(
                &proposition.line_file(),
                "standard-set membership projection changed its member object",
            ));
        }
        let (Obj::StandardSet(source_set), Obj::StandardSet(target_set)) =
            (&source.set, &target.set)
        else {
            return Err(universal_error(
                &proposition.line_file(),
                "standard-set membership projection retained a nonstandard carrier",
            ));
        };
        let path = native_standard_set_projection_path(source_set, target_set).ok_or_else(|| {
            universal_error(
                &proposition.line_file(),
                format!(
                    "shared Lean semantics do not yet implement standard-set projection `{source_set}` to `{target_set}`"
                ),
            )
        })?;
        let mut proof = self.render_proof_term(&premises[0], context)?;
        for theorem in path {
            proof = format!("({theorem} ({proof}))");
        }
        Ok(proof)
    }

    fn render_real_arithmetic_membership(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() {
            return Err(universal_error(
                &proposition.line_file(),
                "real arithmetic closure unexpectedly retained parameter requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "real arithmetic closure targets a non-membership fact",
            ));
        };
        if !matches!(&target.set, Obj::StandardSet(StandardSet::R)) {
            return Err(universal_error(
                &proposition.line_file(),
                "real arithmetic closure targets a set other than R",
            ));
        }
        let (left, right, theorem_name) = match (rule, &target.element) {
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add, Obj::Add(value)) => {
                (value.left.as_ref(), value.right.as_ref(), "realAddClosure")
            }
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(value)) => {
                (value.left.as_ref(), value.right.as_ref(), "realSubClosure")
            }
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(value)) => {
                (value.left.as_ref(), value.right.as_ref(), "realMulClosure")
            }
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div, Obj::Div(value)) => {
                (value.left.as_ref(), value.right.as_ref(), "realDivClosure")
            }
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Pow, Obj::Pow(_)) => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "real-power closure needs its own exponent semantics before Lean emission",
                ))
            }
            _ => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "real arithmetic closure certificate does not match its target operator",
                ))
            }
        };
        let theorem = rule_theorem_name(theorem_name);
        if premises.len() != 2 {
            return Err(universal_error(
                &proposition.line_file(),
                format!(
                    "real arithmetic closure retained {} premises instead of two",
                    premises.len()
                ),
            ));
        }
        for (premise, expected_operand) in premises.iter().zip([left, right]) {
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premise.proposition else {
                return Err(universal_error(
                    &premise.proposition.line_file(),
                    "real arithmetic closure retained a non-membership premise",
                ));
            };
            if obj_equality_key(&membership.element) != obj_equality_key(expected_operand)
                || !matches!(&membership.set, Obj::StandardSet(StandardSet::R))
            {
                return Err(universal_error(
                    &premise.proposition.line_file(),
                    "real arithmetic closure changed an ordered operand premise",
                ));
            }
        }
        let left_proof = self.render_proof_term(&premises[0], context)?;
        let right_proof = self.render_proof_term(&premises[1], context)?;
        if matches!(
            rule,
            LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add
                | LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub
                | LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul
                | LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div
        ) {
            let target_ir = LitexToLeanObjectIr::lower(&target.element)
                .map_err(|message| universal_error(&proposition.line_file(), message))?;
            let LitexToLeanObjectIr::BuiltinApp {
                source_occurrence_id,
                semantic_key,
                operator,
                arguments,
            } = target_ir
            else {
                return Err(universal_error(
                    &proposition.line_file(),
                    "real arithmetic closure retained a non-builtin target object",
                ));
            };
            let complex_proofs = self.resolve_builtin_argument_membership_proofs(
                source_occurrence_id,
                &semantic_key,
                operator,
                &arguments,
                context,
            )?;
            if rule == LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div {
                let nonzero_proof = self.resolve_builtin_argument_nonzero_proof(
                    source_occurrence_id,
                    &semantic_key,
                    operator,
                    &arguments,
                    context,
                )?;
                Ok(format!(
                    "({theorem} ({}) ({}) ({nonzero_proof}) ({left_proof}) ({right_proof}))",
                    complex_proofs[0], complex_proofs[1]
                ))
            } else {
                Ok(format!(
                    "({theorem} ({}) ({}) ({left_proof}) ({right_proof}))",
                    complex_proofs[0], complex_proofs[1]
                ))
            }
        } else {
            Ok(format!("({theorem} ({left_proof}) ({right_proof}))"))
        }
    }

    fn render_integer_arithmetic_membership(
        &mut self,
        proposition: &Fact,
        rule: LitexToLeanIntegerMembershipClosureBuiltinRuleIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || premises.len() != 2 {
            return Err(universal_error(
                &proposition.line_file(),
                "integer arithmetic closure requires exactly two operand proofs",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "integer arithmetic closure targets a non-membership fact",
            ));
        };
        if !matches!(&target.set, Obj::StandardSet(StandardSet::Z)) {
            return Err(universal_error(
                &proposition.line_file(),
                "integer arithmetic closure targets a carrier other than Z",
            ));
        }
        let (left, right, theorem) = match (rule, &target.element) {
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Add, Obj::Add(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "integerAddClosure",
            ),
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "integerSubClosure",
            ),
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "integerMulClosure",
            ),
            (LitexToLeanIntegerMembershipClosureBuiltinRuleIr::Mod, Obj::Mod(_)) => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "integer remainder closure awaits the proof-free remainder object ABI",
                ));
            }
            _ => {
                return Err(universal_error(
                    &proposition.line_file(),
                    "integer arithmetic closure certificate changed its target operator",
                ));
            }
        };
        for (premise, expected) in premises.iter().zip([left, right]) {
            let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premise.proposition else {
                return Err(universal_error(
                    &premise.proposition.line_file(),
                    "integer arithmetic closure retained a non-membership premise",
                ));
            };
            if obj_equality_key(&membership.element) != obj_equality_key(expected)
                || !matches!(&membership.set, Obj::StandardSet(StandardSet::Z))
            {
                return Err(universal_error(
                    &premise.proposition.line_file(),
                    "integer arithmetic closure changed an ordered operand proof",
                ));
            }
        }
        let left_proof = self.render_proof_term(&premises[0], context)?;
        let right_proof = self.render_proof_term(&premises[1], context)?;
        Ok(format!(
            "({} ({left_proof}) ({right_proof}))",
            rule_theorem_name(theorem)
        ))
    }

    fn render_complex_arithmetic_membership(
        &self,
        proposition: &Fact,
        rule: LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty() || !premises.is_empty() {
            return Err(universal_error(
                &proposition.line_file(),
                "complex arithmetic closure must cite the verifier-owned WD facts, not reconstructed child subgoals",
            ));
        }
        let Fact::AtomicFact(AtomicFact::InFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "complex arithmetic closure targets a non-membership fact",
            ));
        };
        if !matches!(&target.set, Obj::StandardSet(StandardSet::C)) {
            return Err(universal_error(
                &proposition.line_file(),
                "complex arithmetic closure targets a set other than C",
            ));
        }
        let (operator, theorem_name) = match rule {
            LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Add => {
                (LitexToLeanBuiltinObjectOperatorIr::Add, "complexAddClosure")
            }
            LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Sub => {
                (LitexToLeanBuiltinObjectOperatorIr::Sub, "complexSubClosure")
            }
            LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Mul => {
                (LitexToLeanBuiltinObjectOperatorIr::Mul, "complexMulClosure")
            }
            LitexToLeanComplexArithmeticMembershipClosureBuiltinRuleIr::Div => {
                (LitexToLeanBuiltinObjectOperatorIr::Div, "complexDivClosure")
            }
        };
        let theorem = rule_theorem_name(theorem_name);
        let target_ir = LitexToLeanObjectIr::lower(&target.element)
            .map_err(|message| universal_error(&proposition.line_file(), message))?;
        let LitexToLeanObjectIr::BuiltinApp {
            source_occurrence_id,
            semantic_key,
            operator: target_operator,
            arguments,
        } = target_ir
        else {
            return Err(universal_error(
                &proposition.line_file(),
                "complex arithmetic closure retained a non-builtin target object",
            ));
        };
        if target_operator != operator {
            return Err(universal_error(
                &proposition.line_file(),
                "complex arithmetic closure certificate does not match its target operator",
            ));
        }
        let membership_proofs = self.resolve_builtin_argument_membership_proofs(
            source_occurrence_id,
            &semantic_key,
            operator,
            &arguments,
            context,
        )?;
        if operator == LitexToLeanBuiltinObjectOperatorIr::Div {
            let nonzero_proof = self.resolve_builtin_argument_nonzero_proof(
                source_occurrence_id,
                &semantic_key,
                operator,
                &arguments,
                context,
            )?;
            Ok(format!(
                "({theorem} ({}) ({}) ({nonzero_proof}))",
                membership_proofs[0], membership_proofs[1]
            ))
        } else {
            Ok(format!(
                "({theorem} ({}) ({}))",
                membership_proofs[0], membership_proofs[1]
            ))
        }
    }

    fn render_known_equality_path(
        &mut self,
        proposition: &Fact,
        path: &LitexToLeanKnownEqualityPathIr,
        parameter_requirements: &[LitexToLeanFactIr],
        premises: &[LitexToLeanFactIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !parameter_requirements.is_empty()
            || path.steps.is_empty()
            || premises.len() != path.steps.len()
        {
            return Err(universal_error(
                &proposition.line_file(),
                "known-equality path has invalid premise arity",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(target)) = proposition else {
            return Err(universal_error(
                &proposition.line_file(),
                "known-equality path targets a non-equality proposition",
            ));
        };

        let mut current_key = obj_equality_key(&target.left);
        let target_key = obj_equality_key(&target.right);
        let mut accumulated = None;
        for (step, premise) in path.steps.iter().zip(premises.iter()) {
            if premise.fact_id != Some(step.source_fact_id)
                || !matches!(
                    &premise.proof,
                    LitexToLeanFactProofIr::KnownFactCitation { source_fact_id }
                        if *source_fact_id == step.source_fact_id
                )
            {
                return Err(universal_error(
                    &proposition.line_file(),
                    "known-equality path changed an exact FactId citation",
                ));
            }
            let stored_proposition = context
                .local_fact_propositions
                .get(&step.source_fact_id)
                .or_else(|| {
                    self.global_facts
                        .get(&step.source_fact_id)
                        .map(|binding| &binding.proposition)
                })
                .ok_or_else(|| {
                    universal_error(
                        &proposition.line_file(),
                        format!(
                            "known-equality path cites unavailable FactId {}",
                            step.source_fact_id.value()
                        ),
                    )
                })?;
            if stored_proposition.to_string() != premise.proposition.to_string() {
                return Err(universal_error(
                    &proposition.line_file(),
                    format!(
                        "known-equality FactId {} does not match its retained proposition",
                        step.source_fact_id.value()
                    ),
                ));
            }

            let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &premise.proposition else {
                return Err(universal_error(
                    &proposition.line_file(),
                    "known-equality path retained a non-equality premise",
                ));
            };
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            if from_key != current_key {
                return Err(universal_error(
                    &proposition.line_file(),
                    "known-equality path contains disconnected steps",
                ));
            }
            let left_key = obj_equality_key(&equality.left);
            let right_key = obj_equality_key(&equality.right);
            let direction_matches = match step.direction {
                LitexToLeanEqualityRewriteDirectionIr::Forward => {
                    from_key == left_key && to_key == right_key
                }
                LitexToLeanEqualityRewriteDirectionIr::Backward => {
                    from_key == right_key && to_key == left_key
                }
            };
            if !direction_matches {
                return Err(universal_error(
                    &proposition.line_file(),
                    "known-equality path contains a wrongly oriented premise",
                ));
            }

            let proof = self.render_proof_term(premise, context)?;
            let oriented = match step.direction {
                LitexToLeanEqualityRewriteDirectionIr::Forward => format!("({proof})"),
                LitexToLeanEqualityRewriteDirectionIr::Backward => {
                    format!("Eq.symm ({proof})")
                }
            };
            accumulated = Some(match accumulated {
                None => oriented,
                Some(previous) => format!("Eq.trans ({previous}) ({oriented})"),
            });
            current_key = to_key;
        }
        if current_key != target_key {
            return Err(universal_error(
                &proposition.line_file(),
                "known-equality path does not end at the target right-hand side",
            ));
        }
        Ok(format!(
            "({})",
            accumulated.expect("nonempty known-equality path was checked above")
        ))
    }

    fn resolve_fact_id(
        &self,
        fact_id: FactId,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if let Some(name) = context.local_fact_names.get(&fact_id) {
            return Ok(name.clone());
        }
        let retained_parameter_detail = context
            .well_definedness
            .parameter_facts
            .iter()
            .find(|evidence| evidence.fact_id == fact_id)
            .map(|evidence| {
                format!(
                    " (retained parameter fact for SymbolId {}: `{}`)",
                    evidence.symbol_id.value(),
                    evidence.proposition
                )
            })
            .unwrap_or_default();
        let binding = self.global_facts.get(&fact_id).ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!(
                    "no emitted Lean proof is registered for source FactId {fact_id}{retained_parameter_detail}"
                ),
            )
        })?;
        let mut arguments = Vec::new();
        for (symbol_id, parameter_fact_id) in binding
            .parameter_symbol_ids
            .iter()
            .zip(binding.parameter_fact_ids.iter())
        {
            let symbol = context.symbol_names.get(symbol_id).ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!("FactId {fact_id} requires a symbol outside the current Lean scope"),
                )
            })?;
            let parameter_proof = context
                .local_fact_names
                .get(parameter_fact_id)
                .ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!(
                            "FactId {fact_id} requires parameter fact {parameter_fact_id} outside the current Lean scope"
                        ),
                    )
                })?;
            arguments.push(symbol.clone());
            arguments.push(parameter_proof.clone());
        }
        for domain_fact_id in binding.domain_fact_ids.iter() {
            let proof = context.local_fact_names.get(domain_fact_id).ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "FactId {fact_id} requires domain fact {domain_fact_id} outside the current Lean scope"
                    ),
                )
            })?;
            arguments.push(proof.clone());
        }
        if arguments.is_empty() {
            Ok(binding.theorem_name.clone())
        } else {
            Ok(format!("{} {}", binding.theorem_name, arguments.join(" ")))
        }
    }

    fn render_fact(&self, fact: &Fact, context: &RenderContext) -> Result<String, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => self.render_atomic_fact(fact, context),
            Fact::ExistFact(existential) => self.render_existential_fact(existential, context),
            Fact::OrFact(disjunction) => {
                let mut parts = Vec::with_capacity(disjunction.facts.len());
                for branch in disjunction.facts.iter() {
                    let rendered = match branch {
                        AndChainAtomicFact::AtomicFact(branch) => {
                            self.render_atomic_fact(branch, context)?
                        }
                        AndChainAtomicFact::AndFact(branch) => {
                            self.render_fact(&Fact::AndFact(branch.clone()), context)?
                        }
                        AndChainAtomicFact::ChainFact(branch) => {
                            self.render_fact(&Fact::ChainFact(branch.clone()), context)?
                        }
                    };
                    parts.push(rendered);
                }
                Ok(right_associated(parts, " ∨ ", "False"))
            }
            Fact::AndFact(conjunction) => {
                let mut parts = Vec::with_capacity(conjunction.facts.len());
                for component in conjunction.facts.iter() {
                    parts.push(self.render_atomic_fact(component, context)?);
                }
                Ok(right_associated(parts, " ∧ ", "True"))
            }
            Fact::ChainFact(chain) => {
                let mut parts = Vec::new();
                for component in chain.facts()? {
                    parts.push(self.render_atomic_fact(&component, context)?);
                }
                Ok(right_associated(parts, " ∧ ", "True"))
            }
            Fact::ForallFact(forall) => self.render_nested_forall_fact(forall, context),
            _ => Err(universal_error(
                &fact.line_file(),
                format!(
                    "the universal-object MVP does not yet render fact kind `{}`",
                    fact.fact_type_string()
                ),
            )),
        }
    }

    fn render_existential_fact(
        &self,
        existential: &ExistFactEnum,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !existential.is_plain_exist()
            || existential.params_def_with_type().number_of_params() != 1
            || existential.facts().len() != 1
        {
            return Err(universal_error(
                &existential.line_file(),
                "the current universal-object existential emitter supports one positive witness and one body fact",
            ));
        }
        let group = &existential.params_def_with_type().groups[0];
        if group.params.len() != 1 {
            return Err(universal_error(
                &existential.line_file(),
                "the current universal-object existential emitter requires one singleton parameter group",
            ));
        }
        let binding = &group.params[0];
        let name = lean_name(binding.name());
        let mut nested = context.clone();
        nested.symbol_names.insert(binding.id(), name.clone());
        let requirement = self.render_parameter_requirement(&name, &group.param_type, &nested)?;
        let body = self.render_fact(&existential.facts()[0].from_ref_to_cloned_fact(), &nested)?;
        Ok(format!("∃ ({name} : Litex.Object), {requirement} ∧ {body}"))
    }

    fn one_witness_existentials_are_alpha_equal(
        &self,
        source: &Fact,
        target: &Fact,
        context: &RenderContext,
    ) -> Result<bool, RuntimeError> {
        let (Fact::ExistFact(source), Fact::ExistFact(target)) = (source, target) else {
            return Ok(false);
        };
        if !source.is_plain_exist()
            || !target.is_plain_exist()
            || source.params_def_with_type().number_of_params() != 1
            || target.params_def_with_type().number_of_params() != 1
            || source.facts().len() != 1
            || target.facts().len() != 1
        {
            return Ok(false);
        }
        let source_group = &source.params_def_with_type().groups[0];
        let target_group = &target.params_def_with_type().groups[0];
        if source_group.params.len() != 1 || target_group.params.len() != 1 {
            return Ok(false);
        }
        let common = "__bound";
        let mut source_context = context.clone();
        source_context
            .symbol_names
            .insert(source_group.params[0].id(), common.to_string());
        let mut target_context = context.clone();
        target_context
            .symbol_names
            .insert(target_group.params[0].id(), common.to_string());
        let source_requirement =
            self.render_parameter_requirement(common, &source_group.param_type, &source_context)?;
        let target_requirement =
            self.render_parameter_requirement(common, &target_group.param_type, &target_context)?;
        let source_body = self.render_fact(
            &source.facts()[0].from_ref_to_cloned_fact(),
            &source_context,
        )?;
        let target_body = self.render_fact(
            &target.facts()[0].from_ref_to_cloned_fact(),
            &target_context,
        )?;
        Ok(source_requirement == target_requirement && source_body == target_body)
    }

    fn render_nested_forall_fact(
        &self,
        forall: &ForallFact,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if !forall.dom_facts.is_empty() {
            return Err(universal_error(
                &forall.line_file,
                "nested forall domain premises need explicit retained binder FactIds before To-Lean emission",
            ));
        }
        let (nested, names, types) =
            self.extend_forall_parameter_scope(forall, context, &[], &[])?;
        let mut binders = Vec::with_capacity(names.len());
        for (name, binder_type) in names.iter().zip(types.iter()) {
            binders.push(format!("({name} : {binder_type})"));
        }
        let mut conclusions = Vec::with_capacity(forall.then_facts.len());
        for conclusion in forall.then_facts.iter() {
            conclusions.push(self.render_fact(&conclusion.clone().to_fact(), &nested)?);
        }
        let conclusion = right_associated(conclusions, " ∧ ", "True");
        if binders.is_empty() {
            Ok(conclusion)
        } else {
            Ok(format!("∀ {}, {conclusion}", binders.join(" ")))
        }
    }

    fn render_atomic_fact(
        &self,
        fact: &AtomicFact,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(fact) => {
                let mut left = self.render_obj(&fact.left, context)?;
                let right = self.render_obj(&fact.right, context)?;
                if lean_text_is_natural_literal(&left) && lean_text_is_natural_literal(&right) {
                    left = format!("({left} : Litex.Object)");
                }
                Ok(format!("{left} = {right}"))
            }
            AtomicFact::NotEqualFact(fact) => {
                let mut left = self.render_obj(&fact.left, context)?;
                let right = self.render_obj(&fact.right, context)?;
                if lean_text_is_natural_literal(&left) && lean_text_is_natural_literal(&right) {
                    left = format!("({left} : Litex.Object)");
                }
                Ok(format!("{left} ≠ {right}"))
            }
            AtomicFact::LessFact(fact) => Ok(format!(
                "Litex.Lt {} {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::GreaterFact(fact) => Ok(format!(
                "Litex.Lt {} {}",
                self.render_obj(&fact.right, context)?,
                self.render_obj(&fact.left, context)?
            )),
            AtomicFact::LessEqualFact(fact) => Ok(format!(
                "Litex.Le {} {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::GreaterEqualFact(fact) => Ok(format!(
                "Litex.Le {} {}",
                self.render_obj(&fact.right, context)?,
                self.render_obj(&fact.left, context)?
            )),
            AtomicFact::NotLessFact(fact) => Ok(format!(
                "¬ Litex.Lt {} {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::NotGreaterFact(fact) => Ok(format!(
                "¬ Litex.Lt {} {}",
                self.render_obj(&fact.right, context)?,
                self.render_obj(&fact.left, context)?
            )),
            AtomicFact::NotLessEqualFact(fact) => Ok(format!(
                "¬ Litex.Le {} {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(format!(
                "¬ Litex.Le {} {}",
                self.render_obj(&fact.right, context)?,
                self.render_obj(&fact.left, context)?
            )),
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                self.render_obj(&fact.element, context)?,
                self.render_obj(&fact.set, context)?
            )),
            AtomicFact::NotInFact(fact) => Ok(format!(
                "¬ Litex.In {} {}",
                self.render_obj(&fact.element, context)?,
                self.render_obj(&fact.set, context)?
            )),
            AtomicFact::SubsetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::SupersetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                self.render_obj(&fact.right, context)?,
                self.render_obj(&fact.left, context)?
            )),
            AtomicFact::NotSubsetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::NotSupersetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                self.render_obj(&fact.right, context)?,
                self.render_obj(&fact.left, context)?
            )),
            AtomicFact::IsSetFact(fact) => Ok(format!(
                "Litex.IsSet {}",
                self.render_obj(&fact.set, context)?
            )),
            AtomicFact::IsNonemptySetFact(fact) => Ok(format!(
                "Litex.IsNonemptySet {}",
                self.render_obj(&fact.set, context)?
            )),
            AtomicFact::IsFiniteSetFact(fact) => Ok(format!(
                "Litex.IsFiniteSet {}",
                self.render_obj(&fact.set, context)?
            )),
            AtomicFact::IsTupleFact(fact) => Ok(format!(
                "Litex.IsTuple {}",
                self.render_obj(&fact.set, context)?
            )),
            AtomicFact::NormalAtomicFact(fact) => {
                let mut text = render_normal_predicate_name(&fact.predicate);
                for argument in fact.body.iter() {
                    text.push(' ');
                    text.push_str(&self.render_obj(argument, context)?);
                }
                Ok(text)
            }
            other => Err(universal_error(
                &other.line_file(),
                format!("the universal-object MVP does not yet render atomic fact `{other}`"),
            )),
        }
    }

    fn render_obj(&self, object: &Obj, context: &RenderContext) -> Result<String, RuntimeError> {
        if let Some(source_occurrence_id) = object.source_occurrence_id() {
            if let Some(name) = context
                .well_defined_object_ids
                .get(&source_occurrence_id)
                .and_then(|obj_id| context.well_defined_object_names.get(obj_id))
            {
                return Ok(name.clone());
            }
        }
        let ir = LitexToLeanObjectIr::lower(object)
            .map_err(|message| universal_error(&default_line_file(), message))?;
        self.render_obj_ir(&ir, context)
    }

    fn render_obj_ir(
        &self,
        object: &LitexToLeanObjectIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match object {
            LitexToLeanObjectIr::Symbol {
                symbol_id,
                name,
            } => Ok(context
                .symbol_names
                .get(symbol_id)
                .cloned()
                .unwrap_or_else(|| lean_name(name))),
            LitexToLeanObjectIr::Number { normalized_value }
                if normalized_value.chars().all(|character| character.is_ascii_digit()) =>
            {
                Ok(normalized_value.clone())
            }
            LitexToLeanObjectIr::Number { normalized_value }
                if normalized_value
                    .strip_prefix('-')
                    .is_some_and(|magnitude| {
                        !magnitude.is_empty()
                            && magnitude
                                .chars()
                                .all(|character| character.is_ascii_digit())
                    }) =>
            {
                Ok(format!(
                    "(Litex.sub 0 {})",
                    normalized_value
                        .strip_prefix('-')
                        .expect("a guarded negative numeral has a magnitude")
                ))
            }
            LitexToLeanObjectIr::Number { normalized_value } => Err(universal_error(
                &default_line_file(),
                format!(
                    "the universal-object MVP currently supports natural numerals, not `{normalized_value}`"
                ),
            )),
            LitexToLeanObjectIr::Constant(constant) => Ok(match constant {
                LitexToLeanConstantObjectIr::ImaginaryUnit => "Litex.i".to_string(),
                LitexToLeanConstantObjectIr::EulerNumber => "Litex.e".to_string(),
                LitexToLeanConstantObjectIr::Pi => "Litex.pi".to_string(),
            }),
            LitexToLeanObjectIr::StandardSet(set) => Ok(standard_set_name(*set).to_string()),
            LitexToLeanObjectIr::FunctionSet { function } => {
                self.render_function_set(function, context)
            }
            LitexToLeanObjectIr::SetBuilder(set_builder) => {
                self.render_set_builder(set_builder, context)
            }
            LitexToLeanObjectIr::AnonymousFunction(function) => {
                self.render_inline_anonymous_function(function, context)
            }
            LitexToLeanObjectIr::FunctionApplication(application) => {
                self.render_function_application(application, context)
            }
            LitexToLeanObjectIr::ClosedRange { start, end } => Ok(format!(
                "(Litex.closedRange {} {})",
                self.render_obj_ir(start.as_ref(), context)?,
                self.render_obj_ir(end.as_ref(), context)?
            )),
            LitexToLeanObjectIr::Range { start, end } => Ok(format!(
                "(Litex.range {} {})",
                self.render_obj_ir(start.as_ref(), context)?,
                self.render_obj_ir(end.as_ref(), context)?
            )),
            LitexToLeanObjectIr::GeneralCartesianProduct {
                index_set,
                family_set,
                family_function,
            } => Ok(format!(
                "(Litex.generalCart {} {} {})",
                self.render_obj_ir(index_set.as_ref(), context)?,
                self.render_obj_ir(family_set.as_ref(), context)?,
                self.render_obj_ir(family_function.as_ref(), context)?
            )),
            LitexToLeanObjectIr::SequenceSet { values, length } => match length {
                Some(length) => Ok(format!(
                    "(Litex.finiteSequenceSet {} {})",
                    self.render_obj_ir(values.as_ref(), context)?,
                    self.render_obj_ir(length.as_ref(), context)?
                )),
                None => Ok(format!(
                    "(Litex.sequenceSet {})",
                    self.render_obj_ir(values.as_ref(), context)?
                )),
            },
            LitexToLeanObjectIr::Aggregate {
                kind, arguments, ..
            } => self.render_aggregate(*kind, arguments, context),
            LitexToLeanObjectIr::TupleDimension(object) => Ok(format!(
                "(Litex.tupleDim {})",
                self.render_obj_ir(object.as_ref(), context)?
            )),
            LitexToLeanObjectIr::IndexedAccess { object, index } => Ok(format!(
                "(Litex.atIndex {} {})",
                self.render_obj_ir(object.as_ref(), context)?,
                self.render_obj_ir(index.as_ref(), context)?
            )),
            LitexToLeanObjectIr::BuiltinApp {
                source_occurrence_id,
                semantic_key,
                operator,
                arguments,
            } => self.render_builtin_application(
                *source_occurrence_id,
                semantic_key,
                *operator,
                arguments,
                context,
            ),
            LitexToLeanObjectIr::Collection {
                source_occurrence_id,
                semantic_key,
                constructor: LitexToLeanCollectionObjectIr::ListSet,
                items,
            } => self.render_list_set(*source_occurrence_id, semantic_key, items, context),
            LitexToLeanObjectIr::Collection {
                constructor: LitexToLeanCollectionObjectIr::Tuple,
                items,
                ..
            } => Ok(format!(
                "(Litex.tupleLiteral [{}])",
                items
                    .iter()
                    .map(|item| self.render_obj_ir(item, context))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            )),
            LitexToLeanObjectIr::Collection {
                constructor: LitexToLeanCollectionObjectIr::SequenceLiteral,
                items,
                ..
            } => Ok(format!(
                "(Litex.sequenceLiteral [{}])",
                items
                    .iter()
                    .map(|item| self.render_obj_ir(item, context))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ")
            )),
        }
    }

    fn render_set_builder(
        &self,
        set_builder: &LitexToLeanSetBuilderIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let base = self.render_obj_ir(set_builder.set.as_ref(), context)?;
        let binder = format!("__x{}", set_builder.symbol_id.value());
        let mut nested = context.clone();
        nested
            .symbol_names
            .insert(set_builder.symbol_id, binder.clone());
        let predicate = if set_builder.facts.is_empty() {
            "True".to_string()
        } else {
            let facts = set_builder
                .facts
                .iter()
                .map(|fact| self.render_fact(fact, &nested))
                .collect::<Result<Vec<_>, RuntimeError>>()?;
            right_associated(facts, " ∧ ", "True")
        };
        Ok(format!(
            "(Litex.setBuilder {base} (fun {binder} => {predicate}))"
        ))
    }

    fn render_inline_anonymous_function(
        &self,
        function: &LitexToLeanAnonymousFunctionIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let spec = self.render_function_spec(&function.function, context)?;
        let arguments = "__anonymous_args";
        let length = "__anonymous_length";
        let requirements = "__anonymous_requirements";
        let mut body_context = context.clone();
        for (parameter_index, parameter) in function.function.parameters.iter().enumerate() {
            body_context.symbol_names.insert(
                parameter.symbol_id,
                format!("(Litex.arg {arguments} {parameter_index})"),
            );
        }
        let body = self.render_obj_ir(function.body.as_ref(), &body_context)?;
        Ok(format!(
            "(Litex.functionObject ({spec}) (fun {arguments} {length} {requirements} => {body}))"
        ))
    }

    fn render_list_set(
        &self,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        semantic_key: &str,
        items: &[LitexToLeanObjectIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let source_occurrence_id = source_occurrence_id.ok_or_else(|| {
            universal_error(
                &default_line_file(),
                "proof-carrying list-set constructor has no parser-owned source occurrence ID",
            )
        })?;
        let proof_id = context
            .well_defined_object_ids
            .get(&source_occurrence_id)
            .copied()
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "proof-carrying list-set source occurrence {} has no exact WellDefinedObjId",
                        source_occurrence_id.value()
                    ),
                )
            })?;
        let object = context
            .well_definedness
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == proof_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} is unavailable while rendering a list set",
                        proof_id.value()
                    ),
                )
            })?;
        if obj_equality_key(&object.source_object) != semantic_key {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "WellDefinedObjId {} changed its source list set before Lean emission",
                    proof_id.value()
                ),
            ));
        }
        let Obj::ListSet(source) = &object.source_object else {
            return Err(universal_error(
                &default_line_file(),
                "a proof-carrying list-set certificate retained a non-list-set object",
            ));
        };
        if source.list.len() != items.len() {
            return Err(universal_error(
                &default_line_file(),
                "proof-carrying list-set IR changed its verifier-owned arity",
            ));
        }

        let mut rendered_items = vec![None; items.len()];
        for child in object.child_uses.iter() {
            let argument_index = match child.role {
                WellDefinedObjChildRole::ConstructorArgument { argument_index } => argument_index,
                WellDefinedObjChildRole::VerificationDependency { .. } => continue,
                _ => {
                    return Err(universal_error(
                        &default_line_file(),
                        "proof-carrying list set retained an incompatible construction-child role",
                    ));
                }
            };
            if argument_index >= items.len() || rendered_items[argument_index].is_some() {
                return Err(universal_error(
                    &default_line_file(),
                    "proof-carrying list set retained a duplicate or out-of-range object child",
                ));
            }
            let child_object = context
                .well_definedness
                .objects
                .iter()
                .find(|candidate| candidate.well_defined_obj_id == child.obj_id)
                .ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        "list-set object child is absent from the frozen certificate",
                    )
                })?;
            if obj_equality_key(&child_object.source_object)
                != obj_equality_key(source.list[argument_index].as_ref())
            {
                return Err(universal_error(
                    &default_line_file(),
                    "list-set object child changed its ordered source entry",
                ));
            }
            let expected = LitexToLeanObjectIr::lower(source.list[argument_index].as_ref())
                .map_err(|message| universal_error(&default_line_file(), message))?;
            if expected != items[argument_index] {
                return Err(universal_error(
                    &default_line_file(),
                    "list-set object IR changed an ordered source entry",
                ));
            }
            rendered_items[argument_index] = Some(
                if let Some(name) = context.well_defined_object_names.get(&child.obj_id) {
                    name.clone()
                } else {
                    self.render_obj_ir(&items[argument_index], context)?
                },
            );
        }
        let rendered_items = rendered_items
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "proof-carrying list set requires one ordered object child per source entry",
                )
            })?;

        let mut pairwise_requirements = HashSet::new();
        for requirement in object.target_requirements.iter() {
            let WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                left_index,
                right_index,
            } = requirement.role
            else {
                return Err(universal_error(
                    &requirement.expected_proposition.line_file(),
                    "proof-carrying list set retained an unexpected target requirement role",
                ));
            };
            if left_index >= right_index
                || right_index >= items.len()
                || !pairwise_requirements.insert((left_index, right_index))
            {
                return Err(universal_error(
                    &requirement.expected_proposition.line_file(),
                    "proof-carrying list set retained a duplicate, reversed, or out-of-range pairwise role",
                ));
            }
            validate_list_set_pairwise_distinct(
                &requirement.expected_proposition,
                source.list[left_index].as_ref(),
                source.list[right_index].as_ref(),
            )?;
        }
        let expected_pairs = items.len().saturating_mul(items.len().saturating_sub(1)) / 2;
        if pairwise_requirements.len() != expected_pairs {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "proof-carrying list set requires {expected_pairs} ordered pairwise-distinctness proofs, but retained {}",
                    pairwise_requirements.len()
                ),
            ));
        }
        Ok(format!("(Litex.listSet [{}])", rendered_items.join(", ")))
    }

    fn render_aggregate(
        &self,
        kind: LitexToLeanAggregateObjectIr,
        arguments: &[LitexToLeanObjectIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let (name, arity) = match kind {
            LitexToLeanAggregateObjectIr::Sum => ("Litex.sum", 3),
            LitexToLeanAggregateObjectIr::Product => ("Litex.product", 3),
            LitexToLeanAggregateObjectIr::FiniteSetSum => ("Litex.finiteSetSum", 2),
            LitexToLeanAggregateObjectIr::FiniteSetProduct => ("Litex.finiteSetProduct", 2),
            LitexToLeanAggregateObjectIr::Reduce => ("Litex.reduce", 5),
            LitexToLeanAggregateObjectIr::FiniteSetReduce => ("Litex.finiteSetReduce", 4),
        };
        if arguments.len() != arity {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "aggregate `{kind:?}` retained {} arguments instead of {arity}",
                    arguments.len()
                ),
            ));
        }
        let rendered = arguments
            .iter()
            .map(|argument| self.render_obj_ir(argument, context))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("({name} {})", rendered.join(" ")))
    }

    fn render_builtin_application(
        &self,
        _source_occurrence_id: Option<SourceObjectOccurrenceId>,
        _semantic_key: &str,
        operator: LitexToLeanBuiltinObjectOperatorIr,
        arguments: &[LitexToLeanObjectIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let set_constructor = match operator {
            LitexToLeanBuiltinObjectOperatorIr::Union => Some(("Litex.union", 2)),
            LitexToLeanBuiltinObjectOperatorIr::Intersect => Some(("Litex.intersect", 2)),
            LitexToLeanBuiltinObjectOperatorIr::SetMinus => Some(("Litex.setMinus", 2)),
            LitexToLeanBuiltinObjectOperatorIr::BigUnion => Some(("Litex.bigUnion", 1)),
            LitexToLeanBuiltinObjectOperatorIr::BigIntersect => Some(("Litex.bigIntersect", 1)),
            LitexToLeanBuiltinObjectOperatorIr::PowerSet => Some(("Litex.powerSet", 1)),
            _ => None,
        };
        if let Some((name, arity)) = set_constructor {
            if arguments.len() != arity {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "total object constructor `{operator:?}` retained {} arguments instead of {arity}",
                        arguments.len(),
                    ),
                ));
            }
            let rendered = arguments
                .iter()
                .map(|argument| self.render_obj_ir(argument, context))
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(format!("({name} {})", rendered.join(" ")));
        }
        let name = match operator {
            LitexToLeanBuiltinObjectOperatorIr::Add => "Litex.add",
            LitexToLeanBuiltinObjectOperatorIr::Sub => "Litex.sub",
            LitexToLeanBuiltinObjectOperatorIr::Mul => "Litex.mul",
            LitexToLeanBuiltinObjectOperatorIr::Div => "Litex.div",
            _ => {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "the universal-object arithmetic slice does not yet render operator `{operator:?}`"
                    ),
                ))
            }
        };
        if arguments.len() != 2 {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "universal arithmetic operator `{operator:?}` retained {} arguments instead of two",
                    arguments.len()
                ),
            ));
        }
        Ok(format!(
            "({name} {} {})",
            self.render_obj_ir(&arguments[0], context)?,
            self.render_obj_ir(&arguments[1], context)?
        ))
    }

    fn resolve_builtin_argument_membership_proofs(
        &self,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        semantic_key: &str,
        operator: LitexToLeanBuiltinObjectOperatorIr,
        arguments: &[LitexToLeanObjectIr],
        context: &RenderContext,
    ) -> Result<[String; 2], RuntimeError> {
        if source_occurrence_id.is_none()
            && matches!(
                operator,
                LitexToLeanBuiltinObjectOperatorIr::Add
                    | LitexToLeanBuiltinObjectOperatorIr::Sub
                    | LitexToLeanBuiltinObjectOperatorIr::Mul
            )
        {
            let mut proofs = Vec::with_capacity(2);
            for argument in arguments {
                let proof = match argument {
                    LitexToLeanObjectIr::Number { normalized_value } => {
                        let (theorem, magnitude) = if let Some(magnitude) =
                            normalized_value.strip_prefix('-')
                        {
                            (rule_theorem_name("negativeNumeralInC"), magnitude)
                        } else {
                            (rule_theorem_name("numeralInC"), normalized_value.as_str())
                        };
                        format!("({theorem} {magnitude})")
                    }
                    LitexToLeanObjectIr::BuiltinApp {
                        source_occurrence_id: Some(source_occurrence_id),
                        ..
                    } => {
                        let obj_id = context
                            .well_defined_object_ids
                            .get(source_occurrence_id)
                            .copied()
                            .ok_or_else(|| {
                                universal_error(
                                    &default_line_file(),
                                    format!(
                                        "synthetic `{operator:?}` argument occurrence {} has no exact WellDefinedObjId",
                                        source_occurrence_id.value()
                                    ),
                                )
                            })?;
                        context
                            .well_defined_result_membership_names
                            .get(&obj_id)
                            .cloned()
                            .ok_or_else(|| {
                                universal_error(
                                    &default_line_file(),
                                    format!(
                                        "synthetic `{operator:?}` argument obj_{} has no local complex-membership proof",
                                        obj_id.value()
                                    ),
                                )
                            })?
                    }
                    _ => {
                        return Err(universal_error(
                            &default_line_file(),
                            format!(
                                "synthetic `{operator:?}` has unsupported complex argument `{argument:?}`"
                            ),
                        ))
                    }
                };
                proofs.push(proof);
            }
            return Ok([proofs.remove(0), proofs.remove(0)]);
        }
        let source_occurrence_id = source_occurrence_id.ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!(
                    "proof-carrying operator `{operator:?}` with semantic key `{semantic_key}` and arguments `{arguments:?}` has no source occurrence ID"
                ),
            )
        })?;
        let proof_id = context
            .well_defined_object_ids
            .get(&source_occurrence_id)
            .copied()
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "proof-carrying operator `{operator:?}` with semantic key `{semantic_key}` has no exact WellDefinedObjId"
                    ),
                )
            })?;
        let object = context
            .well_definedness
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == proof_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} is unavailable while rendering `{operator:?}`",
                        proof_id.value()
                    ),
                )
            })?;
        if obj_equality_key(&object.source_object) != semantic_key {
            return Err(universal_error(
                &default_line_file(),
                format!(
                    "WellDefinedObjId {} changed its source object before Lean emission",
                    proof_id.value()
                ),
            ));
        }
        let (source_operator, source_arguments) =
            arithmetic_source_operator_and_arguments(&object.source_object).ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "a proof-carrying arithmetic certificate retained a non-arithmetic object",
                )
            })?;
        if source_operator != operator || source_arguments.len() != arguments.len() {
            return Err(universal_error(
                &default_line_file(),
                "proof-carrying arithmetic IR changed its verifier-owned operator or arity",
            ));
        }
        for (source, lowered) in source_arguments.iter().zip(arguments.iter()) {
            let expected = LitexToLeanObjectIr::lower(source)
                .map_err(|message| universal_error(&default_line_file(), message))?;
            if &expected != lowered {
                return Err(universal_error(
                    &default_line_file(),
                    "proof-carrying arithmetic IR changed an ordered source operand",
                ));
            }
        }

        let mut resolved: [Option<String>; 2] = [None, None];
        for requirement in object.target_requirements.iter() {
            let argument_index =
                match requirement.role {
                    WellDefinednessRequirementRole::BuiltinArgumentMembership {
                        argument_index,
                    } => argument_index,
                    WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index }
                        if operator == LitexToLeanBuiltinObjectOperatorIr::Div
                            && argument_index == 1 =>
                    {
                        continue;
                    }
                    _ => return Err(universal_error(
                        &requirement.expected_proposition.line_file(),
                        "proof-carrying arithmetic retained an unexpected target requirement role",
                    )),
                };
            if argument_index >= resolved.len() || resolved[argument_index].is_some() {
                return Err(universal_error(
                    &requirement.expected_proposition.line_file(),
                    "proof-carrying arithmetic retained a duplicate or out-of-range membership role",
                ));
            }
            validate_complex_operand_membership(
                &requirement.expected_proposition,
                source_arguments[argument_index],
            )?;
            let proof_name = context
                .well_defined_fact_names
                .get(&requirement.well_defined_fact_id)
                .cloned()
                .ok_or_else(|| {
                    universal_error(
                        &requirement.expected_proposition.line_file(),
                        format!(
                            "WellDefinedFactId {} has no named exact Lean proof",
                            requirement.well_defined_fact_id.value()
                        ),
                    )
                })?;
            resolved[argument_index] = Some(proof_name);
        }
        let [Some(left), Some(right)] = resolved else {
            return Err(universal_error(
                &default_line_file(),
                "proof-carrying arithmetic requires exactly two ordered complex-membership proofs",
            ));
        };
        Ok([left, right])
    }

    fn resolve_builtin_argument_nonzero_proof(
        &self,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        semantic_key: &str,
        operator: LitexToLeanBuiltinObjectOperatorIr,
        arguments: &[LitexToLeanObjectIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if operator != LitexToLeanBuiltinObjectOperatorIr::Div || arguments.len() != 2 {
            return Err(universal_error(
                &default_line_file(),
                "a builtin nonzero proof was requested for a non-division operator",
            ));
        }
        let source_occurrence_id = source_occurrence_id.ok_or_else(|| {
            universal_error(
                &default_line_file(),
                "proof-carrying division has no source occurrence ID",
            )
        })?;
        let proof_id = context
            .well_defined_object_ids
            .get(&source_occurrence_id)
            .copied()
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "proof-carrying division has no exact WellDefinedObjId",
                )
            })?;
        let object = context
            .well_definedness
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == proof_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} is unavailable while rendering division",
                        proof_id.value()
                    ),
                )
            })?;
        if obj_equality_key(&object.source_object) != semantic_key {
            return Err(universal_error(
                &default_line_file(),
                "proof-carrying division changed its verifier-owned source object",
            ));
        }
        let (source_operator, source_arguments) =
            arithmetic_source_operator_and_arguments(&object.source_object).ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "a proof-carrying division certificate retained a non-arithmetic object",
                )
            })?;
        if source_operator != operator || source_arguments.len() != arguments.len() {
            return Err(universal_error(
                &default_line_file(),
                "proof-carrying division IR changed its verifier-owned operator or arity",
            ));
        }
        for (source, lowered) in source_arguments.iter().zip(arguments.iter()) {
            let expected = LitexToLeanObjectIr::lower(source)
                .map_err(|message| universal_error(&default_line_file(), message))?;
            if &expected != lowered {
                return Err(universal_error(
                    &default_line_file(),
                    "proof-carrying division IR changed an ordered source operand",
                ));
            }
        }

        let mut resolved = None;
        for requirement in object.target_requirements.iter() {
            let WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index } =
                requirement.role
            else {
                continue;
            };
            if argument_index != 1 || resolved.is_some() {
                return Err(universal_error(
                    &requirement.expected_proposition.line_file(),
                    "proof-carrying division retained a duplicate or misindexed nonzero role",
                ));
            }
            validate_divisor_nonzero(
                &requirement.expected_proposition,
                source_arguments[argument_index],
            )?;
            resolved = Some(
                context
                    .well_defined_fact_names
                    .get(&requirement.well_defined_fact_id)
                    .cloned()
                    .ok_or_else(|| {
                        universal_error(
                            &requirement.expected_proposition.line_file(),
                            format!(
                                "WellDefinedFactId {} has no named exact Lean proof",
                                requirement.well_defined_fact_id.value()
                            ),
                        )
                    })?,
            );
        }
        resolved.ok_or_else(|| {
            universal_error(
                &default_line_file(),
                "proof-carrying division requires exactly one denominator-nonzero proof",
            )
        })
    }

    fn render_function_set(
        &self,
        function: &LitexToLeanFunctionTypeIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if function_ir_uses_fn_space(function) {
            let mut inputs = Vec::with_capacity(function.parameters.len());
            for parameter in function.parameters.iter() {
                inputs.push(self.render_obj_ir(&parameter.set, context)?);
            }
            let output = self.render_obj_ir(function.return_set.as_ref(), context)?;
            let rendered = match inputs.as_slice() {
                [] => format!("Litex.fnSpace [] {output}"),
                [input] => format!("Litex.fnSpace1 {input} {output}"),
                [input0, input1] => {
                    format!("Litex.fnSpace2 {input0} {input1} {output}")
                }
                [input0, input1, input2] => {
                    format!("Litex.fnSpace3 {input0} {input1} {input2} {output}")
                }
                [input0, input1, input2, input3] => {
                    format!("Litex.fnSpace4 {input0} {input1} {input2} {input3} {output}")
                }
                [input0, input1, input2, input3, input4] => {
                    format!("Litex.fnSpace5 {input0} {input1} {input2} {input3} {input4} {output}")
                }
                _ => format!("Litex.fnSpace [{}] {output}", inputs.join(", ")),
            };
            return Ok(format!("({rendered})"));
        }
        Ok(format!(
            "(Litex.FnSet {})",
            self.render_function_spec(function, context)?
        ))
    }

    fn render_function_spec(
        &self,
        function: &LitexToLeanFunctionTypeIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let arguments_name = format!("__arg_{}", context.function_set_depth);
        let mut nested = context.clone();
        nested.function_set_depth += 1;
        let mut requirements = Vec::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            nested.symbol_names.insert(
                parameter.symbol_id,
                format!("(Litex.arg {arguments_name} {index})"),
            );
            requirements.push((
                format!("__h_arg{index}"),
                format!(
                    "Litex.In (Litex.arg {arguments_name} {index}) {}",
                    self.render_obj_ir(&parameter.set, &nested)?
                ),
            ));
        }
        for fact in function.domain_facts.iter() {
            requirements.push((
                format!("__h_dom{}", requirements.len() - function.parameters.len()),
                self.render_fact(fact, &nested)?,
            ));
        }
        let requirements = dependent_requirement_telescope(&requirements);
        let range = self.render_obj_ir(function.return_set.as_ref(), &nested)?;
        Ok(format!(
            "({{ arity := {}, requirements := fun {arguments_name} => {}, range := fun {arguments_name} _ _ => {} }} : Litex.FnSpec)",
            function.parameters.len(), requirements, range,
        ))
    }

    fn render_function_application(
        &self,
        application: &LitexToLeanFunctionApplicationIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if application.argument_layers.is_empty()
            || application.argument_layers.len() != application.source_argument_layers.len()
        {
            return Err(universal_error(
                &default_line_file(),
                "function application IR has empty or mismatched source layers",
            ));
        }
        let mut value = self.render_obj_ir(application.head.as_ref(), context)?;
        for arguments in application.argument_layers.iter() {
            let rendered_arguments = arguments
                .iter()
                .map(|argument| self.render_obj_ir(argument, context))
                .collect::<Result<Vec<_>, RuntimeError>>()?;
            value = format!("({value}) [{}]", rendered_arguments.join(", "));
        }
        Ok(format!("({value})"))
    }

    fn render_function_application_with_result(
        &self,
        application: &LitexToLeanFunctionApplicationIr,
        context: &RenderContext,
        initial_membership_override: Option<String>,
    ) -> Result<RenderedFunctionApplication, RuntimeError> {
        if application.argument_layers.is_empty()
            || application.argument_layers.len() != application.source_argument_layers.len()
        {
            return Err(universal_error(
                &default_line_file(),
                "function application IR has empty or mismatched source layers",
            ));
        }
        let LitexToLeanObjectIr::Symbol { .. } = application.head.as_ref() else {
            return Err(universal_error(
                &default_line_file(),
                "the universal-object MVP requires a named function head",
            ));
        };
        let obj_id = context
            .well_defined_object_ids
            .get(&application.source_occurrence_id)
            .copied()
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "the function application has no exact WellDefinedObjId",
                )
            })?;
        let object = context
            .well_definedness
            .objects
            .iter()
            .find(|object| object.well_defined_obj_id == obj_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} is missing from the active certificate",
                        obj_id.value()
                    ),
                )
            })?;
        let Some(WellDefinedFunctionContract::StoredMembershipFact(contract_fact_id)) =
            object.function_contracts.first()
        else {
            return Err(universal_error(
                &default_line_file(),
                "the named function application has no verifier-selected membership FactId",
            ));
        };
        let contract_fact_id = *contract_fact_id;
        let binding = context
            .function_bindings
            .get(&contract_fact_id)
            .ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    format!(
                        "the function application has no in-scope binding for contract FactId {}",
                        contract_fact_id.value()
                    ),
                )
            })?;
        let mut current_head = self.render_obj_ir(application.head.as_ref(), context)?;
        let initial_function = binding.function.clone();
        let mut current_function = initial_function.clone();
        let mut current_uses_fn_space = binding.uses_fn_space;
        let mut current_membership =
            initial_membership_override.unwrap_or_else(|| binding.membership_proof_name.clone());

        for (layer_index, arguments) in application.argument_layers.iter().enumerate() {
            if arguments.len() != current_function.parameters.len() {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "application layer {} has {} arguments but its retained FnSpec has arity {}",
                        layer_index + 1,
                        arguments.len(),
                        current_function.parameters.len()
                    ),
                ));
            }
            let source_arguments = &application.source_argument_layers[layer_index];
            if arguments.len() != source_arguments.len() {
                return Err(universal_error(
                    &default_line_file(),
                    "function application changed its ordered source arguments during rendering",
                ));
            }
            let mut rendered_arguments = Vec::new();
            for source_argument in source_arguments {
                rendered_arguments.push(self.render_obj(source_argument, context)?);
            }
            let requirement_proof = self.render_application_requirements(
                application,
                layer_index,
                &current_function,
                &rendered_arguments,
                context,
            )?;
            let rendered_head = if layer_index == 0 {
                current_head.clone()
            } else {
                format!("({current_head})")
            };
            let applied = format!("{rendered_head} [{}]", rendered_arguments.join(", "));
            let argument_list = format!("[{}]", rendered_arguments.join(", "));
            let result_rule = if current_uses_fn_space {
                "Litex.fnSpaceResult"
            } else {
                "Litex.fnSetResult"
            };
            let result_membership = format!(
                "(by simpa using ({result_rule} (args := {argument_list}) {current_membership} rfl ({requirement_proof})))"
            );
            if layer_index + 1 == application.argument_layers.len() {
                return Ok(RenderedFunctionApplication {
                    result_membership,
                    contract_fact_id,
                    function: initial_function,
                });
            }
            let LitexToLeanObjectIr::FunctionSet { function: next } =
                current_function.return_set.as_ref()
            else {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "application retains another source layer after non-function return at layer {}",
                        layer_index + 1
                    ),
                ));
            };
            current_membership = result_membership;
            current_head = applied;
            current_function = next.as_ref().clone();
            current_uses_fn_space = function_ir_uses_fn_space(&current_function);
        }
        unreachable!("nonempty application layers return from the loop")
    }

    fn render_application_requirements(
        &self,
        application: &LitexToLeanFunctionApplicationIr,
        layer_index: usize,
        function: &LitexToLeanFunctionTypeIr,
        rendered_arguments: &[String],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        if rendered_arguments.len() != function.parameters.len() {
            return Err(universal_error(
                &default_line_file(),
                "application requirement renderer received the wrong argument arity",
            ));
        }
        let mut requirement_proofs = Vec::new();
        for parameter_index in 0..function.parameters.len() {
            requirement_proofs.push(self.resolve_application_requirement(
                application,
                WellDefinednessRequirementRole::FunctionArgumentMembership {
                    layer_index,
                    parameter_index,
                },
                context,
            )?);
        }
        for domain_index in 0..function.domain_facts.len() {
            requirement_proofs.push(self.resolve_application_requirement(
                application,
                WellDefinednessRequirementRole::FunctionDomain {
                    layer_index,
                    domain_index,
                },
                context,
            )?);
        }
        let mut requirement_context = context.clone();
        let mut requirement_types = Vec::with_capacity(requirement_proofs.len());
        for (index, (parameter, argument)) in function
            .parameters
            .iter()
            .zip(rendered_arguments.iter())
            .enumerate()
        {
            requirement_context
                .symbol_names
                .insert(parameter.symbol_id, format!("({argument})"));
            requirement_types.push((
                format!("__h_arg{index}"),
                format!(
                    "Litex.In ({argument}) {}",
                    self.render_obj_ir(&parameter.set, &requirement_context)?
                ),
            ));
        }
        for fact in function.domain_facts.iter() {
            requirement_types.push((
                format!(
                    "__h_dom{}",
                    requirement_types.len() - function.parameters.len()
                ),
                self.render_fact(fact, &requirement_context)?,
            ));
        }
        if requirement_types.len() != requirement_proofs.len() {
            return Err(universal_error(
                &default_line_file(),
                "application requirement propositions changed their retained arity",
            ));
        }
        let requirement_type = dependent_requirement_telescope(&requirement_types);
        let proof = dependent_requirement_proof(&requirement_proofs);
        Ok(format!("by\n  change {requirement_type}\n  exact {proof}"))
    }

    fn resolve_application_requirement(
        &self,
        application: &LitexToLeanFunctionApplicationIr,
        role: WellDefinednessRequirementRole,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let mut matching_ids = Vec::new();
        for requirement in context.well_definedness.target_requirements.iter() {
            if requirement.source_occurrence_id != application.source_occurrence_id
                || requirement.role != role
            {
                continue;
            }
            matching_ids.push(requirement.well_defined_fact_id.value());
            return context
                .well_defined_fact_names
                .get(&requirement.well_defined_fact_id)
                .cloned()
                .ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!(
                            "canonical source occurrence {} has no named WD fact for application role {role:?}; WellDefinedFactId {}",
                            application.source_occurrence_id.value(),
                            requirement.well_defined_fact_id.value()
                        ),
                    )
                });
        }
        Err(universal_error(
            &default_line_file(),
            format!(
                "no named exact WD fact was available for application role {role:?}; matching WellDefinedFactIds: {matching_ids:?}"
            ),
        ))
    }
}

fn merge_local_well_defined_context(
    target: &mut RenderContext,
    source: &RenderContext,
) -> Result<(), RuntimeError> {
    merge_well_defined_object_ids(target, source)?;
    target
        .well_defined_fact_names
        .extend(source.well_defined_fact_names.clone());
    target
        .well_defined_object_names
        .extend(source.well_defined_object_names.clone());
    target
        .well_defined_applicable_names
        .extend(source.well_defined_applicable_names.clone());
    target
        .well_defined_result_membership_names
        .extend(source.well_defined_result_membership_names.clone());
    Ok(())
}

fn replace_local_proof_name(context: &mut RenderContext, name: &str, replacement: &str) {
    for proof in context.well_defined_fact_names.values_mut() {
        if proof == name {
            *proof = replacement.to_string();
        }
    }
    for proof in context.well_defined_applicable_names.values_mut() {
        if proof == name {
            *proof = replacement.to_string();
        }
    }
    for proof in context.well_defined_result_membership_names.values_mut() {
        if proof == name {
            *proof = replacement.to_string();
        }
    }
}

fn generated_fact_name(fact_id: FactId) -> String {
    format!("__fact{}", fact_id.value())
}

fn generated_hypothesis_name(depth: usize, index: usize) -> String {
    format!("__h{depth}_{index}")
}

fn generated_object_name(obj_id: WellDefinedObjId) -> String {
    format!("__obj{}", obj_id.value())
}

fn generated_object_applicable_name(obj_id: WellDefinedObjId) -> String {
    format!("__obj{}_app", obj_id.value())
}

fn generated_object_result_name(obj_id: WellDefinedObjId) -> String {
    format!("__obj{}_result", obj_id.value())
}

fn well_defined_fact_name(context: &RenderContext, fact_id: WellDefinedFactId) -> String {
    let environment_depth = context.forall_depth.unwrap_or(0);
    format!("__wd{environment_depth}_{}", fact_id.value())
}

fn push_unique_local_proof_step(
    local_steps: &mut Vec<LocalProofStep>,
    step: LocalProofStep,
) -> Result<(), RuntimeError> {
    if let Some(existing) = local_steps
        .iter()
        .find(|existing| existing.name == step.name)
    {
        if existing.proposition == step.proposition && existing.proof == step.proof {
            return Ok(());
        }
        return Err(universal_error(
            &default_line_file(),
            format!(
                "local Lean proof name `{}` was assigned two different WD certificates",
                step.name
            ),
        ));
    }
    local_steps.push(step);
    Ok(())
}

fn render_local_proof_step(step: &LocalProofStep) -> String {
    render_local_proof_step_at_indent(step, 2)
}

fn render_local_proof_step_at_indent(step: &LocalProofStep, indentation: usize) -> String {
    let prefix = " ".repeat(indentation);
    let proof_prefix = " ".repeat(indentation + 2);
    let proof = format!("exact ({})", step.proof)
        .lines()
        .map(|line| format!("{proof_prefix}{line}"))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "{prefix}have {} : {} := by\n{proof}",
        step.name, step.proposition
    )
}

fn projection_source_index(
    source: &ForallFact,
    projection: &LitexToLeanFactIr,
) -> Result<usize, RuntimeError> {
    let Fact::ForallFact(projected) = &projection.proposition else {
        return Err(universal_error(
            &projection.proposition.line_file(),
            "a projected forall entry is not a forall",
        ));
    };
    if projected.then_facts.len() != 1 {
        return Err(universal_error(
            &projected.line_file,
            "the universal-object MVP requires one conclusion per stored projection",
        ));
    }
    let projected_fact = projected.then_facts[0].clone().to_fact();
    for (index, source_fact) in source.then_facts.iter().enumerate() {
        if facts_are_canonically_equal(&source_fact.clone().to_fact(), &projected_fact)? {
            return Ok(index);
        }
    }
    Err(universal_error(
        &projected.line_file,
        "a stored projection does not match any source forall conclusion",
    ))
}

fn facts_are_canonically_equal(left: &Fact, right: &Fact) -> Result<bool, RuntimeError> {
    if left.to_string() == right.to_string() {
        return Ok(true);
    }
    match (left, right) {
        (Fact::AtomicFact(left), Fact::AtomicFact(right)) => {
            canonical_atomic_facts_equal(left, right, MatchLimits::default()).map_err(|error| {
                universal_error(
                    &left.line_file(),
                    format!("failed to compare projected forall facts: {error:?}"),
                )
            })
        }
        _ => Ok(false),
    }
}

fn is_proof_carrying_arithmetic_obj(object: &Obj) -> bool {
    matches!(
        object,
        Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_)
    )
}

fn is_closed_synthetic_complex_application(
    operator: LitexToLeanBuiltinObjectOperatorIr,
    arguments: &[LitexToLeanObjectIr],
) -> bool {
    matches!(
        operator,
        LitexToLeanBuiltinObjectOperatorIr::Add
            | LitexToLeanBuiltinObjectOperatorIr::Sub
            | LitexToLeanBuiltinObjectOperatorIr::Mul
    ) && arguments.iter().all(|argument| match argument {
        LitexToLeanObjectIr::Number { normalized_value } => normalized_value
            .strip_prefix('-')
            .unwrap_or(normalized_value)
            .chars()
            .all(|character| character.is_ascii_digit()),
        _ => false,
    })
}

fn add_well_defined_object_proof_closure(
    objects_by_id: &HashMap<WellDefinedObjId, &LitexToLeanWellDefinednessObjectIr>,
    pending_object_ids: &mut Vec<WellDefinedObjId>,
    selected_object_ids: &mut HashSet<WellDefinedObjId>,
    selected_fact_ids: &mut HashSet<WellDefinedFactId>,
) -> Result<(), RuntimeError> {
    while let Some(proof_id) = pending_object_ids.pop() {
        if !selected_object_ids.insert(proof_id) {
            continue;
        }
        let object = objects_by_id.get(&proof_id).ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!(
                    "well-defined object proof {} is missing from its frozen compiler certificate",
                    proof_id.value()
                ),
            )
        })?;
        selected_fact_ids.extend(object.well_defined_fact_ids.iter().copied());
        selected_fact_ids.extend(
            object
                .target_requirements
                .iter()
                .map(|requirement| requirement.well_defined_fact_id),
        );
        pending_object_ids.extend(object.child_uses.iter().map(|child| child.obj_id));
    }
    Ok(())
}

fn well_defined_closure_uses_binder_scope(
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    initial_object_ids: &HashSet<WellDefinedObjId>,
) -> Result<bool, RuntimeError> {
    let objects_by_id = well_definedness
        .objects
        .iter()
        .map(|object| (object.well_defined_obj_id, object))
        .collect::<HashMap<_, _>>();
    let mut pending_object_ids = initial_object_ids.iter().copied().collect::<Vec<_>>();
    let mut selected_object_ids = HashSet::new();
    let mut selected_fact_ids = HashSet::new();
    add_well_defined_object_proof_closure(
        &objects_by_id,
        &mut pending_object_ids,
        &mut selected_object_ids,
        &mut selected_fact_ids,
    )?;

    if selected_object_ids.iter().any(|object_id| {
        let object = objects_by_id
            .get(object_id)
            .expect("selected WD object must exist in the frozen certificate");
        !object.ambient_binder_scope_ids.is_empty() || object.owned_binder_scope_id.is_some()
    }) {
        return Ok(true);
    }

    Ok(well_definedness.facts.iter().any(|fact| {
        selected_fact_ids.contains(&fact.well_defined_fact_id)
            && !fact.ambient_binder_scope_ids.is_empty()
    }))
}

fn is_proof_carrying_object(object: &Obj) -> bool {
    matches!(
        object,
        Obj::FnObj(_)
            | Obj::AnonymousFn(_)
            | Obj::Add(_)
            | Obj::Sub(_)
            | Obj::Mul(_)
            | Obj::Div(_)
            | Obj::ListSet(_)
    )
}

fn collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
    fact: &LitexToLeanFactIr,
    source_occurrence_ids: &mut HashSet<SourceObjectOccurrenceId>,
) -> Result<(), RuntimeError> {
    match &fact.proof {
        LitexToLeanFactProofIr::Memo { proof } => {
            let nested = LitexToLeanFactIr {
                fact_id: fact.fact_id,
                proposition: fact.proposition.clone(),
                proof: proof.as_ref().clone(),
            };
            collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                &nested,
                source_occurrence_ids,
            )?;
        }
        LitexToLeanFactProofIr::RuleApplication {
            rule,
            parameter_requirements,
            premises,
        } => {
            if let LitexToLeanProofRuleIr::KnownForallInstantiation { arguments, .. } = rule {
                for argument in arguments {
                    let argument =
                        LitexToLeanObjectIr::lower(&argument.argument).map_err(|message| {
                            universal_error(&fact.proposition.line_file(), message)
                        })?;
                    collect_proof_carrying_object_occurrence_ids(&argument, source_occurrence_ids)?;
                }
            }
            for child in parameter_requirements.iter().chain(premises.iter()) {
                collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                    child,
                    source_occurrence_ids,
                )?;
            }
        }
        LitexToLeanFactProofIr::Composite { steps } => {
            for child in steps {
                collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                    child,
                    source_occurrence_ids,
                )?;
            }
        }
        LitexToLeanFactProofIr::ForallIntroduction {
            parameter_premises,
            premises,
            inferred_premises,
            conclusions,
        } => {
            for premise in parameter_premises.iter().chain(premises.iter()) {
                collect_proof_carrying_object_occurrence_ids_from_fact(
                    &premise.fact,
                    source_occurrence_ids,
                )?;
            }
            for child in inferred_premises.iter().chain(conclusions.iter()) {
                collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                    child,
                    source_occurrence_ids,
                )?;
            }
        }
        LitexToLeanFactProofIr::ObjectDefinition {
            value, value_check, ..
        } => {
            collect_proof_carrying_object_occurrence_ids(value, source_occurrence_ids)?;
            if let Some(child) = value_check {
                collect_proof_carrying_object_occurrence_ids_from_compiler_fact(
                    child,
                    source_occurrence_ids,
                )?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn collect_proof_carrying_object_occurrence_ids_from_fact(
    fact: &Fact,
    source_occurrence_ids: &mut HashSet<SourceObjectOccurrenceId>,
) -> Result<(), RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic) => {
            for object in atomic.args_ref() {
                let object = LitexToLeanObjectIr::lower(object)
                    .map_err(|message| universal_error(&fact.line_file(), message))?;
                collect_proof_carrying_object_occurrence_ids(&object, source_occurrence_ids)?;
            }
        }
        Fact::ForallFact(forall) => {
            for domain in forall.dom_facts.iter() {
                collect_proof_carrying_object_occurrence_ids_from_fact(
                    &domain.clone().into(),
                    source_occurrence_ids,
                )?;
            }
            for conclusion in forall.then_facts.iter() {
                collect_proof_carrying_object_occurrence_ids_from_fact(
                    &conclusion.clone().to_fact(),
                    source_occurrence_ids,
                )?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn arithmetic_source_operator_and_arguments(
    object: &Obj,
) -> Option<(LitexToLeanBuiltinObjectOperatorIr, Vec<&Obj>)> {
    match object {
        Obj::Add(value) => Some((
            LitexToLeanBuiltinObjectOperatorIr::Add,
            vec![value.left.as_ref(), value.right.as_ref()],
        )),
        Obj::Sub(value) => Some((
            LitexToLeanBuiltinObjectOperatorIr::Sub,
            vec![value.left.as_ref(), value.right.as_ref()],
        )),
        Obj::Mul(value) => Some((
            LitexToLeanBuiltinObjectOperatorIr::Mul,
            vec![value.left.as_ref(), value.right.as_ref()],
        )),
        Obj::Div(value) => Some((
            LitexToLeanBuiltinObjectOperatorIr::Div,
            vec![value.left.as_ref(), value.right.as_ref()],
        )),
        _ => None,
    }
}

fn collect_proof_carrying_object_occurrence_ids(
    object: &LitexToLeanObjectIr,
    source_occurrence_ids: &mut HashSet<SourceObjectOccurrenceId>,
) -> Result<(), RuntimeError> {
    match object {
        LitexToLeanObjectIr::BuiltinApp {
            source_occurrence_id,
            semantic_key,
            operator,
            arguments,
            ..
        } => {
            if matches!(
                operator,
                LitexToLeanBuiltinObjectOperatorIr::Add
                    | LitexToLeanBuiltinObjectOperatorIr::Sub
                    | LitexToLeanBuiltinObjectOperatorIr::Mul
                    | LitexToLeanBuiltinObjectOperatorIr::Div
            ) {
                if let Some(source_occurrence_id) = source_occurrence_id {
                    source_occurrence_ids.insert(*source_occurrence_id);
                } else if is_closed_synthetic_complex_application(*operator, arguments) {
                    // Verifier-generated closed arithmetic is not a source
                    // occurrence. It is reconstructed only through the
                    // shared numeral/closure theorem schema below, with all
                    // constructor proofs explicit.
                    return Ok(());
                } else {
                    return Err(universal_error(
                        &default_line_file(),
                        format!(
                            "proof-carrying operator `{operator:?}` for `{semantic_key}` has no parser-owned source occurrence ID"
                        ),
                    ));
                }
            }
            for argument in arguments {
                collect_proof_carrying_object_occurrence_ids(argument, source_occurrence_ids)?;
            }
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            source_occurrence_ids.insert(application.source_occurrence_id);
            collect_proof_carrying_object_occurrence_ids(
                application.head.as_ref(),
                source_occurrence_ids,
            )?;
            for layer in application.argument_layers.iter() {
                for argument in layer {
                    collect_proof_carrying_object_occurrence_ids(argument, source_occurrence_ids)?;
                }
            }
        }
        LitexToLeanObjectIr::Collection {
            source_occurrence_id,
            constructor: LitexToLeanCollectionObjectIr::ListSet,
            items,
            ..
        } => {
            let source_occurrence_id = source_occurrence_id.ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "proof-carrying list set has no parser-owned source occurrence ID",
                )
            })?;
            source_occurrence_ids.insert(source_occurrence_id);
            for item in items {
                collect_proof_carrying_object_occurrence_ids(item, source_occurrence_ids)?;
            }
        }
        LitexToLeanObjectIr::Collection { items, .. } => {
            for item in items {
                collect_proof_carrying_object_occurrence_ids(item, source_occurrence_ids)?;
            }
        }
        LitexToLeanObjectIr::SetBuilder(set_builder) => {
            collect_proof_carrying_object_occurrence_ids(
                set_builder.set.as_ref(),
                source_occurrence_ids,
            )?;
        }
        LitexToLeanObjectIr::AnonymousFunction(function) => {
            let source_occurrence_id = function.source_occurrence_id.ok_or_else(|| {
                universal_error(
                    &default_line_file(),
                    "proof-carrying anonymous function has no parser-owned source occurrence ID",
                )
            })?;
            source_occurrence_ids.insert(source_occurrence_id);
        }
        LitexToLeanObjectIr::FunctionSet { function } => {
            for parameter in function.parameters.iter() {
                collect_proof_carrying_object_occurrence_ids(
                    &parameter.set,
                    source_occurrence_ids,
                )?;
            }
            collect_proof_carrying_object_occurrence_ids(
                function.return_set.as_ref(),
                source_occurrence_ids,
            )?;
        }
        LitexToLeanObjectIr::ClosedRange { start, end }
        | LitexToLeanObjectIr::Range { start, end } => {
            collect_proof_carrying_object_occurrence_ids(start, source_occurrence_ids)?;
            collect_proof_carrying_object_occurrence_ids(end, source_occurrence_ids)?;
        }
        LitexToLeanObjectIr::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => {
            for argument in [index_set, family_set, family_function] {
                collect_proof_carrying_object_occurrence_ids(argument, source_occurrence_ids)?;
            }
        }
        LitexToLeanObjectIr::SequenceSet { values, length } => {
            collect_proof_carrying_object_occurrence_ids(values, source_occurrence_ids)?;
            if let Some(length) = length {
                collect_proof_carrying_object_occurrence_ids(length, source_occurrence_ids)?;
            }
        }
        LitexToLeanObjectIr::Aggregate { arguments, .. } => {
            for argument in arguments {
                collect_proof_carrying_object_occurrence_ids(argument, source_occurrence_ids)?;
            }
        }
        LitexToLeanObjectIr::TupleDimension(object) => {
            collect_proof_carrying_object_occurrence_ids(object, source_occurrence_ids)?;
        }
        LitexToLeanObjectIr::IndexedAccess { object, index } => {
            collect_proof_carrying_object_occurrence_ids(object, source_occurrence_ids)?;
            collect_proof_carrying_object_occurrence_ids(index, source_occurrence_ids)?;
        }
        LitexToLeanObjectIr::Symbol { .. }
        | LitexToLeanObjectIr::Number { .. }
        | LitexToLeanObjectIr::Constant(_)
        | LitexToLeanObjectIr::StandardSet(_) => {}
    }
    Ok(())
}

fn resolve_source_occurrence_object_ids(
    well_definedness: &LitexToLeanWellDefinednessCertificateIr,
    source_occurrence_ids: &HashSet<SourceObjectOccurrenceId>,
    context: &mut RenderContext,
    line_file: &LineFile,
) -> Result<HashSet<WellDefinedObjId>, RuntimeError> {
    let mut result = HashSet::new();
    for source_occurrence_id in source_occurrence_ids {
        if let Some(proof_id) = context
            .well_defined_object_ids
            .get(source_occurrence_id)
            .copied()
        {
            result.insert(proof_id);
            continue;
        }
        let matches = well_definedness
            .source_object_uses
            .iter()
            .filter(|source_use| source_use.source_occurrence_id == *source_occurrence_id)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(universal_error(
                line_file,
                format!(
                    "proof-carrying source occurrence {} has {} exact WD object uses; expected exactly one",
                    source_occurrence_id.value(),
                    matches.len(),
                ),
            ));
        }
        let proof_id = matches[0].well_defined_obj_id;
        context
            .well_defined_object_ids
            .insert(*source_occurrence_id, proof_id);
        result.insert(proof_id);
    }
    Ok(result)
}

fn render_explicit_binders(
    binder_names: &[String],
    binder_types: &[String],
) -> Result<Vec<String>, RuntimeError> {
    if binder_names.len() != binder_types.len() {
        return Err(universal_error(
            &default_line_file(),
            "a scoped Lean declaration has mismatched binder names and types",
        ));
    }
    Ok(binder_names
        .iter()
        .zip(binder_types.iter())
        .map(|(name, binder_type)| format!("({name} : {binder_type})"))
        .collect())
}

/// Keep fixed-object aliases independent of unrelated surrounding binders.
/// Atomic bound symbols need only their own value binder; closed primitives
/// need none.  Compound objects conservatively retain the full verified scope
/// because their applicability/constructor certificates may cite any of its
/// proof binders.
fn object_declaration_binders(
    object: &Obj,
    context: &RenderContext,
    binder_names: &[String],
    binder_types: &[String],
) -> Result<(Vec<String>, Vec<String>), RuntimeError> {
    if binder_names.len() != binder_types.len() {
        return Err(universal_error(
            &default_line_file(),
            "obj_N declaration has mismatched binder names and types",
        ));
    }
    match object {
        Obj::Atom(atom) => {
            let Some(symbol_id) = atom.symbol_ref().map(SymbolRef::id) else {
                return Ok((Vec::new(), Vec::new()));
            };
            let Some(name) = context.symbol_names.get(&symbol_id) else {
                return Ok((Vec::new(), Vec::new()));
            };
            let index = binder_names
                .iter()
                .position(|binder_name| binder_name == name)
                .ok_or_else(|| {
                    universal_error(
                        &default_line_file(),
                        format!(
                            "obj_N for SymbolId {} cannot find its Lean binder `{name}`",
                            symbol_id.value()
                        ),
                    )
                })?;
            Ok((vec![name.clone()], vec![binder_types[index].clone()]))
        }
        Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::StandardSet(_) => Ok((Vec::new(), Vec::new())),
        _ => Ok((binder_names.to_vec(), binder_types.to_vec())),
    }
}

fn apply_scoped_declaration(
    declaration_name: &str,
    required_binder_names: &[String],
    required_binder_types: &[String],
    available_binder_names: &[String],
    available_binder_types: &[String],
    description: &str,
) -> Result<String, RuntimeError> {
    if required_binder_names.len() != required_binder_types.len()
        || available_binder_names.len() != available_binder_types.len()
    {
        return Err(universal_error(
            &default_line_file(),
            format!("{description} has mismatched scoped binder metadata"),
        ));
    }
    let mut arguments = Vec::with_capacity(required_binder_names.len());
    for (required_name, required_type) in required_binder_names
        .iter()
        .zip(required_binder_types.iter())
    {
        let Some(index) = available_binder_names
            .iter()
            .position(|available_name| available_name == required_name)
        else {
            return Err(universal_error(
                &default_line_file(),
                format!("{description} requires unavailable Lean binder `{required_name}`"),
            ));
        };
        // WD aliases can make two renderings of the same binder type textually
        // different (`y` versus `obj_N y`, or `R` versus `obj_M`) while Lean
        // still sees them as definitionally equal.  Identity is guarded by
        // verifier-owned IDs and declaration scope names; final Lean checking
        // is the authoritative type-equivalence test.
        let _ = (required_type, available_binder_types.get(index));
        arguments.push(required_name.clone());
    }
    if arguments.is_empty() {
        Ok(declaration_name.to_string())
    } else {
        Ok(format!("({declaration_name} {})", arguments.join(" ")))
    }
}

fn apply_scoped_declaration_with_substitutions(
    declaration_name: &str,
    required_binder_names: &[String],
    required_binder_types: &[String],
    substitutions: &HashMap<String, String>,
    description: &str,
) -> Result<String, RuntimeError> {
    if required_binder_names.len() != required_binder_types.len() {
        return Err(universal_error(
            &default_line_file(),
            format!("{description} has mismatched scoped binder metadata"),
        ));
    }
    let mut arguments = Vec::with_capacity(required_binder_names.len());
    for required_name in required_binder_names {
        let argument = substitutions.get(required_name).ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!(
                    "{description} requires binder `{required_name}` outside the target constructor's available proof telescope"
                ),
            )
        })?;
        arguments.push(format!("({argument})"));
    }
    if arguments.is_empty() {
        Ok(declaration_name.to_string())
    } else {
        Ok(format!("({declaration_name} {})", arguments.join(" ")))
    }
}

fn merge_well_defined_object_ids(
    target: &mut RenderContext,
    source: &RenderContext,
) -> Result<(), RuntimeError> {
    for (source_occurrence_id, proof_id) in source.well_defined_object_ids.iter() {
        if let Some(previous) = target
            .well_defined_object_ids
            .insert(*source_occurrence_id, *proof_id)
        {
            if previous != *proof_id {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "source occurrence {} maps to WellDefinedObjIds {} and {}",
                        source_occurrence_id.value(),
                        previous.value(),
                        proof_id.value()
                    ),
                ));
            }
        }
    }
    for (obj_id, name) in source.well_defined_object_names.iter() {
        if let Some(previous) = target
            .well_defined_object_names
            .insert(*obj_id, name.clone())
        {
            if previous.as_str() != name.as_str() {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} maps to Lean names `{previous}` and `{name}`",
                        obj_id.value()
                    ),
                ));
            }
        }
    }
    for (obj_id, name) in source.well_defined_applicable_names.iter() {
        if let Some(previous) = target
            .well_defined_applicable_names
            .insert(*obj_id, name.clone())
        {
            if previous.as_str() != name.as_str() {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} maps to applicability helpers `{previous}` and `{name}`",
                        obj_id.value()
                    ),
                ));
            }
        }
    }
    for (obj_id, name) in source.well_defined_result_membership_names.iter() {
        if let Some(previous) = target
            .well_defined_result_membership_names
            .insert(*obj_id, name.clone())
        {
            if previous.as_str() != name.as_str() {
                return Err(universal_error(
                    &default_line_file(),
                    format!(
                        "WellDefinedObjId {} maps to result-membership helpers `{previous}` and `{name}`",
                        obj_id.value()
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn validate_complex_operand_membership(
    proposition: &Fact,
    expected_operand: &Obj,
) -> Result<(), RuntimeError> {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
        return Err(universal_error(
            &proposition.line_file(),
            "proof-carrying arithmetic retained a non-membership requirement",
        ));
    };
    if obj_equality_key(&membership.element) != obj_equality_key(expected_operand)
        || !matches!(&membership.set, Obj::StandardSet(StandardSet::C))
    {
        return Err(universal_error(
            &proposition.line_file(),
            "proof-carrying arithmetic changed an ordered `In operand C` requirement",
        ));
    }
    Ok(())
}

fn validate_list_set_pairwise_distinct(
    proposition: &Fact,
    expected_left: &Obj,
    expected_right: &Obj,
) -> Result<(), RuntimeError> {
    let Fact::AtomicFact(AtomicFact::NotEqualFact(distinct)) = proposition else {
        return Err(universal_error(
            &proposition.line_file(),
            "proof-carrying list set retained a non-inequality pairwise requirement",
        ));
    };
    if obj_equality_key(&distinct.left) != obj_equality_key(expected_left)
        || obj_equality_key(&distinct.right) != obj_equality_key(expected_right)
    {
        return Err(universal_error(
            &proposition.line_file(),
            "proof-carrying list set changed an indexed `left != right` requirement",
        ));
    }
    Ok(())
}

fn validate_divisor_nonzero(
    proposition: &Fact,
    expected_divisor: &Obj,
) -> Result<(), RuntimeError> {
    let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = proposition else {
        return Err(universal_error(
            &proposition.line_file(),
            "proof-carrying division retained a non-inequality nonzero requirement",
        ));
    };
    if obj_equality_key(&nonzero.left) != obj_equality_key(expected_divisor)
        || !matches!(&nonzero.right, Obj::Number(number) if number.normalized_value == "0")
    {
        return Err(universal_error(
            &proposition.line_file(),
            "proof-carrying division changed its ordered `denominator != 0` requirement",
        ));
    }
    Ok(())
}

fn native_standard_set_projection_path(
    source: &StandardSet,
    target: &StandardSet,
) -> Option<Vec<String>> {
    fn rank(set: &StandardSet) -> Option<usize> {
        match set {
            StandardSet::N => Some(0),
            StandardSet::Z => Some(1),
            StandardSet::Q => Some(2),
            StandardSet::R => Some(3),
            StandardSet::C => Some(4),
            _ => None,
        }
    }

    const ADJACENT_THEOREMS: [&str; 4] = [
        "naturalInInteger",
        "integerInRational",
        "rationalInReal",
        "realInComplex",
    ];
    let source_rank = rank(source)?;
    let target_rank = rank(target)?;
    if source_rank >= target_rank {
        return None;
    }
    Some(
        ADJACENT_THEOREMS[source_rank..target_rank]
            .iter()
            .map(|theorem_name| rule_theorem_name(theorem_name))
            .collect(),
    )
}

fn render_closed_standard_membership(
    emitter: &UniversalEmitter,
    proposition: &Fact,
    context: &RenderContext,
) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
        return Err(universal_error(
            &proposition.line_file(),
            "closed standard membership proof targets a non-membership fact",
        ));
    };
    render_closed_standard_membership_object(
        emitter,
        &membership.element,
        &membership.set,
        &membership.line_file,
        context,
    )
}

fn render_closed_standard_membership_object(
    emitter: &UniversalEmitter,
    element: &Obj,
    set: &Obj,
    line_file: &LineFile,
    context: &RenderContext,
) -> Result<String, RuntimeError> {
    if matches!(set, Obj::StandardSet(StandardSet::R)) {
        let (left, right, theorem_name) = match element {
            Obj::Add(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "realAddClosure",
            ),
            Obj::Sub(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "realSubClosure",
            ),
            Obj::Mul(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "realMulClosure",
            ),
            Obj::Div(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "realDivClosure",
            ),
            _ => (None, None, ""),
        };
        if let (Some(left), Some(right)) = (left, right) {
            let theorem = rule_theorem_name(theorem_name);
            let left_real =
                render_closed_standard_membership_object(emitter, left, set, line_file, context)?;
            let right_real =
                render_closed_standard_membership_object(emitter, right, set, line_file, context)?;
            if is_proof_carrying_arithmetic_obj(element) {
                let target_ir = LitexToLeanObjectIr::lower(element)
                    .map_err(|message| universal_error(line_file, message))?;
                let LitexToLeanObjectIr::BuiltinApp {
                    source_occurrence_id,
                    semantic_key,
                    operator,
                    arguments,
                } = target_ir
                else {
                    return Err(universal_error(
                        line_file,
                        "closed real arithmetic retained a non-builtin target object",
                    ));
                };
                let complex_proofs = emitter.resolve_builtin_argument_membership_proofs(
                    source_occurrence_id,
                    &semantic_key,
                    operator,
                    &arguments,
                    context,
                )?;
                if operator == LitexToLeanBuiltinObjectOperatorIr::Div {
                    let nonzero_proof = emitter.resolve_builtin_argument_nonzero_proof(
                        source_occurrence_id,
                        &semantic_key,
                        operator,
                        &arguments,
                        context,
                    )?;
                    return Ok(format!(
                        "({theorem} ({}) ({}) ({nonzero_proof}) ({left_real}) ({right_real}))",
                        complex_proofs[0], complex_proofs[1]
                    ));
                }
                return Ok(format!(
                    "({theorem} ({}) ({}) ({left_real}) ({right_real}))",
                    complex_proofs[0], complex_proofs[1]
                ));
            }
            return Ok(format!("({theorem} ({left_real}) ({right_real}))"));
        }
    }

    let Obj::Number(number) = element else {
        return Err(universal_error(
            line_file,
            "closed standard membership proof targets an unsupported non-numeral expression",
        ));
    };
    let negative_magnitude = number
        .normalized_value
        .strip_prefix('-')
        .filter(|magnitude| {
            !magnitude.is_empty()
                && magnitude
                    .chars()
                    .all(|character| character.is_ascii_digit())
        });
    if negative_magnitude.is_none()
        && !number
            .normalized_value
            .chars()
            .all(|character| character.is_ascii_digit())
    {
        return Err(universal_error(
            line_file,
            "the universal-object numeral theorem currently requires a natural numeral",
        ));
    }
    let Obj::StandardSet(set) = set else {
        return Err(universal_error(
            line_file,
            "closed standard membership proof targets a nonstandard set",
        ));
    };
    let theorem_name = match (set, negative_magnitude.is_some()) {
        (StandardSet::N, false) => "numeralInN",
        (StandardSet::Z, false) => "numeralInZ",
        (StandardSet::Q, false) => "numeralInQ",
        (StandardSet::R, false) => "numeralInR",
        (StandardSet::C, false) => "numeralInC",
        (StandardSet::C, true) => "negativeNumeralInC",
        _ => {
            return Err(universal_error(
                line_file,
                "refined standard-set numerals require a separate builtin theorem",
            ))
        }
    };
    let theorem = rule_theorem_name(theorem_name);
    Ok(format!(
        "{} {}",
        theorem,
        negative_magnitude.unwrap_or(&number.normalized_value)
    ))
}

fn standard_set_name(set: LitexToLeanStandardSetIr) -> &'static str {
    match set {
        LitexToLeanStandardSetIr::PositiveNatural => "Litex.NPos",
        LitexToLeanStandardSetIr::Natural => "Litex.N",
        LitexToLeanStandardSetIr::Rational => "Litex.Q",
        LitexToLeanStandardSetIr::Integer => "Litex.Z",
        LitexToLeanStandardSetIr::Real => "Litex.R",
        LitexToLeanStandardSetIr::Complex => "Litex.C",
        LitexToLeanStandardSetIr::PositiveRational => "Litex.QPos",
        LitexToLeanStandardSetIr::PositiveReal => "Litex.RPos",
        LitexToLeanStandardSetIr::NegativeRational => "Litex.QNeg",
        LitexToLeanStandardSetIr::NegativeInteger => "Litex.ZNeg",
        LitexToLeanStandardSetIr::NegativeReal => "Litex.RNeg",
        LitexToLeanStandardSetIr::NonzeroRational => "Litex.QStar",
        LitexToLeanStandardSetIr::NonzeroInteger => "Litex.ZStar",
        LitexToLeanStandardSetIr::NonzeroReal => "Litex.RStar",
        LitexToLeanStandardSetIr::NonzeroComplex => "Litex.CStar",
    }
}

fn right_associated(mut parts: Vec<String>, separator: &str, empty: &str) -> String {
    let Some(mut output) = parts.pop() else {
        return empty.to_string();
    };
    while let Some(part) = parts.pop() {
        output = format!("{}{}({})", part, separator, output);
    }
    output
}

fn conjunction_components(fact: &Fact) -> Result<Vec<Fact>, RuntimeError> {
    match fact {
        Fact::AndFact(and_fact) => Ok(and_fact.facts.iter().cloned().map(Fact::from).collect()),
        Fact::ChainFact(chain_fact) => {
            Ok(chain_fact.facts()?.into_iter().map(Fact::from).collect())
        }
        _ => Err(universal_error(
            &fact.line_file(),
            "conjunction introduction retained a non-conjunction target",
        )),
    }
}

fn right_associated_disjunction_injection(
    proof: String,
    selected_index: usize,
    branch_count: usize,
) -> String {
    if branch_count <= 1 {
        return proof;
    }
    if selected_index == 0 {
        return format!("Or.inl ({proof})");
    }
    format!(
        "Or.inr ({})",
        right_associated_disjunction_injection(proof, selected_index - 1, branch_count - 1)
    )
}

/// Encode the ordered function-domain evidence as a dependent existential
/// telescope. Later requirement propositions may cite the proof binder of an
/// earlier requirement, while the whole telescope still inhabits `Prop`.
fn dependent_requirement_telescope(requirements: &[(String, String)]) -> String {
    let mut output = "True".to_string();
    for (name, proposition) in requirements.iter().rev() {
        output = format!("∃ {name} : {proposition}, {output}");
    }
    output
}

fn function_ir_uses_fn_space(function: &LitexToLeanFunctionTypeIr) -> bool {
    let parameter_symbol_ids = function
        .parameters
        .iter()
        .map(|parameter| parameter.symbol_id)
        .collect::<HashSet<_>>();
    function.domain_facts.is_empty()
        && function.parameters.iter().all(|parameter| {
            object_ir_is_independent_of_symbols(&parameter.set, &parameter_symbol_ids)
        })
        && object_ir_is_independent_of_symbols(function.return_set.as_ref(), &parameter_symbol_ids)
}

fn object_ir_is_independent_of_symbols(
    object: &LitexToLeanObjectIr,
    symbol_ids: &HashSet<SymbolId>,
) -> bool {
    match object {
        LitexToLeanObjectIr::Symbol { symbol_id, .. } => !symbol_ids.contains(symbol_id),
        LitexToLeanObjectIr::FunctionSet { function } => {
            function.domain_facts.is_empty()
                && function.parameters.iter().all(|parameter| {
                    object_ir_is_independent_of_symbols(&parameter.set, symbol_ids)
                })
                && object_ir_is_independent_of_symbols(function.return_set.as_ref(), symbol_ids)
        }
        LitexToLeanObjectIr::FunctionApplication(application) => {
            object_ir_is_independent_of_symbols(application.head.as_ref(), symbol_ids)
                && application.argument_layers.iter().all(|layer| {
                    layer
                        .iter()
                        .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids))
                })
        }
        LitexToLeanObjectIr::ClosedRange { start, end }
        | LitexToLeanObjectIr::Range { start, end } => {
            object_ir_is_independent_of_symbols(start, symbol_ids)
                && object_ir_is_independent_of_symbols(end, symbol_ids)
        }
        LitexToLeanObjectIr::GeneralCartesianProduct {
            index_set,
            family_set,
            family_function,
        } => {
            object_ir_is_independent_of_symbols(index_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_set, symbol_ids)
                && object_ir_is_independent_of_symbols(family_function, symbol_ids)
        }
        LitexToLeanObjectIr::SequenceSet { values, length } => {
            object_ir_is_independent_of_symbols(values, symbol_ids)
                && length
                    .as_ref()
                    .is_none_or(|length| object_ir_is_independent_of_symbols(length, symbol_ids))
        }
        LitexToLeanObjectIr::Aggregate { arguments, .. } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        LitexToLeanObjectIr::TupleDimension(object) => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
        }
        LitexToLeanObjectIr::IndexedAccess { object, index } => {
            object_ir_is_independent_of_symbols(object, symbol_ids)
                && object_ir_is_independent_of_symbols(index, symbol_ids)
        }
        LitexToLeanObjectIr::BuiltinApp { arguments, .. }
        | LitexToLeanObjectIr::Collection {
            items: arguments, ..
        } => arguments
            .iter()
            .all(|argument| object_ir_is_independent_of_symbols(argument, symbol_ids)),
        LitexToLeanObjectIr::SetBuilder(_) | LitexToLeanObjectIr::AnonymousFunction(_) => false,
        LitexToLeanObjectIr::Number { .. }
        | LitexToLeanObjectIr::Constant(_)
        | LitexToLeanObjectIr::StandardSet(_) => true,
    }
}

fn dependent_requirement_projection(base: &str, index: usize) -> String {
    let mut tail = base.to_string();
    for _ in 0..index {
        tail = format!("Exists.choose_spec ({tail})");
    }
    format!("Exists.choose ({tail})")
}

fn dependent_requirement_proof(proofs: &[String]) -> String {
    let mut output = "True.intro".to_string();
    for proof in proofs.iter().rev() {
        output = format!("Exists.intro ({proof}) ({output})");
    }
    output
}

fn lean_text_is_natural_literal(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
}

fn natural_number_literal(object: &Obj) -> Option<&str> {
    let Obj::Number(number) = object else {
        return None;
    };
    lean_text_is_natural_literal(&number.normalized_value)
        .then_some(number.normalized_value.as_str())
}

fn right_associated_conjunction_proof(mut proofs: Vec<String>) -> Option<String> {
    let mut output = format!("({})", proofs.pop()?);
    while let Some(proof) = proofs.pop() {
        output = format!("And.intro ({proof}) ({output})");
    }
    Some(output)
}

fn conjunction_projection(base: &str, index: usize, count: usize) -> String {
    if count <= 1 {
        return base.to_string();
    }
    if index == 0 {
        return format!("({base}).1");
    }
    conjunction_projection(&format!("({base}).2"), index - 1, count - 1)
}

fn render_top_level_forall_type(binders: &[String], conclusion: &str) -> String {
    if binders.is_empty() {
        return conclusion.to_string();
    }
    let inline = format!("∀ {}, {conclusion}", binders.join(" "));
    if inline.chars().count() <= 100 {
        return inline;
    }

    let mut output = String::new();
    for (index, pair) in binders.chunks(2).enumerate() {
        if index == 0 {
            output.push_str("∀ ");
        } else {
            output.push_str("\n  ");
        }
        output.push_str(&pair.join(" "));
    }
    output.push_str(",\n  ");
    output.push_str(conclusion);
    output
}

fn render_declaration_head(declaration: &str, declaration_type: &str) -> String {
    if declaration_type.contains('\n') {
        format!(
            "{declaration} :\n  {}",
            declaration_type.replace('\n', "\n  ")
        )
    } else {
        format!("{declaration} : {declaration_type}")
    }
}

fn lean_name(name: &str) -> String {
    let mut output = String::new();
    for character in name.chars() {
        if character == '_' || character.is_ascii_alphanumeric() {
            output.push(character);
        } else {
            output.push('_');
        }
    }
    if output.is_empty() || output.starts_with(|character: char| character.is_ascii_digit()) {
        output.insert_str(0, "litex_");
    }
    if matches!(
        output.as_str(),
        "axiom"
            | "by"
            | "def"
            | "do"
            | "else"
            | "end"
            | "example"
            | "false"
            | "for"
            | "forall"
            | "fun"
            | "have"
            | "if"
            | "import"
            | "in"
            | "inductive"
            | "let"
            | "match"
            | "namespace"
            | "open"
            | "opaque"
            | "partial"
            | "private"
            | "protected"
            | "structure"
            | "theorem"
            | "then"
            | "true"
            | "where"
            | "with"
            // `id` is not a parser keyword, but Mathlib already owns the root
            // declaration. Source globals use the same spelling everywhere,
            // so reserving it here keeps definitions and later references in
            // lockstep instead of allowing a late Lean collision.
            | "id"
    ) {
        output.insert_str(0, "litex_");
    }
    output
}

fn render_normal_predicate_name(name: &AtomicName) -> String {
    if name.to_string() == IS_CHOICE_FUNCTION_FOR {
        "Litex.IsChoiceFunctionFor".to_string()
    } else {
        lean_name(&name.to_string())
    }
}

fn unreachable_unemitted_statement_ir<T>() -> T {
    unreachable!("unsupported statement IR payloads are unconstructible")
}

fn statement_proof_facts(statement: &LitexToLeanStatementIr) -> Option<Vec<&LitexToLeanFactIr>> {
    let (facts, inferred_facts): (&[LitexToLeanFactIr], &[LitexToLeanFactIr]) = match statement {
        LitexToLeanStatementIr::Fact(ir) => {
            let facts = if ir.source.fact_id.is_some() {
                std::slice::from_ref(&ir.source)
            } else {
                ir.stored_projections.as_slice()
            };
            return Some(facts.iter().chain(ir.inferred_facts.iter()).collect());
        }
        LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(ir)) => {
            (&ir.facts, &ir.inferred_facts)
        }
        LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(ir)) => {
            (&ir.facts, &ir.inferred_facts)
        }
        LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(ir)) => {
            (&ir.facts, &ir.inferred_facts)
        }
        LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessExistFact(ir)) => {
            (&ir.facts, &ir.inferred_facts)
        }
        LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessAtomicFact(ir)) => {
            (&ir.facts, &ir.inferred_facts)
        }
        LitexToLeanStatementIr::Command(LitexToLeanCommandStmtIr::DoNothingStmt(_)) => {
            return Some(Vec::new());
        }
        _ => return None,
    };
    Some(facts.iter().chain(inferred_facts.iter()).collect())
}

fn statement_label(statement: &LitexToLeanStatementIr) -> &'static str {
    match statement {
        LitexToLeanStatementIr::Fact(_) => "Fact",
        LitexToLeanStatementIr::UnsafeStmt(ir) => match ir {
            LitexToLeanUnsafeStmtIr::TrustStmt(_) => "TrustStmt",
            LitexToLeanUnsafeStmtIr::TrustHaveStmt(_) => "TrustHaveStmt",
        },
        LitexToLeanStatementIr::DefObjStmt(ir) => match ir {
            LitexToLeanDefObjStmtIr::LetObjStmt(_) => "LetObjStmt",
            LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(_) => "HaveObjInNonemptySetStmt",
            LitexToLeanDefObjStmtIr::HaveObjEqualStmt(_) => "HaveObjEqualStmt",
            LitexToLeanDefObjStmtIr::HaveObjByExistFactsStmt(_) => "HaveObjByExistFactsStmt",
            LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(_) => "ObtainObjFromExistFact",
            LitexToLeanDefObjStmtIr::ObtainObjFromAtomicFact(_) => "ObtainObjFromAtomicFact",
            LitexToLeanDefObjStmtIr::ObtainObjFromThm(_) => "ObtainObjFromThm",
            LitexToLeanDefObjStmtIr::HaveByPreimageStmt(_) => "HaveByPreimageStmt",
            LitexToLeanDefObjStmtIr::HaveFnEqualStmt(_) => "HaveFnEqualStmt",
            LitexToLeanDefObjStmtIr::HaveFnEqualCaseByCaseStmt(_) => "HaveFnEqualCaseByCaseStmt",
            LitexToLeanDefObjStmtIr::HaveFnByInducStmt(_) => "HaveFnByInducStmt",
            LitexToLeanDefObjStmtIr::HaveFnByForallExistUniqueStmt(_) => {
                "HaveFnByForallExistUniqueStmt"
            }
            LitexToLeanDefObjStmtIr::HaveTupleStmt(_) => "HaveTupleStmt",
            LitexToLeanDefObjStmtIr::HaveCartStmt(_) => "HaveCartStmt",
            LitexToLeanDefObjStmtIr::HaveSeqStmt(_) => "HaveSeqStmt",
            LitexToLeanDefObjStmtIr::HaveFiniteSeqStmt(_) => "HaveFiniteSeqStmt",
            LitexToLeanDefObjStmtIr::HaveMatrixStmt(_) => "HaveMatrixStmt",
        },
        LitexToLeanStatementIr::DefPredicateStmt(ir) => match ir {
            LitexToLeanDefPredicateStmtIr::DefPropStmt(_) => "DefPropStmt",
            LitexToLeanDefPredicateStmtIr::DefAbstractPropStmt(_) => "DefAbstractPropStmt",
        },
        LitexToLeanStatementIr::DefInterfaceStmt(ir) => match ir {
            LitexToLeanDefInterfaceStmtIr::DefSettingStmt(_) => "DefSettingStmt",
            LitexToLeanDefInterfaceStmtIr::DefTemplateStmt(_) => "DefTemplateStmt",
            LitexToLeanDefInterfaceStmtIr::DefStructStmt(_) => "DefStructStmt",
        },
        LitexToLeanStatementIr::DefAlgoStmt(_) => "DefAlgoStmt",
        LitexToLeanStatementIr::DefThmStmt(_) => "DefThmStmt",
        LitexToLeanStatementIr::DefStrategyStmt(_) => "DefStrategyStmt",
        LitexToLeanStatementIr::By(ir) => match ir {
            LitexToLeanByStmtIr::ByCasesStmt(_) => "ByCasesStmt",
            LitexToLeanByStmtIr::ByContraStmt(_) => "ByContraStmt",
            LitexToLeanByStmtIr::ByEnumerateFiniteSetStmt(_) => "ByEnumerateFiniteSetStmt",
            LitexToLeanByStmtIr::ByFiniteSetInducStmt(_) => "ByFiniteSetInducStmt",
            LitexToLeanByStmtIr::ByInducStmt(_) => "ByInducStmt",
            LitexToLeanByStmtIr::ByForStmt(_) => "ByForStmt",
            LitexToLeanByStmtIr::ByExtensionStmt(_) => "ByExtensionStmt",
            LitexToLeanByStmtIr::ByEnumerateRangeStmt(_) => "ByEnumerateRangeStmt",
            LitexToLeanByStmtIr::ByClosedRangeAsCasesStmt(_) => "ByClosedRangeAsCasesStmt",
            LitexToLeanByStmtIr::ByTransitivePropStmt(_) => "ByTransitivePropStmt",
            LitexToLeanByStmtIr::BySymmetricPropStmt(_) => "BySymmetricPropStmt",
            LitexToLeanByStmtIr::ByReflexivePropStmt(_) => "ByReflexivePropStmt",
            LitexToLeanByStmtIr::ByAntisymmetricPropStmt(_) => "ByAntisymmetricPropStmt",
            LitexToLeanByStmtIr::ByZornLemmaStmt(_) => "ByZornLemmaStmt",
            LitexToLeanByStmtIr::ByAxiomOfChoiceStmt(_) => "ByAxiomOfChoiceStmt",
            LitexToLeanByStmtIr::ByRegularityAxiomStmt(_) => "ByRegularityAxiomStmt",
            LitexToLeanByStmtIr::ByDefStmt(_) => "ByDefStmt",
            LitexToLeanByStmtIr::ByThmStmt(_) => "ByThmStmt",
        },
        LitexToLeanStatementIr::Witness(ir) => match ir {
            LitexToLeanWitnessStmtIr::WitnessExistFact(_) => "WitnessExistFact",
            LitexToLeanWitnessStmtIr::WitnessAtomicFact(_) => "WitnessAtomicFact",
            LitexToLeanWitnessStmtIr::WitnessNonemptySet(_) => "WitnessNonemptySet",
        },
        LitexToLeanStatementIr::ProofBlock(ir) => match ir {
            LitexToLeanProofBlockStmtIr::ClaimStmt(_) => "ClaimStmt",
            LitexToLeanProofBlockStmtIr::ExampleStmt(_) => "ExampleStmt",
            LitexToLeanProofBlockStmtIr::SketchStmt(_) => "SketchStmt",
            LitexToLeanProofBlockStmtIr::TryStmt(_) => "TryStmt",
        },
        LitexToLeanStatementIr::Command(ir) => match ir {
            LitexToLeanCommandStmtIr::ImportStmt(_) => "ImportStmt",
            LitexToLeanCommandStmtIr::DoNothingStmt(_) => "DoNothingStmt",
            LitexToLeanCommandStmtIr::ClearStmt(_) => "ClearStmt",
            LitexToLeanCommandStmtIr::EvalStmt(_) => "EvalStmt",
            LitexToLeanCommandStmtIr::UseStrategyStmt(_) => "UseStrategyStmt",
            LitexToLeanCommandStmtIr::StopStrategyStmt(_) => "StopStrategyStmt",
        },
    }
}

fn statement_line_file(statement: &LitexToLeanStatementIr) -> LineFile {
    match statement {
        LitexToLeanStatementIr::Fact(ir) => ir.source.proposition.line_file(),
        LitexToLeanStatementIr::UnsafeStmt(ir) => match ir {
            LitexToLeanUnsafeStmtIr::TrustStmt(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanUnsafeStmtIr::TrustHaveStmt(_) => unreachable_unemitted_statement_ir(),
        },
        LitexToLeanStatementIr::DefObjStmt(ir) => match ir {
            LitexToLeanDefObjStmtIr::LetObjStmt(ir) => ir.line_file.clone(),
            LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(ir) => ir
                .choices
                .first()
                .map(|choice| choice.membership.proposition.line_file())
                .unwrap_or_else(default_line_file),
            LitexToLeanDefObjStmtIr::HaveObjEqualStmt(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanDefObjStmtIr::HaveObjByExistFactsStmt(ir) => {
                ir.source.proposition.line_file()
            }
            LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(ir) => {
                ir.source.proposition.line_file()
            }
            LitexToLeanDefObjStmtIr::ObtainObjFromAtomicFact(ir) => {
                ir.source.proposition.line_file()
            }
            LitexToLeanDefObjStmtIr::HaveFnEqualStmt(ir) => ir.membership.proposition.line_file(),
            LitexToLeanDefObjStmtIr::HaveTupleStmt(ir) => ir
                .stored_facts
                .first()
                .map(|fact| fact.proposition.line_file())
                .unwrap_or_else(default_line_file),
            LitexToLeanDefObjStmtIr::ObtainObjFromThm(_)
            | LitexToLeanDefObjStmtIr::HaveByPreimageStmt(_)
            | LitexToLeanDefObjStmtIr::HaveFnEqualCaseByCaseStmt(_)
            | LitexToLeanDefObjStmtIr::HaveFnByInducStmt(_)
            | LitexToLeanDefObjStmtIr::HaveFnByForallExistUniqueStmt(_)
            | LitexToLeanDefObjStmtIr::HaveCartStmt(_)
            | LitexToLeanDefObjStmtIr::HaveSeqStmt(_)
            | LitexToLeanDefObjStmtIr::HaveFiniteSeqStmt(_)
            | LitexToLeanDefObjStmtIr::HaveMatrixStmt(_) => unreachable_unemitted_statement_ir(),
        },
        LitexToLeanStatementIr::DefPredicateStmt(_) => default_line_file(),
        LitexToLeanStatementIr::DefInterfaceStmt(ir) => match ir {
            LitexToLeanDefInterfaceStmtIr::DefSettingStmt(_)
            | LitexToLeanDefInterfaceStmtIr::DefTemplateStmt(_)
            | LitexToLeanDefInterfaceStmtIr::DefStructStmt(_) => {
                unreachable_unemitted_statement_ir()
            }
        },
        LitexToLeanStatementIr::DefAlgoStmt(_) | LitexToLeanStatementIr::DefStrategyStmt(_) => {
            unreachable_unemitted_statement_ir()
        }
        LitexToLeanStatementIr::DefThmStmt(ir) => ir.theorem.proposition.line_file(),
        LitexToLeanStatementIr::By(ir) => match ir {
            LitexToLeanByStmtIr::ByCasesStmt(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanByStmtIr::ByContraStmt(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanByStmtIr::ByDefStmt(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanByStmtIr::ByEnumerateFiniteSetStmt(_)
            | LitexToLeanByStmtIr::ByFiniteSetInducStmt(_)
            | LitexToLeanByStmtIr::ByInducStmt(_)
            | LitexToLeanByStmtIr::ByForStmt(_)
            | LitexToLeanByStmtIr::ByExtensionStmt(_)
            | LitexToLeanByStmtIr::ByEnumerateRangeStmt(_)
            | LitexToLeanByStmtIr::ByClosedRangeAsCasesStmt(_)
            | LitexToLeanByStmtIr::ByTransitivePropStmt(_)
            | LitexToLeanByStmtIr::BySymmetricPropStmt(_)
            | LitexToLeanByStmtIr::ByReflexivePropStmt(_)
            | LitexToLeanByStmtIr::ByAntisymmetricPropStmt(_)
            | LitexToLeanByStmtIr::ByZornLemmaStmt(_)
            | LitexToLeanByStmtIr::ByAxiomOfChoiceStmt(_)
            | LitexToLeanByStmtIr::ByRegularityAxiomStmt(_)
            | LitexToLeanByStmtIr::ByThmStmt(_) => unreachable_unemitted_statement_ir(),
        },
        LitexToLeanStatementIr::Witness(ir) => match ir {
            LitexToLeanWitnessStmtIr::WitnessExistFact(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanWitnessStmtIr::WitnessAtomicFact(ir) => first_fact_line_file(&ir.facts),
            LitexToLeanWitnessStmtIr::WitnessNonemptySet(_) => unreachable_unemitted_statement_ir(),
        },
        LitexToLeanStatementIr::ProofBlock(ir) => match ir {
            LitexToLeanProofBlockStmtIr::ClaimStmt(ir) => ir.line_file.clone(),
            LitexToLeanProofBlockStmtIr::ExampleStmt(ir) => ir.line_file.clone(),
            LitexToLeanProofBlockStmtIr::SketchStmt(ir) => ir.line_file.clone(),
            LitexToLeanProofBlockStmtIr::TryStmt(_) => unreachable_unemitted_statement_ir(),
        },
        LitexToLeanStatementIr::Command(ir) => match ir {
            LitexToLeanCommandStmtIr::DoNothingStmt(ir) => ir.line_file.clone(),
            LitexToLeanCommandStmtIr::ImportStmt(_)
            | LitexToLeanCommandStmtIr::ClearStmt(_)
            | LitexToLeanCommandStmtIr::EvalStmt(_)
            | LitexToLeanCommandStmtIr::UseStrategyStmt(_)
            | LitexToLeanCommandStmtIr::StopStrategyStmt(_) => unreachable_unemitted_statement_ir(),
        },
    }
}

fn first_fact_line_file(facts: &[LitexToLeanFactIr]) -> LineFile {
    facts
        .first()
        .map(|fact| fact.proposition.line_file())
        .unwrap_or_else(default_line_file)
}

fn universal_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        Vec::new(),
    ))
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_choice_predicate_uses_the_shared_core_definition() {
        let name = AtomicName::WithoutMod(IS_CHOICE_FUNCTION_FOR.to_string());
        assert_eq!(
            render_normal_predicate_name(&name),
            "Litex.IsChoiceFunctionFor"
        );
        assert_eq!(
            render_normal_predicate_name(&AtomicName::WithoutMod("marked".to_string())),
            "marked"
        );
    }

    #[test]
    fn universal_object_tracer_uses_membership_facts_without_retyping() {
        run_with_large_stack(|| {
            let source = r#"forall a C, f fn(x R) R:
    a = 1
    =>:
        1 $in R
        a $in R
        f(a) = f(a)
"#;
            let output = compile_to_lean_from_source(source, "universal-object-tracer.lit")
                .expect("the universal-object tracer should compile");
            assert!(output.starts_with("import Litex.Rules\n\n"), "{output}");
            assert!(!output.contains("Litex.abiVersion"), "{output}");
            assert!(!output.contains("import Mathlib"), "{output}");
            assert!(!output.contains("axiom Object : Type"), "{output}");
            assert!(!output.contains("LitexObject"), "{output}");
            assert!(
                output.contains("(a : Litex.Object)")
                    && output.contains("Litex.In a Litex.C")
                    && output.contains("Litex.In a Litex.R"),
                "{output}"
            );
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(output.contains("\n  have __wd0_"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(
                output.contains("\n  have __obj") && output.contains("_app :"),
                "{output}"
            );
            assert!(!output.contains("Set ℝ"), "{output}");
            assert!(!output.contains("(a : ℂ)"), "{output}");
            assert!(!output.contains("downcast"), "{output}");
        });
    }

    #[test]
    fn well_defined_object_dag_stays_inside_its_owning_forall_scope() {
        run_with_large_stack(|| {
            let output = compile_to_lean_from_source(
                scoped_nested_application_source(),
                "well-defined-object-scope.lit",
            )
            .expect("the scoped nested-application tracer should compile");

            assert_eq!(output.matches("\ntheorem __fact").count(), 1, "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("\ntheorem __obj"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(
                output.contains("Litex.fnSpace1 Litex.R Litex.R")
                    && output.contains("Litex.fnSpace2 Litex.R Litex.R Litex.R"),
                "{output}"
            );
            assert!(!output.contains("Litex.FnSpec"), "{output}");
            assert!(
                output.contains(
                    "theorem __fact43 :\n  ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R)\n    (b : Litex.Object) (__h0_2 : Litex.In b Litex.R)\n    (g : Litex.Object) (__h0_3 : Litex.In g (Litex.fnSpace1 Litex.R Litex.R))\n    (t : Litex.Object) (__h0_4 : Litex.In t (Litex.fnSpace1 Litex.R Litex.R))\n    (f : Litex.Object) (__h0_5 : Litex.In f (Litex.fnSpace2 Litex.R Litex.R Litex.R)),\n    (f [(g [a]), (t [b])]) = (f [(g [a]), (t [b])]) :="
                ),
                "{output}"
            );
            assert!(!output.contains("theorem __fact43 : ∀"), "{output}");

            let intro = output.find("\n  intro ").expect("forall intro");
            let inner_g_fact = output.find("\n  have __wd0_7").expect("g argument WD fact");
            let inner_g_applicable = output
                .find("\n  have __obj44_app")
                .expect("g application proof");
            let inner_g_result = output
                .find("\n  have __obj44_result")
                .expect("g result membership");
            let inner_t_fact = output.find("\n  have __wd0_8").expect("t argument WD fact");
            let inner_t_applicable = output
                .find("\n  have __obj45_app")
                .expect("t application proof");
            let inner_t_result = output
                .find("\n  have __obj45_result")
                .expect("t result membership");
            let outer_applicable = output
                .find("\n  have __obj46_app")
                .expect("outer application proof");
            let conclusion = output.rfind("\n  exact rfl").expect("source proof");
            assert!(
                intro < inner_g_fact
                    && inner_g_fact < inner_g_applicable
                    && inner_g_applicable < inner_g_result
                    && inner_g_result < inner_t_fact
                    && inner_t_fact < inner_t_applicable
                    && inner_t_applicable < inner_t_result
                    && inner_t_result < outer_applicable
                    && outer_applicable < conclusion,
                "{output}"
            );
            assert!(!output.contains("well_defined_fact_"), "{output}");
        });
    }

    #[test]
    fn ordinary_function_spaces_use_readable_specializations_and_generic_fallback() {
        run_with_large_stack(|| {
            let output = compile_to_lean_from_source(
                readable_function_spaces_source(),
                "readable-function-spaces.lit",
            )
            .expect("ordinary function spaces should compile");

            for expected in [
                "Litex.fnSpace1 Litex.R Litex.R",
                "Litex.fnSpace2 Litex.R Litex.C Litex.R",
                "Litex.fnSpace3 Litex.R Litex.C Litex.Z Litex.R",
                "Litex.fnSpace4 Litex.R Litex.C Litex.Z Litex.Q Litex.R",
                "Litex.fnSpace5 Litex.R Litex.C Litex.Z Litex.Q Litex.N Litex.R",
                "Litex.fnSpace [Litex.R, Litex.C, Litex.Z, Litex.Q, Litex.N, Litex.NPos] Litex.R",
            ] {
                assert!(output.contains(expected), "missing `{expected}`\n{output}");
            }
            assert!(!output.contains("Litex.FnSpec"), "{output}");
            assert!(!output.contains("litex_function_args"), "{output}");
            assert!(!output.contains("litex_function_length"), "{output}");
            assert!(!output.contains("litex_function_requirements"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn readable_function_spaces_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                readable_function_spaces_source(),
                "readable-function-spaces",
            );
            assert_source_compiles_with_mathlib(
                "forall f fn(x R: x > 0) R:\n    f = f\n",
                "dependent-function-space",
            );
        });
    }

    #[test]
    fn dependent_function_space_keeps_the_advanced_fn_spec_layer() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x R: x > 0) R:
    f = f
"#;
            let output = compile_to_lean_from_source(source, "dependent-function-space.lit")
                .expect("a function space with a domain condition should compile");

            assert!(output.contains("Litex.FnSet ({"), "{output}");
            assert!(output.contains(": Litex.FnSpec"), "{output}");
            assert!(output.contains("fun __arg_0"), "{output}");
            assert!(output.contains("∃ __h_arg0"), "{output}");
            assert!(
                output.contains("∃ __h_dom0 : Litex.Lt 0 (Litex.arg __arg_0 0)"),
                "{output}"
            );
        });
    }

    #[test]
    fn universal_object_application_does_not_invent_domain_membership() {
        run_with_large_stack(|| {
            let source = r#"forall a C, f fn(x R) R:
    f(a) = f(a)
"#;
            let error = compile_to_lean_from_source(source, "missing-domain-membership.lit")
                .expect_err("Litex verification must reject the undefined application");
            assert!(
                error.trace_message().contains("well-defined")
                    || error.trace_message().contains("not proved")
                    || error.trace_message().contains("cannot verify"),
                "unexpected rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn inferred_forall_premise_replays_its_exact_fact_id() {
        run_with_large_stack(|| {
            let source = "forall x R+:\n    x > 0\n";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "compile_to_lean_inferred_forall_premise.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse inferred-forall tracer");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse inferred-forall statement");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify inferred-forall tracer");
            let mut ir = vec![result
                .litex_to_lean_ir()
                .expect("inferred-forall tracer should retain To-Lean IR")
                .clone()];

            let LitexToLeanStatementIr::Fact(statement) = &ir[0] else {
                panic!("expected one factual tracer statement")
            };
            let LitexToLeanFactProofIr::ForallIntroduction {
                parameter_premises,
                inferred_premises,
                conclusions,
                ..
            } = &statement.source.proof
            else {
                panic!("expected forall-introduction evidence")
            };
            assert_eq!(parameter_premises.len(), 1);
            assert_eq!(inferred_premises.len(), 1);
            assert_eq!(conclusions.len(), 1);
            let inferred_fact_id = inferred_premises[0]
                .fact_id
                .expect("the inferred premise must retain its environment FactId");
            let LitexToLeanFactProofIr::RuleApplication {
                rule,
                parameter_requirements,
                premises,
            } = &inferred_premises[0].proof
            else {
                panic!("expected checked inferred-premise rule evidence")
            };
            assert!(matches!(
                rule,
                LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::PositiveRealMembership)
            ));
            assert!(parameter_requirements.is_empty());
            assert_eq!(premises.len(), 1);
            assert_eq!(premises[0].fact_id, Some(parameter_premises[0].fact_id));

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("the exact inferred-forall tracer should emit Lean");
            assert!(
                output.contains("have __inferred0 : Litex.Lt 0 x :="),
                "{output}"
            );
            assert!(
                output.contains("Litex.Rules.positiveRealMembership __h0_1"),
                "{output}"
            );
            assert!(
                !output.contains("litex_h_") && !output.contains("litex_param_fact_"),
                "{output}"
            );
            assert!(output.contains("exact __inferred0"), "{output}");
            assert!(!output.contains("assumption"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                unreachable!("checked factual tracer statement")
            };
            let LitexToLeanFactProofIr::ForallIntroduction {
                inferred_premises, ..
            } = &mut statement.source.proof
            else {
                unreachable!("checked forall-introduction evidence")
            };
            let LitexToLeanFactProofIr::RuleApplication { premises, .. } =
                &mut inferred_premises[0].proof
            else {
                unreachable!("checked inferred-premise rule evidence")
            };
            let unavailable = FactId::new(u64::MAX);
            premises[0].fact_id = Some(unavailable);
            premises[0].proof = LitexToLeanFactProofIr::KnownFactCitation {
                source_fact_id: unavailable,
            };
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("an unavailable inferred-premise source FactId must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("no emitted Lean proof is registered for source FactId"),
                "unexpected strict rejection for inferred FactId {inferred_fact_id}: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn unsupported_inferred_forall_premise_remains_rejected() {
        run_with_large_stack(|| {
            let error = compile_to_lean_from_source(
                "forall x N+:\n    x > 0\n",
                "unsupported-inferred-forall-premise.lit",
            )
            .expect_err("unsupported verifier inference must not become target-side search");
            assert!(
                error
                    .trace_message()
                    .contains("no checked Litex-to-Lean proof adapter")
                    || error
                        .trace_message()
                        .contains("no emitted Lean proof is registered for source FactId"),
                "unexpected unsupported-inference rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn inferred_forall_premise_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                "forall x R+:\n    x > 0\n",
                "inferred-forall-premise",
            );
        });
    }

    #[test]
    fn object_choice_emits_one_definition_and_exact_membership_fact() {
        run_with_large_stack(|| {
            let source = "have x R\nx $in R\n";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("compile_to_lean_object_choice.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse object-choice tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify object-choice tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("object-choice statement should retain To-Lean IR")
                        .clone(),
                );
            }
            assert_eq!(ir.len(), 2, "{ir:#?}");
            let LitexToLeanStatementIr::DefObjStmt(
                LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(choice),
            ) = &ir[0]
            else {
                panic!("expected object-choice statement IR")
            };
            assert_eq!(choice.choices.len(), 1);
            let membership_fact_id = choice.choices[0]
                .membership
                .fact_id
                .expect("object choice must retain its stored membership FactId");

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("the exact object-choice tracer should emit Lean");
            assert!(
                output.contains("noncomputable def x : Litex.Object := Classical.choose"),
                "{output}"
            );
            assert!(
                output.contains(&format!(
                    "theorem __fact{} : Litex.In x Litex.R :=",
                    membership_fact_id.value()
                )),
                "{output}"
            );
            assert!(output.contains("Classical.choose_spec"), "{output}");
            assert_eq!(
                output
                    .matches(&format!("theorem __fact{}", membership_fact_id.value()))
                    .count(),
                1,
                "the explicit membership statement must reuse the choice FactId\n{output}"
            );
            assert!(!output.contains("axiom x"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let LitexToLeanStatementIr::DefObjStmt(
                LitexToLeanDefObjStmtIr::HaveObjInNonemptySetStmt(choice),
            ) = &mut ir[0]
            else {
                unreachable!("checked object-choice statement IR")
            };
            let LitexToLeanFactProofIr::ObjectChoice { definition, .. } =
                &mut choice.choices[0].membership.proof
            else {
                panic!("expected object-choice membership proof")
            };
            *definition = "changed_x".to_string();
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("changed object-choice definition evidence must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("object-choice membership changed its definition or carrier"),
                "unexpected malformed object-choice rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn meta_level_object_choice_remains_rejected() {
        run_with_large_stack(|| {
            let error = compile_to_lean_from_source("have s set\n", "meta-object-choice.lit")
                .expect_err("meta-level choice has no checked inhabited-object backend");
            assert!(
                error
                    .trace_message()
                    .contains("no checked inhabited-type backend"),
                "unexpected meta-choice rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn object_choice_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib("have x R\nx $in R\n", "object-choice");
        });
    }

    #[test]
    fn existential_intro_and_elim_replay_exact_projection_roles() {
        run_with_large_stack(|| {
            let source = r#"witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
y = 1
"#;
            let mut runtime = Runtime::new();
            runtime
                .new_file_path_new_env_new_name_scope("compile_to_lean_existential_intro_elim.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse existential tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify existential tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("existential statement should retain To-Lean IR")
                        .clone(),
                );
            }
            assert_eq!(ir.len(), 3, "{ir:#?}");
            let LitexToLeanStatementIr::Witness(LitexToLeanWitnessStmtIr::WitnessExistFact(
                introduction,
            )) = &mut ir[0]
            else {
                panic!("expected existential introduction proof IR")
            };
            assert_eq!(introduction.facts.len(), 1);
            let existential_fact_id = introduction.facts[0]
                .fact_id
                .expect("introduced existential must retain a FactId");
            let LitexToLeanStatementIr::DefObjStmt(
                LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(elimination),
            ) = &ir[1]
            else {
                panic!("expected existential elimination IR")
            };
            assert_eq!(elimination.witnesses.len(), 1);
            assert_eq!(elimination.projections.len(), 2);
            let projection_ids = elimination
                .projections
                .iter()
                .map(|projection| {
                    projection
                        .fact_id
                        .expect("existential projection must retain a FactId")
                })
                .collect::<Vec<_>>();

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("the exact existential tracer should emit Lean");
            assert!(
                output.contains(&format!(
                    "theorem __fact{} : ∃ (x : Litex.Object),",
                    existential_fact_id.value()
                )),
                "{output}"
            );
            assert!(
                output.contains("noncomputable def y : Litex.Object := Classical.choose"),
                "{output}"
            );
            assert!(output.contains("Classical.choose_spec"), "{output}");
            for projection_id in projection_ids {
                assert_eq!(
                    output
                        .matches(&format!("theorem __fact{}", projection_id.value()))
                        .count(),
                    1,
                    "each existential projection FactId must emit once\n{output}"
                );
            }
            assert!(!output.contains("axiom __fact"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let LitexToLeanStatementIr::DefObjStmt(
                LitexToLeanDefObjStmtIr::ObtainObjFromExistFact(elimination),
            ) = &mut ir[1]
            else {
                unreachable!("checked existential elimination IR")
            };
            let LitexToLeanFactProofIr::ExistentialElimination { role, .. } =
                &mut elimination.projections[0].proof
            else {
                panic!("expected existential projection proof")
            };
            *role = LitexToLeanExistentialProjectionRoleIr::BodyFact { body_index: 0 };
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("duplicated existential projection roles must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("existential projection does not match its witness role")
                    || error
                        .trace_message()
                        .contains("did not retain both projection roles"),
                "unexpected existential projection rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn existential_intro_and_elim_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
y = 1
"#,
                "existential-intro-elim",
            );
        });
    }

    #[test]
    fn example_and_sketch_compile_to_scoped_lean_examples() {
        run_with_large_stack(|| {
            let source =
                include_str!("../../lean/examples/cases/compile_to_lean_example_and_sketch.lit");
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("compile_to_lean_example_and_sketch.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse example-and-sketch tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify example-and-sketch tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("proof block should retain To-Lean IR")
                        .clone(),
                );
            }
            assert_eq!(ir.len(), 3, "{ir:#?}");
            let LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ExampleStmt(
                first_example,
            )) = &ir[0]
            else {
                panic!("expected example proof-block IR")
            };
            assert!(first_example.target.fact_id.is_none());
            assert_eq!(first_example.block.steps.len(), 1);
            let LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ExampleStmt(
                forall_example,
            )) = &ir[1]
            else {
                panic!("expected forall example proof-block IR")
            };
            assert!(matches!(
                forall_example.target.proposition,
                Fact::ForallFact(_)
            ));
            let LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::SketchStmt(sketch)) =
                &ir[2]
            else {
                panic!("expected sketch proof-block IR")
            };
            assert_eq!(sketch.block.steps.len(), 1);

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("example-and-sketch tracer should emit Lean");
            assert_eq!(output.matches("\nexample :").count(), 2, "{output}");
            assert!(output.contains("namespace __Sketch01"), "{output}");
            assert!(output.contains("theorem __fact"), "{output}");
            assert!(output.contains("have __step_1 :"), "{output}");
            assert!(output.contains("\n  intro "), "{output}");
            assert!(output.contains("(__h0_1 : Litex.In x Litex.R)"), "{output}");
            assert!(!output.contains("__h1_1"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let mut malformed = ir.clone();
            let LitexToLeanStatementIr::ProofBlock(LitexToLeanProofBlockStmtIr::ExampleStmt(
                example,
            )) = &mut malformed[0]
            else {
                unreachable!("checked first example IR")
            };
            example.target.fact_id = Some(FactId::new(u64::MAX));
            let error = emit_lean_from_litex_to_lean_ir(&malformed)
                .expect_err("an exported example target FactId must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("example` target must not retain an exported FactId"),
                "unexpected malformed-example rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn declaration_bearing_sketch_uses_an_isolated_namespace() {
        run_with_large_stack(|| {
            let output = compile_to_lean_from_source(
                "sketch:\n    trust 1 = 1\n    1 = 1\n",
                "sketch-local-trust.lit",
            )
            .expect("an explicit local trust should compile inside an isolated namespace");
            assert!(output.contains("namespace __Sketch01"), "{output}");
            assert!(output.contains("axiom __fact"), "{output}");
            assert!(output.contains("end __Sketch01"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn example_and_sketch_compile_with_mathlib() {
        run_with_large_stack(|| {
            let source =
                include_str!("../../lean/examples/cases/compile_to_lean_example_and_sketch.lit");
            assert_source_compiles_with_mathlib(source, "example-and-sketch");
        });
    }

    #[test]
    fn case_and_contradiction_scopes_replay_local_fact_ids() {
        run_with_large_stack(|| {
            let source = r#"by cases:
    ? 1 = 1
    case 1 = 1:
        2 = 2
by contra:
    ? 2 = 2
    1 = 1
    impossible 2 != 2
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "compile_to_lean_case_and_contradiction_scopes.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse case-and-contradiction tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify case-and-contradiction tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("scope statement should retain To-Lean IR")
                        .clone(),
                );
            }
            assert_eq!(ir.len(), 2, "{ir:#?}");
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(cases)) = &ir[0] else {
                panic!("expected by-cases proof IR")
            };
            let LitexToLeanFactProofIr::CaseSplit { branches, .. } = &cases.facts[0].proof else {
                panic!("expected case-split proof IR")
            };
            assert_eq!(branches[0].block.steps.len(), 1);
            let branch_step_fact_id = statement_proof_facts(&branches[0].block.steps[0])
                .expect("case body should retain a local factual statement")[0]
                .fact_id
                .expect("case body fact should retain its temporary FactId");
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(contra)) = &ir[1]
            else {
                panic!("expected by-contra proof IR")
            };
            let LitexToLeanFactProofIr::ByContradiction { block, .. } = &contra.facts[0].proof
            else {
                panic!("expected by-contradiction proof IR")
            };
            assert_eq!(block.steps.len(), 1);
            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("the exact scope tracer should emit Lean");
            assert!(output.contains("have __case1 :"), "{output}");
            assert!(output.contains("have __case1_step_1 :"), "{output}");
            assert!(output.contains("exact __case1"), "{output}");
            assert!(output.contains("by_contra __reverse"), "{output}");
            assert!(output.contains("__reverse"), "{output}");
            assert!(output.contains("have __contra_step_1 :"), "{output}");
            assert!(
                !output.contains(&format!("theorem __fact{}", branch_step_fact_id.value())),
                "a branch-local FactId leaked into a top-level declaration:\n{output}"
            );
            assert!(!output.contains("\n  assumption"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let mut leaked_citation_ir = ir.clone();
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(contra)) =
                &mut leaked_citation_ir[1]
            else {
                unreachable!("checked by-contra statement")
            };
            let LitexToLeanFactProofIr::ByContradiction { block, .. } = &mut contra.facts[0].proof
            else {
                unreachable!("checked by-contradiction proof")
            };
            let LitexToLeanStatementIr::Fact(local_fact) = &mut block.steps[0] else {
                unreachable!("checked local fact statement")
            };
            local_fact.source.proof = LitexToLeanFactProofIr::KnownFactCitation {
                source_fact_id: branch_step_fact_id,
            };
            let error = emit_lean_from_litex_to_lean_ir(&leaked_citation_ir)
                .expect_err("a sibling branch FactId must be unavailable in by-contra");
            assert!(
                error
                    .trace_message()
                    .contains("no emitted Lean proof is registered for source FactId"),
                "unexpected sibling-scope rejection: {}",
                error.trace_message()
            );

            let mut malformed_wd_ir = ir.clone();
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(cases)) =
                &mut malformed_wd_ir[0]
            else {
                unreachable!("checked by-cases statement")
            };
            let LitexToLeanFactProofIr::CaseSplit { branches, .. } = &mut cases.facts[0].proof
            else {
                unreachable!("checked case-split proof")
            };
            branches[0]
                .block
                .well_definedness
                .root_obj_ids
                .push(WellDefinedObjId::new(u64::MAX));
            let error = emit_lean_from_litex_to_lean_ir(&malformed_wd_ir)
                .expect_err("a branch WD root without an object record must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("has no frozen object record"),
                "unexpected malformed branch WD rejection: {}",
                error.trace_message()
            );

            let wrong_assumption = match &ir[1] {
                LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(contra)) => {
                    match &contra.facts[0].proof {
                        LitexToLeanFactProofIr::ByContradiction {
                            reverse_assumption, ..
                        } => reverse_assumption.premise.fact.clone(),
                        _ => unreachable!("checked by-contradiction proof"),
                    }
                }
                _ => unreachable!("checked by-contra statement"),
            };
            let mut wrong_slot_ir = ir.clone();
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(cases)) =
                &mut wrong_slot_ir[0]
            else {
                unreachable!("checked by-cases proof IR")
            };
            let LitexToLeanFactProofIr::CaseSplit { branches, .. } = &mut cases.facts[0].proof
            else {
                unreachable!("checked case-split proof")
            };
            branches[0].assumption.fact = wrong_assumption;
            let error = emit_lean_from_litex_to_lean_ir(&wrong_slot_ir)
                .expect_err("a case assumption in the wrong coverage slot must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("case branch assumption does not match its coverage position"),
                "unexpected malformed case rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn case_conjunction_and_negative_contra_replay_structured_scope_evidence() {
        run_with_large_stack(|| {
            let source = r#"by cases:
    ? 2 = 2
    case 1 = 1 and 2 = 2:
        1 = 1
by contra:
    ? 1 != 2
    impossible 1 = 2
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "compile_to_lean_structured_case_and_negative_contra.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse structured proof-scope tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify structured proof-scope tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("structured proof scope should retain To-Lean IR")
                        .clone(),
                );
            }

            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(cases)) = &ir[0] else {
                panic!("expected by-cases proof IR")
            };
            let LitexToLeanFactProofIr::CaseSplit { branches, .. } = &cases.facts[0].proof else {
                panic!("expected case-split proof IR")
            };
            assert_eq!(branches[0].block.assumption_inferred_facts.len(), 2);
            for (index, inferred) in branches[0]
                .block
                .assumption_inferred_facts
                .iter()
                .enumerate()
            {
                assert!(matches!(
                    inferred.proof,
                    LitexToLeanFactProofIr::RuleApplication {
                        rule: LitexToLeanProofRuleIr::ConjunctionProjection {
                            index: retained_index,
                            count: 2,
                            ..
                        },
                        ..
                    } if retained_index == index
                ));
            }

            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(contra)) = &ir[1]
            else {
                panic!("expected by-contra proof IR")
            };
            assert!(matches!(
                contra.facts[0].proof,
                LitexToLeanFactProofIr::ByContradiction {
                    reverse_assumption: LitexToLeanReverseAssumptionIr {
                        introduction:
                            LitexToLeanReverseAssumptionIntroductionIr::ClassicalDoubleNegation,
                        ..
                    },
                    ..
                }
            ));

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("structured local proof scopes should emit Lean");
            assert!(output.contains("have __case1_step_1 :"), "{output}");
            assert!(output.contains("have __case1_step_2 :"), "{output}");
            assert!(output.contains("Classical.byContradiction"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let mut malformed_projection_ir = ir.clone();
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(cases)) =
                &mut malformed_projection_ir[0]
            else {
                unreachable!("checked by-cases proof IR")
            };
            let LitexToLeanFactProofIr::CaseSplit { branches, .. } = &mut cases.facts[0].proof
            else {
                unreachable!("checked case-split proof")
            };
            let LitexToLeanFactProofIr::RuleApplication {
                rule: LitexToLeanProofRuleIr::ConjunctionProjection { index, .. },
                ..
            } = &mut branches[0].block.assumption_inferred_facts[0].proof
            else {
                unreachable!("checked conjunction projection")
            };
            *index = 1;
            let error = emit_lean_from_litex_to_lean_ir(&malformed_projection_ir)
                .expect_err("a retargeted conjunction projection must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("changed its retained component position"),
                "unexpected malformed conjunction rejection: {}",
                error.trace_message()
            );

            let mut malformed_polarity_ir = ir.clone();
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(contra)) =
                &mut malformed_polarity_ir[1]
            else {
                unreachable!("checked by-contra proof IR")
            };
            let LitexToLeanFactProofIr::ByContradiction {
                reverse_assumption, ..
            } = &mut contra.facts[0].proof
            else {
                unreachable!("checked by-contradiction proof")
            };
            reverse_assumption.introduction =
                LitexToLeanReverseAssumptionIntroductionIr::DirectNegation;
            let error = emit_lean_from_litex_to_lean_ir(&malformed_polarity_ir)
                .expect_err("a retargeted reverse-assumption bridge must fail closed");
            assert!(
                error.trace_message().contains("changed target polarity"),
                "unexpected malformed polarity rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn nested_case_and_contra_keep_branch_wd_and_statement_scopes_local() {
        run_with_large_stack(|| {
            let source = r#"have fn identity(x R) R = x
by cases:
    ? identity(1) = identity(1)
    case 1 = 1:
        by contra:
            ? 2 = 2
            impossible 2 != 2
        1 $in R
by contra:
    ? 3 = 3
    by cases:
        ? 4 = 4
        case 4 = 4:
            5 = 5
    impossible 3 != 3
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "compile_to_lean_nested_case_contra_branch_wd.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse nested proof-scope tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify nested proof-scope tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("nested proof scope should retain To-Lean IR")
                        .clone(),
                );
            }

            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(cases)) = &ir[1] else {
                panic!("expected outer by-cases proof IR")
            };
            assert!(!cases.well_definedness.root_obj_ids.is_empty());
            let LitexToLeanFactProofIr::CaseSplit { branches, .. } = &cases.facts[0].proof else {
                panic!("expected outer case-split proof IR")
            };
            assert_eq!(branches[0].block.steps.len(), 2);
            assert!(
                !branches[0].block.well_definedness.root_obj_ids.is_empty(),
                "the branch must own its proof-phase identity(1) WD replay"
            );
            let nested_fact_ids = branches[0]
                .block
                .steps
                .iter()
                .flat_map(statement_proof_facts)
                .flatten()
                .filter_map(|fact| fact.fact_id)
                .collect::<Vec<_>>();

            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByContraStmt(contra)) = &ir[2]
            else {
                panic!("expected outer by-contra proof IR")
            };
            let LitexToLeanFactProofIr::ByContradiction { block, .. } = &contra.facts[0].proof
            else {
                panic!("expected outer contradiction proof IR")
            };
            assert_eq!(block.steps.len(), 1);
            assert!(matches!(
                block.steps[0],
                LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByCasesStmt(_))
            ));

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("nested cases/contra with branch WD should emit Lean");
            assert!(output.matches("by_contra __reverse").count() >= 2);
            assert!(
                output.contains("Litex.Applicable (identity) [1]"),
                "{output}"
            );
            for fact_id in nested_fact_ids {
                assert!(
                    !output.contains(&format!("theorem __fact{}", fact_id.value())),
                    "nested FactId leaked to the top level:\n{output}"
                );
            }
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn nested_case_and_contra_branch_wd_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"have fn identity(x R) R = x
by cases:
    ? identity(1) = identity(1)
    case 1 = 1:
        by contra:
            ? 2 = 2
            impossible 2 != 2
        1 $in R
by contra:
    ? 3 = 3
    by cases:
        ? 4 = 4
        case 4 = 4:
            5 = 5
    impossible 3 != 3
"#,
                "nested-case-contra-branch-wd",
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn case_and_contradiction_scopes_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                include_str!(
                    "../../lean/examples/cases/compile_to_lean_case_and_contradiction_scopes.lit"
                ),
                "case-and-contradiction-scopes",
            );
        });
    }

    #[test]
    fn named_theorem_emits_its_source_name_and_fact_id_binding() {
        run_with_large_stack(|| {
            let source = r#"thm one_eq_one:
    ? forall:
        1 = 1
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("compile_to_lean_named_theorem.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse named-theorem tracer");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse named theorem");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify named-theorem tracer");
            let mut ir = vec![result
                .litex_to_lean_ir()
                .expect("named theorem should retain To-Lean IR")
                .clone()];
            let LitexToLeanStatementIr::DefThmStmt(theorem) = &ir[0] else {
                panic!("expected named-theorem statement IR")
            };
            assert_eq!(theorem.name, "one_eq_one");
            assert_eq!(theorem.expected_proof_step_count, 0);
            assert!(theorem.proof_steps.is_empty());
            let fact_id = theorem
                .theorem
                .fact_id
                .expect("complete named theorem must retain its FactId");

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("the exact named-theorem tracer should emit Lean");
            assert!(output.contains("theorem one_eq_one :"), "{output}");
            assert!(output.contains("exact rfl"), "{output}");
            assert!(
                !output.contains(&format!("theorem __fact{}", fact_id.value())),
                "the complete theorem must use its source name once\n{output}"
            );
            assert!(!output.contains("axiom one_eq_one"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let LitexToLeanStatementIr::DefThmStmt(theorem) = &mut ir[0] else {
                unreachable!("checked named-theorem statement IR")
            };
            theorem.expected_proof_step_count = 1;
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("changed named-theorem proof-step count must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("proof steps changed their retained source order"),
                "unexpected malformed named-theorem rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn total_object_constructors_render_without_proof_arguments() {
        run_with_large_stack(|| {
            let source = r#"pi = pi
forall A, B set:
    union(A, B) = union(A, B)
"#;
            let output = compile_to_lean_from_source(source, "total-object-constructors.lit")
                .expect("pi and union should render as total object constructors");
            assert!(output.contains("Litex.pi"), "{output}");
            assert!(output.contains("Litex.union"), "{output}");
            assert!(!output.contains("Litex.union A B "), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let malformed = LitexToLeanObjectIr::BuiltinApp {
                source_occurrence_id: None,
                semantic_key: "malformed-union".to_string(),
                operator: LitexToLeanBuiltinObjectOperatorIr::Union,
                arguments: vec![LitexToLeanObjectIr::Constant(
                    LitexToLeanConstantObjectIr::Pi,
                )],
            };
            let error = UniversalEmitter::new()
                .render_obj_ir(&malformed, &RenderContext::default())
                .expect_err("a changed total-constructor arity must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("retained 1 arguments instead of two"),
                "unexpected malformed total-constructor rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn simple_statements_and_native_constants_emit_checked_lean() {
        run_with_large_stack(|| {
            let source = include_str!(
                "../../lean/examples/cases/compile_to_lean_simple_statements_and_constants.lit"
            );
            let output = compile_to_lean_from_source(
                source,
                "compile_to_lean_simple_statements_and_constants.lit",
            )
            .expect("verified simple statements and native constants should compile");
            assert!(
                output.contains("noncomputable def x : Litex.Object := 1"),
                "{output}"
            );
            assert!(output.contains("Litex.e = Litex.e"), "{output}");
            assert!(output.contains("Litex.i = Litex.i"), "{output}");
            assert!(
                output.contains("Litex.Rules.eInR")
                    && output.contains("Litex.Rules.imaginaryUnitInC"),
                "{output}"
            );
            assert!(!output.contains("do_nothing"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let repeated_claim = compile_to_lean_from_source(
                "let y = 1\nclaim:\n    ? y = 1\n    y = 1\n",
                "compile_to_lean_repeated_claim_fact.lit",
            )
            .expect("a claim may reuse an already assigned environment FactId");
            assert!(
                repeated_claim.contains("noncomputable def y : Litex.Object := 1"),
                "{repeated_claim}"
            );
        });
    }

    #[test]
    fn forall_claim_remains_an_explicit_boundary() {
        run_with_large_stack(|| {
            let error = compile_to_lean_from_source(
                "claim:\n    ? forall:\n        1 = 1\n    1 = 1\n",
                "compile_to_lean_forall_claim_boundary.lit",
            )
            .expect_err("forall claims are outside this simple statement tranche");
            assert!(
                error
                    .trace_message()
                    .contains("supports ordinary fact goals, not `forall` goals"),
                "unexpected forall-claim boundary: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn total_object_constructors_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"pi = pi
forall A, B set:
    union(A, B) = union(A, B)
"#,
                "total-object-constructors",
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn simple_statements_and_native_constants_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                include_str!(
                    "../../lean/examples/cases/compile_to_lean_simple_statements_and_constants.lit"
                ),
                "simple-statements-and-native-constants",
            );
        });
    }

    #[test]
    fn set_builder_scope_uses_a_nonleaking_symbol_id_binder() {
        run_with_large_stack(|| {
            let source = r#"have S set = {x R: x = x}
S = S
"#;
            let output = compile_to_lean_from_source(source, "set-builder-scope.lit")
                .expect("a set-builder definition should compile with a local binder");
            assert!(output.contains("Litex.setBuilder Litex.R"), "{output}");
            assert!(output.contains("fun __x"), "{output}");
            assert!(output.contains("Litex.Rules.objectIsSet"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("set-builder-scope-malformed.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse set-builder scope tracer");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse set-builder definition");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify set-builder definition");
            let mut ir = vec![result
                .litex_to_lean_ir()
                .expect("set-builder definition should retain To-Lean IR")
                .clone()];
            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjEqualStmt(
                definition,
            )) = &mut ir[0]
            else {
                panic!("expected have-object statement IR")
            };
            let LitexToLeanObjectIr::SetBuilder(set_builder) = &mut definition.definitions[0].value
            else {
                panic!("expected an explicit set-builder object IR")
            };
            set_builder.symbol_id = SymbolId::new(u64::MAX);
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a changed set-builder binder identity must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("have-object equality facts do not match the retained definition")
                    || error
                        .trace_message()
                        .contains("changed its definition, value, or required type"),
                "unexpected malformed set-builder rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn set_builder_replays_ordered_local_condition_wd_inside_definition_theorem() {
        run_with_large_stack(|| {
            let source = "have S set = {x R: x != 0, 1 / x > 0}\nS = S\n";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("set-builder-ordered-local-wd.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse ordered set-builder WD tracer");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse set-builder definition");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify ordered set-builder WD tracer");
            let mut ir = vec![result
                .litex_to_lean_ir()
                .expect("set-builder definition should retain To-Lean IR")
                .clone()];
            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjEqualStmt(
                definition,
            )) = &ir[0]
            else {
                panic!("expected have-object statement IR")
            };
            let scope = definition
                .well_definedness
                .binder_scopes
                .iter()
                .find(|scope| matches!(scope.owner_object, Obj::SetBuilder(_)))
                .expect("set builder must own a frozen local scope");
            assert_eq!(scope.premises.len(), 3);
            assert_eq!(
                scope
                    .premises
                    .iter()
                    .map(|premise| premise.role)
                    .collect::<Vec<_>>(),
                vec![
                    WellDefinedBinderPremiseRole::ParameterMembership {
                        parameter_group_index: 0,
                        parameter_index: 0,
                    },
                    WellDefinedBinderPremiseRole::LocalCondition { condition_index: 0 },
                    WellDefinedBinderPremiseRole::LocalCondition { condition_index: 1 },
                ]
            );

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("ordered set-builder WD should emit Lean");
            assert!(output.contains("have __set_builder_scope"), "{output}");
            assert!(output.contains("Litex.Rules.realDivClosure"), "{output}");
            assert!(output.contains("__wd_scope1_premise2"), "{output}");
            assert!(
                output.contains("noncomputable def S : Litex.Object := (Litex.setBuilder Litex.R"),
                "{output}"
            );
            assert!(!output.contains("sorry"), "{output}");

            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjEqualStmt(
                definition,
            )) = &mut ir[0]
            else {
                unreachable!("checked have-object statement IR")
            };
            let scope = definition
                .well_definedness
                .binder_scopes
                .iter_mut()
                .find(|scope| matches!(scope.owner_object, Obj::SetBuilder(_)))
                .expect("set-builder scope");
            scope.premises.swap(1, 2);
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("reordered set-builder conditions must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("changed binder premise order"),
                "unexpected reordered condition rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn set_builder_scope_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"have S set = {x R: x = x}
S = S
"#,
                "set-builder-scope",
            );
        });
    }

    #[test]
    fn named_function_emits_checked_constructor_and_definition_reduction() {
        run_with_large_stack(|| {
            let source = r#"have fn id(x R) R = x
id(1) = 1
"#;
            let output = compile_to_lean_from_source(source, "named-function.lit")
                .expect("a named identity function should compile end to end");
            assert!(
                output.contains("def __litex_id_spec : Litex.FnSpec"),
                "{output}"
            );
            assert!(output.contains("def __litex_id_body"), "{output}");
            assert!(output.contains("theorem __litex_id_closed"), "{output}");
            assert!(
                output.contains("Litex.functionObject __litex_id_spec __litex_id_body"),
                "{output}"
            );
            assert!(
                !output.contains(
                    "Litex.functionObject __litex_id_spec __litex_id_body __litex_id_closed"
                ),
                "{output}"
            );
            assert!(output.contains("Litex.functionObjectInFnSet"), "{output}");
            assert!(output.contains("_app"), "{output}");
            assert!(output.contains("_result"), "{output}");
            assert!(
                output.contains("∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True"),
                "{output}"
            );
            assert!(output.contains("Exists.choose (__fn_arg_req)"), "{output}");
            assert!(output.contains("List.getD_cons_zero"), "{output}");
            assert!(!output.contains("axiom litex_id"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("named-function-malformed.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse named-function tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify named-function tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("named-function statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(application_fact) = &mut ir[1] else {
                panic!("expected application equality fact IR")
            };
            let proof = match &mut application_fact.source.proof {
                LitexToLeanFactProofIr::Memo { proof } => proof.as_mut(),
                proof => proof,
            };
            let LitexToLeanFactProofIr::RuleApplication { rule, .. } = proof else {
                panic!("expected checked function reduction proof: {proof:#?}")
            };
            let LitexToLeanProofRuleIr::CheckedFunctionDefinitionReduction {
                defining_equality_fact_id,
                ..
            } = rule
            else {
                panic!("expected checked function definition reduction")
            };
            *defining_equality_fact_id = FactId::new(u64::MAX);
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("an unavailable defining equality FactId must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("cites unavailable defining FactId"),
                "unexpected malformed named-function rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn named_function_replays_compound_body_wd_inside_its_closed_proof() {
        run_with_large_stack(|| {
            let source = r#"have fn inc(x R) R = x + 1
inc(1) = 1 + 1
"#;
            let output = compile_to_lean_from_source(source, "named-function-compound-body.lit")
                .expect("a named function must replay its arithmetic body WD locally");
            assert!(output.contains("\n  have __wd0_"), "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(output.contains("Litex.add"), "{output}");
            assert!(output.contains("Litex.functionObject_apply"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn named_function_replays_domain_evidence_in_partial_body() {
        run_with_large_stack(|| {
            let source = r#"have fn reciprocal(x R: x != 0) R = 1 / x
forall a R:
    a != 0
    =>:
        reciprocal(a) = 1 / a
"#;
            let output = compile_to_lean_from_source(source, "named-function-partial-body.lit")
                .expect("a named function must pass its retained domain proof to division");
            assert!(output.contains("Litex.div"), "{output}");
            assert!(output.contains("\n  have __wd0_"), "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(output.contains("__fn_arg_req"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn named_function_wd_evidence_fails_closed_when_malformed() {
        run_with_large_stack(|| {
            let source = "have fn inc(x R) R = x + 1";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("named-function-malformed-wd.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse named-function malformed WD tracer");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse named-function definition");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify named-function definition");
            let original = result
                .litex_to_lean_ir()
                .expect("named-function definition should retain To-Lean IR")
                .clone();

            let mut missing_occurrence = vec![original.clone()];
            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveFnEqualStmt(
                function,
            )) = &mut missing_occurrence[0]
            else {
                panic!("expected named-function definition IR")
            };
            let LitexToLeanObjectIr::BuiltinApp {
                source_occurrence_id: Some(body_occurrence_id),
                ..
            } = function.body
            else {
                panic!("expected proof-carrying arithmetic function body")
            };
            function
                .well_definedness
                .source_object_uses
                .retain(|source_use| source_use.source_occurrence_id != body_occurrence_id);
            let error = emit_lean_from_litex_to_lean_ir(&missing_occurrence)
                .expect_err("a named body without its exact source occurrence must fail closed");
            assert!(
                error.trace_message().contains("exact WD object uses")
                    || error.trace_message().contains("no exact WellDefinedObjId"),
                "unexpected missing named-body occurrence rejection: {}",
                error.trace_message()
            );

            let reciprocal_source = "have fn reciprocal(x R: x != 0) R = 1 / x";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("named-function-missing-domain.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(reciprocal_source, runtime.current_file_path_rc())
                .expect("parse reciprocal definition");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse reciprocal statement");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify reciprocal definition");
            let mut missing_domain = vec![result
                .litex_to_lean_ir()
                .expect("reciprocal should retain To-Lean IR")
                .clone()];
            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveFnEqualStmt(
                function,
            )) = &mut missing_domain[0]
            else {
                panic!("expected reciprocal definition IR")
            };
            function.domain_premises.clear();
            let error = emit_lean_from_litex_to_lean_ir(&missing_domain)
                .expect_err("a named partial body without its domain FactId must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("binder requirements changed"),
                "unexpected missing named-domain rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn named_function_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"have fn id(x R) R = x
id(1) = 1
"#,
                "named-function",
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn named_function_proof_carrying_bodies_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"have fn inc(x R) R = x + 1
inc(1) = 1 + 1
"#,
                "named-function-compound-body",
            );
            assert_source_compiles_with_mathlib(
                r#"have fn reciprocal(x R: x != 0) R = 1 / x
forall a R:
    a != 0
    =>:
        reciprocal(a) = 1 / a
"#,
                "named-function-partial-body",
            );
        });
    }

    #[test]
    fn indexed_aggregate_emits_one_checked_tuple_recipe() {
        run_with_large_stack(|| {
            let source = r#"have tuple q for i1 <= 2, q[i1] = 0
q = q
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("indexed-aggregate.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse indexed aggregate tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify indexed aggregate tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("indexed aggregate statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("one checked indexed tuple should emit Lean");
            assert!(output.contains("Litex.tupleObject"), "{output}");
            assert!(output.contains("Litex.tupleObjectIsTuple"), "{output}");
            assert!(output.contains("Litex.tupleObject_dim"), "{output}");
            assert!(output.contains("Litex.tupleObject_at"), "{output}");
            assert!(output.contains("theorem __q_dim_pos"), "{output}");
            assert!(
                output.contains("Litex.Rules.numeralInNPos 2 (by norm_num)"),
                "{output}"
            );
            assert!(!output.contains("axiom q"), "{output}");
            assert!(!output.contains("sorry"), "{output}");

            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveTupleStmt(tuple)) =
                &mut ir[0]
            else {
                panic!("expected indexed tuple statement IR")
            };
            tuple.stored_facts[1].role = LitexToLeanStoredTupleFactRoleIr::Coordinate;
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a changed indexed tuple effect role must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("three ordered stored-effect roles"),
                "unexpected malformed indexed aggregate rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn indexed_aggregate_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"have tuple q for i1 <= 2, q[i1] = 0
q = q
"#,
                "indexed-aggregate",
            );
        });
    }

    #[test]
    fn statement_object_interaction_probes_compile_together() {
        run_with_large_stack(|| {
            let source = r#"have fn id(x R) R = x
witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
id(y) = y

thm one_eq_one_by_cases:
    ? forall:
        1 = 1
    by cases:
        ? 1 = 1
        case 1 = 1

have fn into_builder(x R) {z R: z = z} = x
into_builder(1) = 1
"#;
            let output = compile_to_lean_from_source(source, "statement-object-interactions.lit")
                .expect("the three deliberate statement-object interactions should compile");
            assert!(output.contains("noncomputable def y"), "{output}");
            assert!(output.contains("Litex.functionObject_apply"), "{output}");
            assert!(output.contains("theorem one_eq_one_by_cases"), "{output}");
            assert!(output.contains("have __step1"), "{output}");
            assert!(output.contains("Litex.inSetBuilder_iff.mpr"), "{output}");
            assert!(
                output.contains("change Litex.In (Litex.arg __fn_arg 0) (Litex.setBuilder"),
                "{output}"
            );
            assert!(
                !output.contains(
                    "simp only [__into_builder_spec, __into_builder_body] at __fn_arg_req"
                ),
                "{output}"
            );
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn statement_object_interaction_probes_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"have fn id(x R) R = x
witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
id(y) = y

thm one_eq_one_by_cases:
    ? forall:
        1 = 1
    by cases:
        ? 1 = 1
        case 1 = 1

have fn into_builder(x R) {z R: z = z} = x
into_builder(1) = 1
"#,
                "statement-object-interactions",
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn named_theorem_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"thm one_eq_one:
    ? forall:
        1 = 1
"#,
                "named-theorem",
            );
        });
    }

    #[test]
    fn scoped_nested_applications_emit_stable_object_aliases() {
        run_with_large_stack(|| {
            let source = scoped_nested_application_source();
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("scoped-object-cache-tracer.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse nested object-cache tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify nested object-cache tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("tracer statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &ir[0] else {
                panic!("expected one factual tracer statement")
            };
            let target_object_ids = statement
                .well_definedness
                .target_requirements
                .iter()
                .map(|requirement| requirement.well_defined_obj_id)
                .collect::<HashSet<_>>();
            let outer = statement
                .well_definedness
                .objects
                .iter()
                .find(|object| {
                    target_object_ids.contains(&object.well_defined_obj_id)
                        && strip_free_param_numeric_tags_in_display(
                            &object.source_object.to_string(),
                        )
                        .ends_with("f(g(a), t(b))")
                })
                .expect("outer cached application should have a WellDefinedObjId");
            let mut direct_children = outer
                .child_uses
                .iter()
                .filter_map(|child| match child.role {
                    WellDefinedObjChildRole::FunctionArgument {
                        layer_index: 0,
                        argument_index,
                    } => Some((argument_index, child.obj_id)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            direct_children.sort_by_key(|(argument_index, _)| *argument_index);
            assert_eq!(direct_children.len(), 2);
            assert_eq!(direct_children[0].0, 0);
            assert_eq!(direct_children[1].0, 1);
            let outer_id = outer.well_defined_obj_id;
            let child_ids = [direct_children[0].1, direct_children[1].1];
            for reused_id in [child_ids[0], child_ids[1], outer_id] {
                assert_eq!(
                    statement
                        .well_definedness
                        .source_object_uses
                        .iter()
                        .filter(|source_use| source_use.well_defined_obj_id == reused_id)
                        .count(),
                    2,
                    "both equal source occurrences must cite cached WellDefinedObjId {} directly",
                    reused_id.value()
                );
            }

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("nested applications should compile through object aliases");
            assert!(output.contains("_app : Litex.Applicable"), "{output}");
            for obj_id in [child_ids[0], child_ids[1], outer_id] {
                assert_eq!(
                    output
                        .matches(&format!("have __obj{}_app", obj_id.value()))
                        .count(),
                    1,
                    "selected WellDefinedObjId {} must have exactly one local applicability proof\n{output}",
                    obj_id.value()
                );
            }
            let source_theorem = output
                .rsplit_once("theorem __fact")
                .map(|(_, theorem)| theorem)
                .expect("emitted tracer must end with its source fact theorem");
            let source_theorem_type = source_theorem
                .split_once(":=\nby")
                .map(|(theorem_type, _)| theorem_type)
                .expect("source theorem must separate its type from its proof");
            assert_eq!(
                source_theorem_type.matches("f [(g [a]), (t [b])]").count(),
                2,
                "the two source occurrences must render the same proof-free outer object\n{output}"
            );
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("well_defined_object_"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn scoped_nested_object_aliases_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                scoped_nested_application_source(),
                "scoped-nested-object-aliases",
            );
        });
    }

    #[test]
    fn set_parameter_predicates_are_derived_from_membership_and_sethood() {
        run_with_large_stack(|| {
            let source = r#"forall s nonempty_set, t finite_set:
    s = s
    t = t
"#;
            let output = compile_to_lean_from_source(source, "derived-set-predicates.lit")
                .expect("nonempty-set and finite-set parameters should compile");
            assert!(!output.contains("def IsNonemptySet"), "{output}");
            assert!(!output.contains("def IsFiniteSet"), "{output}");
            assert!(output.contains("(s : Litex.Object)"), "{output}");
            assert!(output.contains("Litex.IsNonemptySet s"), "{output}");
            assert!(output.contains("(t : Litex.Object)"), "{output}");
            assert!(output.contains("Litex.IsFiniteSet t"), "{output}");
        });
    }

    #[test]
    fn trusted_forall_atomic_fact_replays_exact_fact_id() {
        run_with_large_stack(|| {
            let source = trusted_forall_atomic_source();
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "compile_to_lean_trusted_forall_atomic_fact.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse trusted-forall tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify trusted-forall tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("tracer statement should retain To-Lean IR")
                        .clone(),
                );
            }
            assert_eq!(ir.len(), 3, "{ir:#?}");

            let LitexToLeanStatementIr::UnsafeStmt(LitexToLeanUnsafeStmtIr::TrustStmt(trust)) =
                &ir[1]
            else {
                panic!("expected the second statement to be trust")
            };
            assert_eq!(trust.facts.len(), 1);
            let trusted_fact_id = trust.facts[0]
                .fact_id
                .expect("trusted forall should have one stored FactId");
            assert!(matches!(
                trust.facts[0].proof,
                LitexToLeanFactProofIr::Trusted
            ));

            let LitexToLeanStatementIr::Fact(statement) = &ir[2] else {
                panic!("expected the final atomic fact statement")
            };
            let final_fact_id = statement
                .source
                .fact_id
                .expect("final atomic fact should be stored");
            let proof = match &statement.source.proof {
                LitexToLeanFactProofIr::Memo { proof } => proof.as_ref(),
                proof => proof,
            };
            let LitexToLeanFactProofIr::RuleApplication {
                rule,
                parameter_requirements,
                premises,
            } = proof
            else {
                panic!("expected a known-forall rule application")
            };
            let LitexToLeanProofRuleIr::KnownForallInstantiation {
                source_fact_id,
                arguments,
            } = rule
            else {
                panic!("expected exact known-forall evidence")
            };
            assert_eq!(*source_fact_id, trusted_fact_id);
            assert_eq!(arguments.len(), 1);
            assert_eq!(arguments[0].argument.to_string(), "1");
            assert_eq!(parameter_requirements.len(), 1);
            assert!(premises.is_empty());

            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("the exact trusted-forall tracer should emit Lean");
            assert!(output.contains("axiom p : Litex.Object → Prop"), "{output}");
            assert_eq!(output.matches("axiom __fact").count(), 1, "{output}");
            assert!(
                output.contains(&format!("axiom __fact{} :", trusted_fact_id.value())),
                "{output}"
            );
            assert!(output.contains("(__h0_1 : Litex.In x Litex.R)"), "{output}");
            assert!(!output.contains("(h_0_"), "{output}");
            assert!(
                output.contains(&format!("theorem __fact{} : p 1", final_fact_id.value())),
                "{output}"
            );
            assert!(
                output.contains(&format!("__fact{} 1", trusted_fact_id.value())),
                "{output}"
            );
            assert!(
                output.contains(&format!(
                    "__fact{} 1 (Litex.Rules.numeralInR 1)",
                    trusted_fact_id.value()
                )),
                "{output}"
            );
            assert!(!output.contains("sorry"), "{output}");
            assert!(!output.contains("assumption"), "{output}");

            let LitexToLeanStatementIr::Fact(statement) = &mut ir[2] else {
                unreachable!("checked final fact statement")
            };
            let proof = match &mut statement.source.proof {
                LitexToLeanFactProofIr::Memo { proof } => proof.as_mut(),
                proof => proof,
            };
            let LitexToLeanFactProofIr::RuleApplication { rule, .. } = proof else {
                unreachable!("checked known-forall rule application")
            };
            let LitexToLeanProofRuleIr::KnownForallInstantiation { source_fact_id, .. } = rule
            else {
                unreachable!("checked known-forall evidence")
            };
            *source_fact_id = FactId::new(u64::MAX);
            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("an unavailable trusted forall FactId must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("known forall cites unavailable FactId"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn atomic_abstract_prop_without_known_forall_remains_rejected() {
        run_with_large_stack(|| {
            let error = compile_to_lean_from_source(
                "abstract_prop q(x)\n\n$q(1)\n",
                "abstract-prop-without-known-forall.lit",
            )
            .expect_err("an abstract predicate declaration alone proves no application");
            let message = error.trace_message();
            assert!(
                message.contains("verification failed") || message.contains("unknown result"),
                "unexpected Litex boundary error: {message}"
            );
        });
    }

    #[test]
    fn known_forall_uses_exact_fact_id_and_explicit_requirements() {
        run_with_large_stack(|| {
            let source = r#"abstract_prop marked(x)

trust forall x R:
    x = 1
    =>:
        $marked(x)

forall a R:
    a = 1
    a != 0
    =>:
        $marked(a)
"#;
            let output = compile_to_lean_from_source(source, "known-forall-universal-object.lit")
                .expect("known forall should replay through its retained FactId");
            assert!(
                output.contains("axiom marked : Litex.Object → Prop"),
                "{output}"
            );
            assert!(output.contains("axiom __fact"), "{output}");
            assert!(output.contains("marked a"), "{output}");
            assert!(!output.contains("assumption"), "{output}");
            assert!(!output.contains("Set ℝ"), "{output}");
        });
    }

    #[test]
    fn first_statement_tranche_emits_definitions_proofs_and_only_explicit_trust_axioms() {
        run_with_large_stack(|| {
            let source = r#"abstract_prop marked(x)

prop is_zero(x R):
    x = 0

have named_zero R = 0
by def $is_zero(named_zero)

trust $marked(named_zero)
$marked(named_zero)
"#;
            let output = compile_to_lean_from_source(source, "first-statement-tranche.lit")
                .expect("the first statement tranche should compile");
            assert!(
                output.contains("axiom marked : Litex.Object → Prop"),
                "{output}"
            );
            assert!(
                output.contains("def is_zero (x : Litex.Object) : Prop :=")
                    && output.contains("Litex.In x Litex.R ∧ (x = 0)"),
                "{output}"
            );
            assert!(
                output.contains("noncomputable def named_zero : Litex.Object := 0"),
                "{output}"
            );
            assert!(
                output.contains("change Litex.In named_zero Litex.R ∧ (named_zero = 0)"),
                "{output}"
            );
            assert_eq!(
                output.matches("axiom __fact").count(),
                1,
                "only the explicit trusted fact may become a fact axiom\n{output}"
            );
            let mut declared_fact_names = HashSet::new();
            for line in output.lines().filter(|line| {
                line.starts_with("axiom __fact") || line.starts_with("theorem __fact")
            }) {
                let name = line
                    .split_whitespace()
                    .nth(1)
                    .expect("a fact declaration has a name");
                assert!(
                    declared_fact_names.insert(name),
                    "FactId-backed Lean declaration `{name}` was emitted twice\n{output}"
                );
            }
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn every_retained_environment_fact_id_gets_one_lean_binding() {
        run_with_large_stack(|| {
            let source = r#"prop is_zero(x R):
    x = 0

$is_zero(0)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("fact-id-completeness.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse FactId completeness tracer");
            let mut retained_ids = HashSet::new();
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify FactId completeness tracer");
                let infer_result = result
                    .factual_success()
                    .map(|success| &success.infers)
                    .or_else(|| result.non_factual_success().map(|success| &success.infers))
                    .expect("successful tracer statement");
                for output in infer_result.store_fact_outputs.iter() {
                    retained_ids.extend(output.fact_id);
                    retained_ids.extend(output.inferred_fact_ids.iter().flatten().copied());
                }
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("tracer statement should retain To-Lean IR")
                        .clone(),
                );
            }
            assert!(
                retained_ids.len() > 1,
                "the tracer must retain inferred environment consequences"
            );
            let output = emit_lean_from_litex_to_lean_ir(&ir)
                .expect("every retained concrete-prop fact should replay");
            for fact_id in retained_ids {
                let name = generated_fact_name(fact_id);
                let declaration_count = output
                    .lines()
                    .filter(|line| {
                        line.starts_with(&format!("theorem {name} :"))
                            || line.starts_with(&format!("axiom {name} :"))
                    })
                    .count();
                assert_eq!(
                    declaration_count,
                    1,
                    "FactId {} must have exactly one Lean proof binding\n{output}",
                    fact_id.value()
                );
            }
        });
    }

    #[test]
    fn closed_numeric_environment_consequence_is_not_dropped() {
        run_with_large_stack(|| {
            let output = compile_to_lean_from_source("1 $in N", "numeric-env-effect.lit")
                .expect("the inferred nonnegativity FactId should replay");
            assert!(
                output.contains("theorem __fact1 : Litex.In 1 Litex.N")
                    && output.contains("theorem __fact2 : Litex.Le 0 1")
                    && output.contains("Litex.Rules.numeralLe 0 1"),
                "{output}"
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn closed_numeric_environment_consequence_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib("1 $in N", "numeric-environment-consequence");
        });
    }

    #[test]
    fn ordinary_concrete_prop_fact_replays_retained_definition_children() {
        run_with_large_stack(|| {
            let source = r#"prop is_zero(x R):
    x = 0

$is_zero(0)
have named_zero R = 0
"#;
            let output = compile_to_lean_from_source(source, "ordinary-concrete-prop-fact.lit")
                .expect("an ordinary concrete prop fact should replay its definition proof");
            assert!(output.contains("theorem __fact"), "{output}");
            assert!(
                output.contains("change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0)"),
                "{output}"
            );
            assert!(output.contains("exact And.intro"), "{output}");
            assert!(
                output.contains("noncomputable def named_zero : Litex.Object := 0"),
                "{output}"
            );
            assert!(output.matches("theorem __fact").count() >= 5, "{output}");
            assert!(!output.contains("axiom __fact"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn trusted_concrete_prop_projects_definition_consequences_as_theorems() {
        run_with_large_stack(|| {
            let source = r#"prop is_zero(x R):
    x = 0

trust $is_zero(0)
0 $in R
0 = 0
"#;
            let output = compile_to_lean_from_source(source, "trusted-prop-projection.lit")
                .expect("trusted concrete prop consequences should have checked projections");
            assert_eq!(output.matches("axiom __fact").count(), 1, "{output}");
            assert!(
                output.contains(
                    "change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at __definition"
                ),
                "{output}"
            );
            assert!(output.matches("theorem __fact").count() >= 2, "{output}");
        });
    }

    #[test]
    fn first_statement_tranche_rejects_bodyless_prop() {
        let error = compile_to_lean_from_source("prop P(x R)\n", "bodyless-prop.lit")
            .expect_err("bodyless prop must fail closed in the first tranche");
        assert!(
            error.trace_message().contains("bodyless concrete prop"),
            "unexpected rejection: {}",
            error.trace_message()
        );
    }

    #[test]
    fn first_statement_tranche_rejects_trust_have() {
        let error = compile_to_lean_from_source("trust have x R\n", "trust-have.lit")
            .expect_err("trust have remains outside the first To-Lean statement tranche");
        assert!(
            error.trace_message().contains("TrustHaveStmt")
                || error
                    .trace_message()
                    .contains("does not support statement kind"),
            "unexpected rejection: {}",
            error.trace_message()
        );
    }

    #[test]
    fn changed_object_definition_ir_is_rejected_before_lean() {
        run_with_large_stack(|| {
            let source = "have named_zero R = 0\n";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("changed-object-definition.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let mut blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse object-definition malformed-certificate source");
            let statement = runtime
                .parse_stmt(&mut blocks.remove(0))
                .expect("parse object definition");
            let result = run_stmt_at_global_env(&statement, &mut runtime)
                .expect("verify object definition baseline");
            let mut ir = vec![result
                .litex_to_lean_ir()
                .expect("object definition should retain To-Lean IR")
                .clone()];
            let LitexToLeanStatementIr::DefObjStmt(LitexToLeanDefObjStmtIr::HaveObjEqualStmt(
                statement,
            )) = &mut ir[0]
            else {
                panic!("expected have-object equality IR")
            };
            statement.definitions[0].value = LitexToLeanObjectIr::Number {
                normalized_value: "1".to_string(),
            };

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("changed object-definition evidence must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("do not match the retained definition"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn changed_definition_reduction_ir_is_rejected_before_lean() {
        run_with_large_stack(|| {
            let source = r#"prop is_zero(x R):
    x = 0
have named_zero R = 0
by def $is_zero(named_zero)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("changed-definition-reduction.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse definition-reduction malformed-certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify definition-reduction baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::By(LitexToLeanByStmtIr::ByDefStmt(statement)) = &mut ir[2]
            else {
                panic!("expected by-definition proof IR")
            };
            let LitexToLeanFactProofIr::RuleApplication { rule, .. } =
                &mut statement.facts[0].proof
            else {
                panic!("expected definition-reduction rule application")
            };
            let LitexToLeanProofRuleIr::DefinitionReduction {
                expected_clauses, ..
            } = rule
            else {
                panic!("expected definition-reduction rule")
            };
            expected_clauses.clear();

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("changed definition-reduction evidence must fail closed");
            assert!(
                error.trace_message().contains("wrong child-proof arity"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn builtin_certificate_calls_a_real_universal_object_theorem() {
        run_with_large_stack(|| {
            let source = r#"forall a, b C:
    a != b
    =>:
        b != a
"#;
            let output = compile_to_lean_from_source(source, "builtin-not-equal-symmetry.lit")
                .expect("the checked builtin certificate should compile");
            assert!(output.contains("Litex.Rules.notEqualSymmetry"), "{output}");
            assert!(!output.contains("theorem notEqualSymmetry"), "{output}");
            assert!(!output.contains("axiom notEqualSymmetry"), "{output}");
        });
    }

    #[test]
    fn known_equality_path_replays_symmetry_and_transitivity_by_fact_id() {
        run_with_large_stack(|| {
            let source = r#"forall a, b set:
    a = b
    =>:
        b = a

forall a, b, c set:
    a = b
    b = c
    =>:
        a = c
"#;
            let output = compile_to_lean_from_source(source, "known-equality-path.lit")
                .expect("known equality symmetry and transitivity should compile");
            assert!(output.contains("Eq.symm (__h0_3)"), "{output}");
            assert!(output.contains("Eq.trans"), "{output}");
            assert!(!output.contains("same known equality class"), "{output}");
        });
    }

    #[test]
    fn unavailable_known_equality_fact_id_is_rejected() {
        run_with_large_stack(|| {
            let source = r#"forall a, b set:
    a = b
    =>:
        b = a
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("bad-known-equality-fact-id.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse known-equality malformed-certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify known-equality malformed-certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let LitexToLeanFactProofIr::ForallIntroduction { conclusions, .. } =
                &mut statement.source.proof
            else {
                panic!("expected forall-introduction proof")
            };
            let conclusion_proof = match &mut conclusions[0].proof {
                LitexToLeanFactProofIr::Memo { proof } => proof.as_mut(),
                proof => proof,
            };
            let LitexToLeanFactProofIr::RuleApplication { rule, premises, .. } = conclusion_proof
            else {
                panic!("expected known-equality rule application")
            };
            let LitexToLeanProofRuleIr::KnownEqualityPath(path) = rule else {
                panic!("expected a known-equality path")
            };
            let unavailable = FactId::new(u64::MAX);
            path.steps[0].source_fact_id = unavailable;
            premises[0].fact_id = Some(unavailable);
            premises[0].proof = LitexToLeanFactProofIr::KnownFactCitation {
                source_fact_id: unavailable,
            };

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("an unavailable equality FactId must fail closed");
            assert!(
                error.trace_message().contains("unavailable FactId"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn exact_source_application_layers_use_lists_and_fn_space_result() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x, y, z R) R:
    f(1, 2, 3) = f(1, 2, 3)

forall g fn(x R) fn(y R) R:
    g(1)(2) = g(1)(2)
"#;
            let output = compile_to_lean_from_source(source, "exact-application-layers.lit")
                .expect("one-layer and nested applications should compile");
            assert!(output.contains("f [1, 2, 3]"), "{output}");
            assert!(output.contains("(g [1]) [2]"), "{output}");
            assert!(output.contains("Litex.fnSpaceResult"), "{output}");
            assert!(!output.contains("Litex.fnSetResult"), "{output}");
            assert!(
                output.matches("_result :").count() >= 3
                    && output.contains("Litex.Applicable (f)")
                    && output.contains("Litex.Applicable ((g [1]))"),
                "layered application must retain a named prefix result theorem\n{output}"
            );
            assert!(
                output.contains("Exists.intro (__wd0_")
                    && output.matches("have __wd0_").count() >= 5,
                "{output}"
            );
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn exact_source_application_layers_compile_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x, y, z R) R:
    f(1, 2, 3) = f(1, 2, 3)

forall g fn(x R) fn(y R) R:
    g(1)(2) = g(1)(2)
"#;
            assert_source_compiles_with_mathlib(source, "exact-application-layers");
        });
    }

    #[test]
    fn arithmetic_forall_tracer_replays_subtraction_and_well_definedness() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x R) R:
    forall y R:
        f(y) = f(y - 1)
    =>:
        f(2) = f(1)
"#;
            let output = compile_to_lean_from_source(source, "arithmetic-forall-tracer.lit")
                .expect("subtraction, nested forall, and exact WD evidence should compile");
            assert!(output.contains("Litex.sub"), "{output}");
            assert!(output.contains("Litex.Rules"), "{output}");
            assert!(output.contains("__wd0_"), "{output}");
            assert!(output.contains("__wd1_"), "{output}");
            assert!(output.contains("\n  have __scope"), "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(output.contains("__h0_1"), "{output}");
            assert!(output.contains("__h0_2"), "{output}");
            assert!(output.contains("__h1_1"), "{output}");
            assert!(!output.contains("litex_h_"), "{output}");
            assert!(!output.contains("litex_nh_"), "{output}");
            assert!(!output.contains("litex_domain_fact_"), "{output}");
            assert!(!output.contains("(y : ℝ)"), "{output}");
        });
    }

    #[test]
    fn first_forall_in_a_definition_starts_at_depth_zero() {
        run_with_large_stack(|| {
            let source = r#"prop has_self_equality(x R):
    forall y R:
        x = x
"#;
            let output = compile_to_lean_from_source(source, "definition-forall-depth.lit")
                .expect("the first forall in a definition should compile at depth zero");
            assert!(output.contains("(y : Litex.Object) (__h0_1 :"), "{output}");
            assert!(!output.contains("__h1_1"), "{output}");
        });
    }

    #[test]
    fn arithmetic_denotation_is_proof_free_and_wd_replays_locally() {
        run_with_large_stack(|| {
            let source = include_str!(
                "../../lean/examples/cases/compile_to_lean_proof_carrying_arithmetic.lit"
            );
            let output = compile_to_lean_from_source(source, "proof-carrying-arithmetic.lit")
                .expect("+, -, *, and / should compile from exact local WD evidence");
            assert!(output.contains("Litex.Rules.complexAddClosure"), "{output}");
            assert!(output.contains("Litex.Rules.complexSubClosure"), "{output}");
            assert!(output.contains("Litex.Rules.complexMulClosure"), "{output}");
            assert!(output.contains("Litex.Rules.complexDivClosure"), "{output}");
            assert!(output.contains("Litex.Rules.realDivClosure"), "{output}");
            assert!(output.contains("\n  have __wd0_"), "{output}");
            assert!(output.contains("\n  have __wd0_5 :"), "{output}");
            assert!(
                output.contains(
                    "_result : Litex.In (Litex.add (Litex.add a b) c) Litex.C"
                ),
                "the outer arithmetic result membership must remain in the owning theorem proof\n{output}"
            );
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(output.contains("(Litex.add (Litex.add a b) c)"), "{output}");
            assert!(output.contains("(Litex.div a b)"), "{output}");
            assert!(output.contains("__wd0_"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(!output.contains("axiom add"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn arithmetic_intrinsic_result_carrier_fails_closed_when_missing() {
        run_with_large_stack(|| {
            let source = r#"forall a, b, c C:
    (a + b) + c = (a + b) + c
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("missing-arithmetic-result-carrier.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse arithmetic result-carrier tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify arithmetic result-carrier tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected arithmetic fact statement")
            };
            let mut changed = 0;
            for arithmetic in statement
                .well_definedness
                .objects
                .iter_mut()
                .filter(|object| {
                    matches!(
                        &object.source_object,
                        Obj::Add(add) if matches!(add.left.as_ref(), Obj::Add(_))
                    )
                })
            {
                arithmetic.intrinsic_result_set = None;
                changed += 1;
            }
            assert!(
                changed > 0,
                "arithmetic statement should retain an outer addition WD object"
            );

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("missing intrinsic arithmetic result carrier must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("has no frozen intrinsic result carrier"),
                "unexpected missing-result-carrier rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn proof_carrying_occurrence_edges_fail_closed_when_missing_duplicated_or_retargeted() {
        run_with_large_stack(|| {
            let source = r#"forall a, b, c C, f fn(x C) C:
    f((a + b) + c) = f((a + b) + c)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("malformed-occurrence-wd-use.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse occurrence-edge malformed-certificate source");
            let mut baseline = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify occurrence-edge malformed-certificate baseline");
                baseline.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &baseline[0] else {
                panic!("expected one fact statement")
            };
            assert!(statement.well_definedness.source_object_uses.len() >= 4);
            let verification_dependencies = statement
                .well_definedness
                .objects
                .iter()
                .flat_map(|object| {
                    object.child_uses.iter().filter_map(move |child| {
                        matches!(
                            child.role,
                            WellDefinedObjChildRole::VerificationDependency { .. }
                        )
                        .then_some((
                            object.well_defined_obj_id,
                            child.role,
                            child.obj_id,
                        ))
                    })
                })
                .collect::<Vec<_>>();
            assert!(
                !verification_dependencies.is_empty(),
                "the tracer should preserve verifier-only object visits separately from construction slots"
            );

            let mut missing = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut missing[0] else {
                unreachable!()
            };
            statement.well_definedness.source_object_uses.remove(0);
            let error = emit_lean_from_litex_to_lean_ir(&missing)
                .expect_err("a missing source-occurrence WD edge must fail closed");
            assert!(
                error.trace_message().contains("exact WD object uses"),
                "unexpected missing-edge rejection: {}",
                error.trace_message()
            );

            let mut duplicated = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut duplicated[0] else {
                unreachable!()
            };
            let duplicate = statement.well_definedness.source_object_uses[0].clone();
            statement
                .well_definedness
                .source_object_uses
                .push(duplicate);
            let error = emit_lean_from_litex_to_lean_ir(&duplicated)
                .expect_err("a duplicated source-occurrence WD edge must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("more than one frozen WD object use"),
                "unexpected duplicate-edge rejection: {}",
                error.trace_message()
            );

            let mut retargeted = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut retargeted[0] else {
                unreachable!()
            };
            let original_id = statement.well_definedness.source_object_uses[0].well_defined_obj_id;
            let original_key =
                obj_equality_key(&statement.well_definedness.source_object_uses[0].source_object);
            let replacement_id = statement
                .well_definedness
                .objects
                .iter()
                .find(|object| {
                    matches!(object.source_object, Obj::Add(_))
                        && object.well_defined_obj_id != original_id
                        && obj_equality_key(&object.source_object) != original_key
                })
                .expect("nested arithmetic must retain a structurally distinct add node")
                .well_defined_obj_id;
            statement.well_definedness.source_object_uses[0].well_defined_obj_id = replacement_id;
            let error = emit_lean_from_litex_to_lean_ir(&retargeted)
                .expect_err("a retargeted source-occurrence WD edge must fail closed");
            assert!(
                error.trace_message().contains("changed the source object"),
                "unexpected retargeted-edge rejection: {}",
                error.trace_message()
            );

            let mut changed_occurrence_identity = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut changed_occurrence_identity[0]
            else {
                unreachable!()
            };
            let unused_occurrence_id = SourceObjectOccurrenceId::new(SymbolId::new(u64::MAX - 1));
            statement.well_definedness.source_object_uses[0].source_occurrence_id =
                unused_occurrence_id;
            let error = emit_lean_from_litex_to_lean_ir(&changed_occurrence_identity)
                .expect_err("a changed source occurrence identity must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("changed or lost its parser-owned identity"),
                "unexpected occurrence-identity rejection: {}",
                error.trace_message()
            );

            let mut changed_phase = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut changed_phase[0] else {
                unreachable!()
            };
            let requirement = statement
                .well_definedness
                .target_requirements
                .first_mut()
                .expect("nested arithmetic application should retain a target requirement");
            requirement.phase = match requirement.phase {
                WellDefinednessTargetRequirementPhase::Preflight => {
                    WellDefinednessTargetRequirementPhase::Proof
                }
                WellDefinednessTargetRequirementPhase::Proof => {
                    WellDefinednessTargetRequirementPhase::Store
                }
                WellDefinednessTargetRequirementPhase::Store => {
                    WellDefinednessTargetRequirementPhase::Preflight
                }
            };
            let error = emit_lean_from_litex_to_lean_ir(&changed_phase)
                .expect_err("a changed target-requirement phase must fail closed");
            assert!(
                error.trace_message().contains("changed execution phase"),
                "unexpected target-requirement phase rejection: {}",
                error.trace_message()
            );

            let mut missing_binder_child = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut missing_binder_child[0] else {
                unreachable!()
            };
            let function_set = statement
                .well_definedness
                .objects
                .iter_mut()
                .find(|object| matches!(object.source_object, Obj::FnSet(_)))
                .expect("application contract should retain a function-set WD node");
            let return_carrier_index = function_set
                .child_uses
                .iter()
                .position(|child| child.role == WellDefinedObjChildRole::BinderReturnCarrier)
                .expect("function-set WD recipe should retain its return carrier");
            function_set.child_uses.remove(return_carrier_index);
            let error = emit_lean_from_litex_to_lean_ir(&missing_binder_child)
                .expect_err("a missing binder return-carrier edge must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("missing required construction-child role BinderReturnCarrier"),
                "unexpected missing binder-child rejection: {}",
                error.trace_message()
            );

            let mut retargeted_function_argument = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut retargeted_function_argument[0]
            else {
                unreachable!()
            };
            let complex_set_id = statement
                .well_definedness
                .objects
                .iter()
                .find(|object| matches!(object.source_object, Obj::StandardSet(StandardSet::C)))
                .expect("application trace should retain the complex carrier")
                .well_defined_obj_id;
            let application = statement
                .well_definedness
                .objects
                .iter_mut()
                .find(|object| {
                    object.child_uses.iter().any(|child| {
                        matches!(child.role, WellDefinedObjChildRole::FunctionArgument { .. })
                    })
                })
                .expect("application WD recipe should retain one argument edge");
            let application_argument = application
                .child_uses
                .iter_mut()
                .find(|child| {
                    matches!(child.role, WellDefinedObjChildRole::FunctionArgument { .. })
                })
                .expect("checked application argument");
            application_argument.obj_id = complex_set_id;
            application_argument.source_object = StandardSet::C.into();
            let error = emit_lean_from_litex_to_lean_ir(&retargeted_function_argument)
                .expect_err("a retargeted construction child must fail closed");
            assert!(
                error.trace_message().contains("changed construction child"),
                "unexpected construction-child retarget rejection: {}",
                error.trace_message()
            );

            let mut gapped_verification_trace = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut gapped_verification_trace[0] else {
                unreachable!()
            };
            let dependency = statement
                .well_definedness
                .objects
                .iter_mut()
                .flat_map(|object| object.child_uses.iter_mut())
                .find(|child| {
                    matches!(
                        child.role,
                        WellDefinedObjChildRole::VerificationDependency { .. }
                    )
                })
                .expect("application trace should retain a verifier-only dependency");
            dependency.role = WellDefinedObjChildRole::VerificationDependency {
                dependency_index: usize::MAX,
            };
            let error = emit_lean_from_litex_to_lean_ir(&gapped_verification_trace)
                .expect_err("a gapped verification trace must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("non-contiguous verification-dependency indices"),
                "unexpected verification-trace gap rejection: {}",
                error.trace_message()
            );

            let mut retargeted_verification_dependency = baseline.clone();
            let LitexToLeanStatementIr::Fact(statement) =
                &mut retargeted_verification_dependency[0]
            else {
                unreachable!()
            };
            let dependency_snapshot_key = statement
                .well_definedness
                .objects
                .iter()
                .flat_map(|object| object.child_uses.iter())
                .find(|child| {
                    matches!(
                        child.role,
                        WellDefinedObjChildRole::VerificationDependency { .. }
                    )
                })
                .map(|child| obj_equality_key(&child.source_object))
                .expect("application trace should retain a verifier dependency");
            let replacement_id = statement
                .well_definedness
                .objects
                .iter()
                .find(|object| obj_equality_key(&object.source_object) != dependency_snapshot_key)
                .expect("trace should contain a structurally distinct object")
                .well_defined_obj_id;
            statement
                .well_definedness
                .objects
                .iter_mut()
                .flat_map(|object| object.child_uses.iter_mut())
                .find(|child| {
                    matches!(
                        child.role,
                        WellDefinedObjChildRole::VerificationDependency { .. }
                    )
                })
                .expect("checked verifier dependency")
                .obj_id = replacement_id;
            let error = emit_lean_from_litex_to_lean_ir(&retargeted_verification_dependency)
                .expect_err("a retargeted verification dependency must fail closed");
            assert!(
                error.trace_message().contains("changed child snapshot"),
                "unexpected verifier-dependency retarget rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn ordinary_constructor_cache_hit_projects_nested_source_occurrences_by_typed_roles() {
        run_with_large_stack(|| {
            let source = r#"forall a, b C:
    (a + b) ^ 2 = (a + b) ^ 2
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "ordinary-constructor-occurrence-projection.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse ordinary-constructor cache projection source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify ordinary-constructor cache projection source");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("source should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &ir[0] else {
                panic!("expected one factual statement")
            };
            let add_uses = statement
                .well_definedness
                .source_object_uses
                .iter()
                .filter(|source_use| matches!(source_use.source_object, Obj::Add(_)))
                .collect::<Vec<_>>();
            assert_eq!(
                add_uses.len(),
                2,
                "both nested additions must retain their own source-occurrence edge"
            );
            assert_eq!(
                add_uses[0].well_defined_obj_id, add_uses[1].well_defined_obj_id,
                "the second addition occurrence should reuse the exact cached child WD object"
            );
            let add_id = add_uses[0].well_defined_obj_id;
            let pow_parents = statement
                .well_definedness
                .objects
                .iter()
                .filter(|object| matches!(object.source_object, Obj::Pow(_)))
                .collect::<Vec<_>>();
            assert!(
                !pow_parents.is_empty(),
                "the certificate should retain its phase-local power nodes"
            );
            assert!(pow_parents.iter().any(|parent| {
                parent.child_uses.iter().any(|child| {
                    child.role == WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 }
                        && child.obj_id == add_id
                })
            }));
        });
    }

    #[test]
    fn finite_range_aggregate_recipe_separates_value_slots_from_audit_dependencies() {
        run_with_large_stack(|| {
            let source = r#"finite_set_sum(1...3, fn(k Z) Z {k}) = finite_set_sum(1...3, fn(k Z) Z {k})
finite_set_product(1...3, fn(k Z) Z {k}) = finite_set_product(1...3, fn(k Z) Z {k})
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "finite-range-aggregate-construction-recipe.lit",
            );
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse finite-range aggregate recipe source");

            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify finite-range aggregate recipe source");
                let LitexToLeanStatementIr::Fact(statement) = result
                    .litex_to_lean_ir()
                    .expect("aggregate statement should retain To-Lean IR")
                else {
                    panic!("expected one factual aggregate statement")
                };

                let parents = statement
                    .well_definedness
                    .objects
                    .iter()
                    .filter(|object| {
                        matches!(
                            object.source_object,
                            Obj::SumOfFiniteSet(_) | Obj::ProductOfFiniteSet(_)
                        )
                    })
                    .collect::<Vec<_>>();
                assert!(!parents.is_empty(), "{:#?}", statement.well_definedness);
                for parent in parents {
                    let value_slots = parent
                        .child_uses
                        .iter()
                        .filter_map(|child| match child.role {
                            WellDefinedObjChildRole::ConstructorArgument { argument_index } => {
                                Some(argument_index)
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(value_slots, vec![0, 1], "{parent:#?}");

                    let range_fold_dependency = parent
                        .child_uses
                        .iter()
                        .find(|child| {
                            matches!(
                                child.role,
                                WellDefinedObjChildRole::VerificationDependency { .. }
                            ) && matches!(child.source_object, Obj::Sum(_) | Obj::Product(_))
                        })
                        .expect("closed-range audit must be a separate fold dependency");
                    let dependency = statement
                        .well_definedness
                        .objects
                        .iter()
                        .find(|object| object.well_defined_obj_id == range_fold_dependency.obj_id)
                        .expect("audit dependency must name a frozen WD object");
                    let dependency_slots = dependency
                        .child_uses
                        .iter()
                        .filter_map(|child| match child.role {
                            WellDefinedObjChildRole::ConstructorArgument { argument_index } => {
                                Some(argument_index)
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(dependency_slots, vec![0, 1, 2], "{dependency:#?}");
                }
            }
        });
    }

    #[test]
    fn aggregate_object_families_emit_proof_free_universal_object_terms() {
        run_with_large_stack(|| {
            let source = r#"forall F set:
    big_union(F) = big_union(F)
forall F set:
    big_intersect(F) = big_intersect(F)
power_set(R) = power_set(R)
forall I set, S nonempty_set, g fn(i1 I) S:
    general_cart(I, S, g) = general_cart(I, S, g)
range(1, 4) = range(1, 4)
closed_range(1, 4) = closed_range(1, 4)
sum(1, 3, fn(k Z) Z {k}) = sum(1, 3, fn(k Z) Z {k})
product(1, 3, fn(k Z) Z {k}) = product(1, 3, fn(k Z) Z {k})
reduce(1, 3, fn(k Z) Z {k}, fn(x, y Z) Z {x + y}, 0) = reduce(1, 3, fn(k Z) Z {k}, fn(x, y Z) Z {x + y}, 0)
finite_set_sum(1...3, fn(k Z) Z {k}) = finite_set_sum(1...3, fn(k Z) Z {k})
finite_set_product(1...3, fn(k Z) Z {k}) = finite_set_product(1...3, fn(k Z) Z {k})
finite_set_reduce(1...3, fn(k Z) Z {k}, fn(x, y Z) Z {x + y}, 0) = finite_set_reduce(1...3, fn(k Z) Z {k}, fn(x, y Z) Z {x + y}, 0)
(1, 2, 3) = (1, 2, 3)
[1, 2, 3] = [1, 2, 3]
finite_seq(Z, 3) = finite_seq(Z, 3)
seq(Z) = seq(Z)
"#;
            let output = compile_to_lean_from_source(source, "aggregate-object-families.lit")
                .expect("all supported aggregate object families should compile");

            for expected in [
                "Litex.bigUnion F",
                "Litex.bigIntersect F",
                "Litex.powerSet Litex.R",
                "Litex.generalCart I S g",
                "Litex.range 1 4",
                "Litex.closedRange 1 4",
                "Litex.sum 1 3",
                "Litex.product 1 3",
                "Litex.reduce 1 3",
                "Litex.finiteSetSum (Litex.closedRange 1 3)",
                "Litex.finiteSetProduct (Litex.closedRange 1 3)",
                "Litex.finiteSetReduce (Litex.closedRange 1 3)",
                "Litex.tupleLiteral [1, 2, 3]",
                "Litex.sequenceLiteral [1, 2, 3]",
                "Litex.finiteSequenceSet Litex.Z 3",
                "Litex.sequenceSet Litex.Z",
            ] {
                assert!(output.contains(expected), "missing `{expected}`\n{output}");
            }
            assert!(output.contains("Litex.functionObject"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
        });
    }

    #[test]
    fn anonymous_function_wd_recipe_has_one_exact_return_route_and_occurrence_edge() {
        run_with_large_stack(|| {
            let source = "fn(x R) R {x} = fn(y R) R {y}";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("anonymous-function-wd-recipe.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse anonymous-function WD recipe source");
            let mut statements = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify anonymous-function WD recipe source");
                statements.push(
                    result
                        .litex_to_lean_ir()
                        .expect("anonymous-function source should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &statements[0] else {
                panic!("expected one factual statement")
            };
            let anonymous_uses = statement
                .well_definedness
                .source_object_uses
                .iter()
                .filter(|source_use| matches!(source_use.source_object, Obj::AnonymousFn(_)))
                .collect::<Vec<_>>();
            assert_eq!(anonymous_uses.len(), 2);
            for source_use in &anonymous_uses {
                let object = statement
                    .well_definedness
                    .objects
                    .iter()
                    .find(|object| object.well_defined_obj_id == source_use.well_defined_obj_id)
                    .expect("occurrence-selected anonymous-function WD node");
                assert_eq!(object.target_requirements.len(), 1);
                assert!(matches!(
                    object.target_requirements[0].role,
                    WellDefinednessRequirementRole::AnonymousFunctionBodyMembership
                        | WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset { .. }
                ));
                assert_eq!(
                    object.source_object.source_occurrence_id(),
                    Some(source_use.source_occurrence_id)
                );
                let scope_id = object
                    .owned_binder_scope_id
                    .expect("anonymous-function WD node must own one binder scope");
                let scope = statement
                    .well_definedness
                    .binder_scopes
                    .iter()
                    .find(|scope| scope.scope_id == scope_id)
                    .expect("owned binder scope must be frozen into IR");
                assert_eq!(scope.premises.len(), 1);
                assert_eq!(
                    scope.premises[0].role,
                    WellDefinedBinderPremiseRole::ParameterMembership {
                        parameter_group_index: 0,
                        parameter_index: 0,
                    }
                );
                assert_eq!(
                    statement
                        .well_definedness
                        .facts
                        .iter()
                        .find(|fact| {
                            fact.well_defined_fact_id
                                == object.target_requirements[0].well_defined_fact_id
                        })
                        .expect("anonymous closure fact")
                        .ambient_binder_scope_ids,
                    vec![scope_id]
                );

                let parameter_carrier = object
                    .child_uses
                    .iter()
                    .find(|child| {
                        child.role
                            == WellDefinedObjChildRole::BinderParameterCarrier {
                                parameter_group_index: 0,
                            }
                    })
                    .expect("anonymous-function parameter carrier child");
                let parameter_carrier_object = statement
                    .well_definedness
                    .objects
                    .iter()
                    .find(|child| child.well_defined_obj_id == parameter_carrier.obj_id)
                    .expect("anonymous-function parameter carrier object");
                assert_eq!(
                    parameter_carrier_object.ambient_binder_scope_ids,
                    object.ambient_binder_scope_ids,
                    "a parameter carrier must be checked before opening the function's own scope"
                );

                let body = object
                    .child_uses
                    .iter()
                    .find(|child| child.role == WellDefinedObjChildRole::BinderBody)
                    .expect("anonymous-function body child");
                let body_object = statement
                    .well_definedness
                    .objects
                    .iter()
                    .find(|child| child.well_defined_obj_id == body.obj_id)
                    .expect("anonymous-function body object");
                let mut expected_body_scopes = object.ambient_binder_scope_ids.clone();
                expected_body_scopes.push(scope_id);
                assert_eq!(
                    body_object.ambient_binder_scope_ids, expected_body_scopes,
                    "the function body must be checked inside the exact owned binder scope"
                );
            }

            let mut missing = statement.well_definedness.clone();
            missing
                .objects
                .iter_mut()
                .find(|object| matches!(object.source_object, Obj::AnonymousFn(_)))
                .expect("anonymous-function WD node")
                .target_requirements
                .clear();
            let error =
                crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                    &missing,
                )
                .expect_err("an anonymous function without a return route must fail closed");
            assert!(
                error.contains("requires exactly one checked return-closure route"),
                "unexpected missing anonymous closure rejection: {error}"
            );

            let mut missing_scope = statement.well_definedness.clone();
            missing_scope.binder_scopes.clear();
            let error =
                crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                    &missing_scope,
                )
                .expect_err("an anonymous function without its lexical scope must fail closed");
            assert!(
                error.contains("missing WellDefinedBinderScopeId"),
                "unexpected missing binder-scope rejection: {error}"
            );

            let mut missing_occurrence = statements.clone();
            let LitexToLeanStatementIr::Fact(statement) = &mut missing_occurrence[0] else {
                unreachable!()
            };
            let anonymous_use_index = statement
                .well_definedness
                .source_object_uses
                .iter()
                .position(|source_use| matches!(source_use.source_object, Obj::AnonymousFn(_)))
                .expect("anonymous-function source occurrence");
            statement
                .well_definedness
                .source_object_uses
                .remove(anonymous_use_index);
            let error = emit_lean_from_litex_to_lean_ir(&missing_occurrence)
                .expect_err("an anonymous function without its source-use edge must fail closed");
            assert!(
                error.trace_message().contains("exact WD object uses"),
                "unexpected missing anonymous occurrence rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn anonymous_function_binder_premise_order_is_frozen() {
        run_with_large_stack(|| {
            let source = "fn(x, y R: x < y) R {x} = fn(a, b R: a < b) R {a}";
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("anonymous-function-scope-order.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse ordered anonymous-function binder source");
            let mut statements = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify ordered anonymous-function binder source");
                statements.push(
                    result
                        .litex_to_lean_ir()
                        .expect("ordered binder source should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &statements[0] else {
                panic!("expected one factual statement")
            };
            let mut reordered = statement.well_definedness.clone();
            let scope = reordered
                .binder_scopes
                .iter_mut()
                .find(|scope| matches!(scope.owner_object, Obj::AnonymousFn(_)))
                .expect("anonymous-function binder scope");
            assert_eq!(scope.premises.len(), 3);
            scope.premises.swap(0, 1);
            let error =
                crate::litex_to_lean_ir::validate_litex_to_lean_well_definedness_certificate(
                    &reordered,
                )
                .expect_err("reordered binder premises must fail closed");
            assert!(
                error.contains("changed binder premise order"),
                "unexpected reordered binder-premise rejection: {error}"
            );
        });
    }

    #[test]
    fn anonymous_function_emits_checked_constructor_and_head_application() {
        run_with_large_stack(|| {
            let source = r#"fn(x R) R {x} = fn(y R) R {y}
forall a R:
    fn(x R) R {x}(a) = fn(x R) R {x}(a)
"#;
            let output = compile_to_lean_from_source(source, "anonymous-function-object.lit")
                .expect("anonymous functions and their direct application should compile");
            assert!(output.contains("Litex.functionObject"), "{output}");
            assert!(output.contains("Litex.functionObjectInFnSet"), "{output}");
            assert!(output.contains("_app"), "{output}");
            assert!(output.contains("_result"), "{output}");
            assert!(output.contains("theorem __wd0_"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn anonymous_function_with_unproved_return_membership_remains_rejected() {
        run_with_large_stack(|| {
            let source = "fn(x R) N {x} = fn(y R) N {y}";
            let error = compile_to_lean_from_source(source, "anonymous-function-bad-range.lit")
                .expect_err("an anonymous body without checked range membership must fail");
            assert!(
                error.trace_message().contains("declared return set")
                    || error.trace_message().contains("well-defined")
                    || error.trace_message().contains("not proved"),
                "unexpected anonymous-function rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn compound_anonymous_function_body_keeps_constructor_proof_free() {
        run_with_large_stack(|| {
            let source = "fn(x R) R {x + 1} = fn(y R) R {y + 1}";
            let output =
                compile_to_lean_from_source(source, "anonymous-function-compound-body.lit")
                    .expect("a compound anonymous body should replay WD under its binder");
            assert!(
                output.contains("Litex.add (Litex.arg")
                    && output.contains("Litex.functionObject")
                    && output.contains("_closed"),
                "{output}"
            );
            assert!(!output.contains("available proof telescope"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn anonymous_function_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                r#"fn(x R) R {x} = fn(y R) R {y}
fn(x R) R {x + 1} = fn(y R) R {y + 1}
forall a R:
    fn(x R) R {x + 1}(a) = fn(x R) R {x + 1}(a)
"#,
                "anonymous-function-object",
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn owned_construction_scopes_compile_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                include_str!(
                    "../../lean/examples/cases/compile_to_lean_owned_construction_scopes.lit"
                ),
                "owned-construction-scopes",
            );
        });
    }

    #[test]
    fn proof_carrying_list_set_replays_indexed_well_definedness() {
        run_with_large_stack(|| {
            let source = include_str!(
                "../../lean/examples/cases/compile_to_lean_proof_carrying_list_set.lit"
            );
            let output = compile_to_lean_from_source(source, "proof-carrying-list-set.lit")
                .expect("a finite set literal should compile from exact indexed WD evidence");
            assert!(output.contains("Litex.listSet [a, b]"), "{output}");
            assert!(output.contains("\n  have __wd0_"), "{output}");
            assert!(!output.contains("List.Pairwise.cons"), "{output}");
            assert!(!output.contains("\ntheorem __wd"), "{output}");
            assert!(!output.contains("\nnoncomputable def __obj"), "{output}");
            assert!(!output.contains("well_defined_fact_"), "{output}");
            assert!(!output.contains("axiom listSet"), "{output}");
            assert!(!output.contains("sorry"), "{output}");
        });
    }

    #[test]
    fn missing_builtin_argument_well_definedness_role_is_rejected() {
        run_with_large_stack(|| {
            let source = r#"forall a, b C:
    a + b = a + b
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("missing-arithmetic-wd-role.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse arithmetic malformed-certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify arithmetic malformed-certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let mut removed = 0;
            for object in statement.well_definedness.objects.iter_mut() {
                if matches!(&object.source_object, Obj::Add(_)) {
                    let original = object.target_requirements.len();
                    object.target_requirements.retain(|requirement| {
                        requirement.role
                            != WellDefinednessRequirementRole::BuiltinArgumentMembership {
                                argument_index: 1,
                            }
                    });
                    removed += original - object.target_requirements.len();
                }
            }
            assert!(
                removed > 0,
                "baseline IR must retain the right operand WD role"
            );

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a missing ordered arithmetic WD role must fail closed");
            assert!(
                error.trace_message().contains("exactly two ordered")
                    || error.trace_message().contains("no named exact Lean proof")
                    || error
                        .trace_message()
                        .contains("target requirement recipe changed"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn missing_divisor_nonzero_well_definedness_role_is_rejected() {
        run_with_large_stack(|| {
            let source = r#"forall a, b C:
    b != 0
    =>:
        a / b = a / b
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("missing-division-nonzero-role.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse division malformed-certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify division malformed-certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let mut removed = 0;
            for object in statement.well_definedness.objects.iter_mut() {
                if matches!(&object.source_object, Obj::Div(_)) {
                    let original = object.target_requirements.len();
                    object.target_requirements.retain(|requirement| {
                        requirement.role
                            != WellDefinednessRequirementRole::BuiltinArgumentNonzero {
                                argument_index: 1,
                            }
                    });
                    removed += original - object.target_requirements.len();
                }
            }
            assert!(removed > 0, "baseline IR must retain the nonzero WD role");

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a missing division nonzero role must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("exactly one denominator-nonzero proof")
                    || error
                        .trace_message()
                        .contains("target requirement recipe changed"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn missing_list_set_pairwise_well_definedness_role_is_rejected() {
        run_with_large_stack(|| {
            let source = r#"forall a, b set:
    a != b
    =>:
        {a, b} = {a, b}
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("missing-list-set-pair-role.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse list-set malformed-certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify list-set malformed-certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let mut removed = 0;
            for object in statement.well_definedness.objects.iter_mut() {
                if matches!(&object.source_object, Obj::ListSet(_)) {
                    let original = object.target_requirements.len();
                    object.target_requirements.retain(|requirement| {
                        requirement.role
                            != WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                                left_index: 0,
                                right_index: 1,
                            }
                    });
                    removed += original - object.target_requirements.len();
                }
            }
            assert!(
                removed > 0,
                "baseline IR must retain the indexed pairwise WD role"
            );

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a missing list-set pairwise role must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("requires 1 ordered pairwise-distinctness proofs")
                    || error
                        .trace_message()
                        .contains("target requirement recipe changed"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn reversed_list_set_pairwise_well_definedness_role_is_rejected() {
        run_with_large_stack(|| {
            let source = r#"forall a, b set:
    a != b
    =>:
        {a, b} = {a, b}
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("reversed-list-set-pair-role.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse reversed list-set certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify reversed list-set certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let mut changed = 0;
            for requirement in statement
                .well_definedness
                .objects
                .iter_mut()
                .filter(|object| matches!(&object.source_object, Obj::ListSet(_)))
                .flat_map(|object| object.target_requirements.iter_mut())
                .filter(|requirement| {
                    requirement.role
                        == WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                            left_index: 0,
                            right_index: 1,
                        }
                })
            {
                requirement.role = WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                    left_index: 1,
                    right_index: 0,
                };
                changed += 1;
            }
            assert!(changed > 0, "baseline list set must retain pair (0,1)");

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a reversed list-set pairwise role must fail closed");
            assert!(
                error
                    .trace_message()
                    .contains("duplicate, reversed, or out-of-range pairwise role")
                    || error
                        .trace_message()
                        .contains("reversed or out-of-range pairwise role"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn retargeted_list_set_pairwise_proposition_is_rejected() {
        run_with_large_stack(|| {
            let source = r#"forall a, b, c set:
    a != b
    a != c
    b != c
    =>:
        {a, b, c} = {a, b, c}
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("retargeted-list-set-pair.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse retargeted list-set certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify retargeted list-set certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let mut changed_count = 0;
            for object in statement
                .well_definedness
                .objects
                .iter_mut()
                .filter(|object| matches!(&object.source_object, Obj::ListSet(_)))
            {
                let Obj::ListSet(source_set) = &object.source_object else {
                    unreachable!()
                };
                let changed: Fact = NotEqualFact::new(
                    source_set.list[0].as_ref().clone(),
                    source_set.list[2].as_ref().clone(),
                    default_line_file(),
                )
                .into();
                for requirement in object.target_requirements.iter_mut().filter(|requirement| {
                    requirement.role
                        == WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
                            left_index: 0,
                            right_index: 1,
                        }
                }) {
                    requirement.expected_proposition = changed.clone();
                    changed_count += 1;
                }
            }
            assert!(
                changed_count > 0,
                "baseline list set must retain pair (0,1)"
            );

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a retargeted list-set proposition must fail closed");
            assert!(
                error.trace_message().contains("changed proposition")
                    || error.trace_message().contains("changed WellDefinedFactId")
                    || error
                        .trace_message()
                        .contains("changed an indexed `left != right` requirement"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn dangling_well_defined_object_child_is_rejected_before_emission() {
        run_with_large_stack(|| {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("dangling-wd-child.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(
                    scoped_nested_application_source(),
                    runtime.current_file_path_rc(),
                )
                .expect("parse nested object-cache tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify nested object-cache tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("tracer statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let child = statement
                .well_definedness
                .objects
                .iter_mut()
                .find_map(|object| object.child_uses.first_mut())
                .expect("nested tracer must retain a child edge");
            child.obj_id = WellDefinedObjId::new(u64::MAX);

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("a dangling WD child must fail before Lean emission");
            assert!(
                error
                    .trace_message()
                    .contains("cites missing child WellDefinedObjId"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn retargeted_well_defined_fact_id_is_rejected_before_emission() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x, y R) R:
    f(1, 2) = f(1, 2)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("mismatched-wd-fact-pair.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse two-argument application tracer");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify two-argument application tracer");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("tracer statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let requirement = statement
                .well_definedness
                .target_requirements
                .first_mut()
                .expect("function application must retain a target requirement");
            let different_well_defined_fact_id = statement
                .well_definedness
                .facts
                .iter()
                .find(|fact| fact.well_defined_fact_id != requirement.well_defined_fact_id)
                .map(|fact| fact.well_defined_fact_id)
                .expect("two arguments must retain another WD fact");
            requirement.well_defined_fact_id = different_well_defined_fact_id;

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("retargeted WD fact identity must fail before Lean emission");
            assert!(
                error.trace_message().contains("changed WellDefinedFactId")
                    || error
                        .trace_message()
                        .contains("is not an edge of WellDefinedObjId"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn changed_application_occurrence_id_is_rejected_without_structural_fallback() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x R) R:
    f(1) = f(1)
"#;
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("changed-occurrence-id.lit");
            runtime.start_well_defined_capture();
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .expect("parse malformed-certificate source");
            let mut ir = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).expect("parse statement");
                let result = run_stmt_at_global_env(&statement, &mut runtime)
                    .expect("verify malformed-certificate baseline");
                ir.push(
                    result
                        .litex_to_lean_ir()
                        .expect("baseline statement should retain To-Lean IR")
                        .clone(),
                );
            }
            let LitexToLeanStatementIr::Fact(statement) = &mut ir[0] else {
                panic!("expected one fact statement")
            };
            let requirements = &mut statement.well_definedness.target_requirements;
            assert_eq!(
                requirements
                    .iter()
                    .map(|requirement| requirement.source_occurrence_id)
                    .collect::<HashSet<_>>()
                    .len(),
                2,
                "equal source applications must retain distinct occurrence IDs"
            );
            assert_eq!(
                requirements
                    .iter()
                    .map(|requirement| requirement.well_defined_obj_id)
                    .collect::<HashSet<_>>()
                    .len(),
                1,
                "cache reuse should cite one environment-owned WD proof"
            );
            let first = requirements
                .first()
                .expect("two application occurrences should retain WD requirements")
                .source_occurrence_id;
            let replacement = requirements
                .iter()
                .map(|requirement| requirement.source_occurrence_id)
                .find(|occurrence| *occurrence != first)
                .expect("the two source applications must have distinct occurrence IDs");
            for requirement in requirements.iter_mut() {
                if requirement.source_occurrence_id == first {
                    requirement.source_occurrence_id = replacement;
                }
            }

            let error = emit_lean_from_litex_to_lean_ir(&ir)
                .expect_err("changed source occurrence identity must fail closed");
            assert!(
                error.trace_message().contains("source occurrence")
                    || error.trace_message().contains("no named exact WD fact"),
                "unexpected strict rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    fn split_application_layer_does_not_bypass_litex_arity() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x, y, z R) R:
    f(1)(2, 3) = f(1)(2, 3)
"#;
            let error = compile_to_lean_from_source(source, "split-application-layer.lit")
                .expect_err("Litex must reject a split application of a one-layer function set");
            assert!(
                error.trace_message().contains("parameter")
                    || error.trace_message().contains("well-defined")
                    || error.trace_message().contains("cannot verify"),
                "unexpected rejection: {}",
                error.trace_message()
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn first_statement_tranche_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = include_str!(
                "../../lean/examples/cases/compile_to_lean_first_statement_tranche.lit"
            );
            assert_source_compiles_with_mathlib(source, "first-statement-tranche");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn universal_object_tracer_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"forall a C, f fn(x R) R:
    a = 1
    =>:
        1 $in R
        a $in R
        f(a) = f(a)
"#;
            assert_source_compiles_with_mathlib(source, "universal-object-tracer");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn trusted_forall_atomic_fact_compiles_with_mathlib() {
        run_with_large_stack(|| {
            assert_source_compiles_with_mathlib(
                trusted_forall_atomic_source(),
                "trusted-forall-atomic-fact",
            );
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn known_forall_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"abstract_prop marked(x)

trust forall x R:
    x = 1
    =>:
        $marked(x)

forall a R:
    a = 1
    a != 0
    =>:
        $marked(a)
"#;
            assert_source_compiles_with_mathlib(source, "known-forall-universal-object");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn builtin_certificate_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"forall a, b C:
    a != b
    =>:
        b != a
"#;
            assert_source_compiles_with_mathlib(source, "builtin-not-equal-symmetry");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn known_equality_path_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"forall a, b set:
    a = b
    =>:
        b = a

forall a, b, c set:
    a = b
    b = c
    =>:
        a = c
"#;
            assert_source_compiles_with_mathlib(source, "known-equality-path");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn arithmetic_forall_tracer_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x R) R:
    forall y R:
        f(y) = f(y - 1)
    =>:
        f(2) = f(1)
"#;
            assert_source_compiles_with_mathlib(source, "arithmetic-forall-tracer");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn proof_carrying_arithmetic_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = include_str!(
                "../../lean/examples/cases/compile_to_lean_proof_carrying_arithmetic.lit"
            );
            assert_source_compiles_with_mathlib(source, "proof-carrying-arithmetic");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn proof_carrying_list_set_compiles_with_mathlib() {
        run_with_large_stack(|| {
            let source = include_str!(
                "../../lean/examples/cases/compile_to_lean_proof_carrying_list_set.lit"
            );
            assert_source_compiles_with_mathlib(source, "proof-carrying-list-set");
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn set_parameter_predicates_compile_with_mathlib() {
        run_with_large_stack(|| {
            let source = r#"forall s nonempty_set, t finite_set:
    s = s
    t = t
"#;
            assert_source_compiles_with_mathlib(source, "derived-set-predicates");
        });
    }

    fn assert_source_compiles_with_mathlib(source: &str, label: &str) {
        use crate::compile_to_lean::lean_test_support::SharedLeanTestLibrary;

        let generated = compile_to_lean_from_source(source, &format!("{label}.lit"))
            .expect("the universal-object source should compile");
        let mut library = SharedLeanTestLibrary::new(label);
        library.compile_generated(label, &generated);
    }

    fn scoped_nested_application_source() -> &'static str {
        include_str!("../../lean/examples/cases/compile_to_lean_well_defined_object_dag.lit")
    }

    fn readable_function_spaces_source() -> &'static str {
        r#"forall f fn(a R) R:
    f = f

forall f fn(a R, b C) R:
    f = f

forall f fn(a R, b C, c Z) R:
    f = f

forall f fn(a R, b C, c Z, d Q) R:
    f = f

forall f fn(a R, b C, c Z, d Q, m N) R:
    f = f

forall f fn(a R, b C, c Z, d Q, m N, p N+) R:
    f = f
"#
    }

    fn trusted_forall_atomic_source() -> &'static str {
        include_str!("../../lean/examples/cases/compile_to_lean_trusted_forall_atomic_fact.lit")
    }

    fn run_with_large_stack(action: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name("universal_to_lean_test".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn(action)
            .expect("spawn universal To-Lean test thread")
            .join()
            .expect("universal To-Lean test thread panicked");
    }
}
