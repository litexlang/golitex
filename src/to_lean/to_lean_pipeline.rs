use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::rational_expression::{lean_name, LeanRationalExpression};
use super::set_prelude::LITEX_SET_PRELUDE;
use super::{
    ToLeanCompilationReport, ToLeanCompilationStatus, ToLeanUnsupported, ToLeanUnsupportedPhase,
};

enum ToLeanStatementOutcome {
    Ir(StmtToLeanIR),
    Unsupported(String),
}

struct ToLeanStatementInput {
    statement_index: usize,
    statement: String,
    line_file: LineFile,
    outcome: ToLeanStatementOutcome,
}

pub fn to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let namespace = lean_namespace_for_runtime(runtime);
    to_lean_with_namespace(source_code, runtime, namespace)
}

/// Compiles every supported statement and returns an explicit completeness
/// status. Parsing, execution, and verification errors remain hard failures.
pub fn to_lean_with_report(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<ToLeanCompilationReport, RuntimeError> {
    let namespace = lean_namespace_for_runtime(runtime);
    to_lean_with_report_and_namespace(source_code, runtime, namespace)
}

fn to_lean_with_namespace(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<String>,
) -> Result<String, RuntimeError> {
    let previous_mode = runtime.replace_to_lean_mode(true);
    let result = to_lean_in_mode(source_code, runtime, namespace.as_deref());
    runtime.replace_to_lean_mode(previous_mode);
    result
}

fn to_lean_in_mode(
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
            return Err(to_lean_error(
                &statement.line_file(),
                "To-Lean received an unverified Litex statement",
            ));
        }
        let Some(statement_ir) = result.to_lean_ir() else {
            return Err(to_lean_error(
                &statement.line_file(),
                "To-Lean mode completed a statement without producing IR",
            ));
        };
        ir.push(statement_ir.clone());
    }

    if ir.is_empty() {
        return Err(to_lean_error(
            &default_line_file(),
            "To-Lean requires at least one supported statement",
        ));
    }

    emit_lean_from_ir_with_namespace(&ir, namespace)
}

pub fn to_lean_from_source(source_code: &str, entry_label: &str) -> Result<String, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_lean_with_namespace(&normalized, &mut runtime, None)
}

pub fn to_lean_from_source_with_report(
    source_code: &str,
    entry_label: &str,
) -> Result<ToLeanCompilationReport, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    to_lean_with_report_and_namespace(&normalized, &mut runtime, None)
}

/// Pure backend boundary: this function has no Runtime and cannot inspect raw
/// Litex statements or re-run proof search.
pub fn emit_lean_from_ir(ir: &[StmtToLeanIR]) -> Result<String, RuntimeError> {
    emit_lean_from_ir_with_namespace(ir, None)
}

/// Pure partial backend boundary. Every rejected IR statement is represented
/// in the returned report and as a Lean comment; no axiom or sorry is added.
pub fn emit_lean_from_ir_with_report(ir: &[StmtToLeanIR]) -> ToLeanCompilationReport {
    let statements = ir
        .iter()
        .enumerate()
        .map(|(index, statement)| ToLeanStatementInput {
            statement_index: index + 1,
            statement: statement_ir_display(statement),
            line_file: statement_ir_line_file(statement),
            outcome: ToLeanStatementOutcome::Ir(statement.clone()),
        })
        .collect::<Vec<_>>();
    emit_lean_report(statements, None)
}

fn to_lean_with_report_and_namespace(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<String>,
) -> Result<ToLeanCompilationReport, RuntimeError> {
    // Eager To-Lean mode turns IR construction failures into execution errors.
    // Report mode owns that boundary so it can retain the verified statement,
    // record the unsupported IR, and continue with later statements.
    let previous_mode = runtime.replace_to_lean_mode(false);
    let result = to_lean_report_in_mode(source_code, runtime, namespace.as_deref());
    runtime.replace_to_lean_mode(previous_mode);
    result
}

fn to_lean_report_in_mode(
    source_code: &str,
    runtime: &mut Runtime,
    namespace: Option<&str>,
) -> Result<ToLeanCompilationReport, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = tokenizer.parse_blocks(source_code, current_file_path)?;
    let mut statements = Vec::with_capacity(blocks.len());

    for (index, mut block) in blocks.into_iter().enumerate() {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(to_lean_error(
                &statement.line_file(),
                "To-Lean received an unverified Litex statement",
            ));
        }
        let outcome = match runtime.build_stmt_to_lean_ir(&result) {
            Ok(ir) => ToLeanStatementOutcome::Ir(ir),
            Err(error) => ToLeanStatementOutcome::Unsupported(error.trace_message()),
        };
        statements.push(ToLeanStatementInput {
            statement_index: index + 1,
            statement: statement.to_string(),
            line_file: statement.line_file(),
            outcome,
        });
    }

    if statements.is_empty() {
        return Err(to_lean_error(
            &default_line_file(),
            "To-Lean requires at least one supported statement",
        ));
    }

    Ok(emit_lean_report(statements, namespace))
}

fn emit_lean_report(
    statements: Vec<ToLeanStatementInput>,
    namespace: Option<&str>,
) -> ToLeanCompilationReport {
    let mut emitter = LeanEmitter::new(namespace.map(str::to_string));
    let mut unsupported = Vec::new();

    for statement in statements {
        let diagnostic = match statement.outcome {
            ToLeanStatementOutcome::Unsupported(reason) => Some(ToLeanUnsupported::new(
                statement.statement_index,
                statement.statement,
                &statement.line_file,
                ToLeanUnsupportedPhase::IrConstruction,
                reason,
            )),
            ToLeanStatementOutcome::Ir(ir) => {
                let checkpoint = emitter.clone();
                match emitter.emit_statement(&ir) {
                    Ok(()) => None,
                    Err(error) => {
                        emitter = checkpoint;
                        Some(ToLeanUnsupported::new(
                            statement.statement_index,
                            statement.statement,
                            &statement.line_file,
                            ToLeanUnsupportedPhase::LeanEmission,
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
        ToLeanCompilationStatus::Complete
    } else {
        ToLeanCompilationStatus::Incomplete
    };
    let lean_code = emitter.finish_with_report(status, unsupported.len());
    ToLeanCompilationReport::new(lean_code, unsupported)
}

fn emit_lean_from_ir_with_namespace(
    ir: &[StmtToLeanIR],
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
    emitted_fact_ids: HashSet<FactId>,
    next_local_space_id: usize,
}

#[derive(Clone, Default)]
struct LeanProofContext {
    // Litex FactIds remain the lookup keys; emitted local names use independent
    // proof-space coordinates.
    proof_fact_names: HashMap<FactId, String>,
    nonzero_names: Vec<String>,
    real_memberships: Vec<(Obj, String)>,
    local_space_id: Option<usize>,
    next_local_index: usize,
}

impl LeanProofContext {
    fn new_proof_space(&self) -> Self {
        LeanProofContext {
            proof_fact_names: self.proof_fact_names.clone(),
            nonzero_names: self.nonzero_names.clone(),
            real_memberships: self.real_memberships.clone(),
            local_space_id: None,
            next_local_index: 0,
        }
    }
}

impl LeanEmitter {
    fn new(namespace: Option<String>) -> Self {
        LeanEmitter {
            namespace,
            declarations: Vec::new(),
            emitted_fact_ids: HashSet::new(),
            next_local_space_id: 1,
        }
    }

    fn finish(self) -> String {
        self.finish_with_status_comment(None)
    }

    fn finish_with_report(
        self,
        status: ToLeanCompilationStatus,
        unsupported_count: usize,
    ) -> String {
        let status_comment = match status {
            ToLeanCompilationStatus::Complete => "-- To-Lean status: complete".to_string(),
            ToLeanCompilationStatus::Incomplete => format!(
                "-- To-Lean status: incomplete\n-- Omitted statements: {}",
                unsupported_count
            ),
        };
        self.finish_with_status_comment(Some(status_comment))
    }

    fn finish_with_status_comment(self, status_comment: Option<String>) -> String {
        let status_comment = status_comment
            .map(|comment| format!("{}\n\n", comment))
            .unwrap_or_default();
        let body = format!(
            "{}{}\n\n{}",
            status_comment,
            LITEX_SET_PRELUDE,
            self.declarations.join("\n\n")
        );
        match self.namespace {
            Some(namespace) => format!(
                "import Mathlib\n\nnamespace {}\n\n{}\n\nend {}\n",
                namespace, body, namespace
            ),
            None => format!("import Mathlib\n\n{}\n", body),
        }
    }

    fn emit_unsupported(&mut self, diagnostic: &ToLeanUnsupported) {
        self.declarations.push(format!(
            "-- To-Lean omitted statement {} during {} at {}:{}.\n-- Statement: {}\n-- Reason: {}",
            diagnostic.statement_index,
            diagnostic.phase.label(),
            lean_comment_text(&diagnostic.source_path),
            diagnostic.line,
            lean_comment_text(&diagnostic.statement),
            lean_comment_text(&diagnostic.reason),
        ));
    }

    fn emit_statement(&mut self, statement: &StmtToLeanIR) -> Result<(), RuntimeError> {
        match statement {
            StmtToLeanIR::AbstractProp(ir) => {
                self.declarations.push(lean_abstract_prop(ir));
                Ok(())
            }
            StmtToLeanIR::Prop(ir) => {
                self.declarations.push(lean_prop(ir)?);
                Ok(())
            }
            StmtToLeanIR::HaveObjChoice(ir) => self.emit_object_choices(ir),
            StmtToLeanIR::HaveExistentialWitness(ir) => self.emit_existential_witnesses(ir),
            StmtToLeanIR::HaveObjEqual(ir) => {
                for definition in ir.definitions.iter() {
                    self.declarations.push(format!(
                        "def {} : LitexSet := {}",
                        lean_name(&definition.name),
                        lean_obj_ir(&definition.value)?
                    ));
                }
                for fact in ir.facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            StmtToLeanIR::Proof(ir) => {
                for fact in ir.facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            StmtToLeanIR::Trust(ir) => {
                for fact in ir.facts.iter() {
                    self.emit_trusted_fact(fact)?;
                }
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
            StmtToLeanIR::Fact(ir) => {
                self.emit_proved_fact(&ir.fact)?;
                for fact in ir.inferred_facts.iter() {
                    self.emit_proved_fact(fact)?;
                }
                Ok(())
            }
        }
    }

    fn emit_existential_witnesses(
        &mut self,
        ir: &HaveExistentialWitnessToLeanIR,
    ) -> Result<(), RuntimeError> {
        let layout = validate_existential_elimination(ir)?;
        let first_witness = ir.witnesses.first().ok_or_else(|| {
            to_lean_error(
                &ir.source.proposition.line_file(),
                "existential elimination IR must contain at least one witness",
            )
        })?;
        let source_name = lean_exist_source_name(first_witness.symbol_id);
        let source_proof = self.lean_proof(
            &ir.source.proposition,
            &ir.source.proof,
            &LeanProofContext::default(),
        )?;
        self.declarations.push(format!(
            "-- Litex checked existential source for `{}`\ntheorem {} : {} := {}",
            lean_comment_text(&first_witness.name),
            source_name,
            lean_fact(&ir.source.proposition)?,
            source_proof
        ));

        for (witness, value_term) in ir.witnesses.iter().zip(layout.witness_terms.iter()) {
            self.declarations.push(format!(
                "noncomputable def {} : LitexSet := {}",
                lean_name(&witness.name),
                value_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name)
            ));
        }
        for (projection, proof_term) in ir.projections.iter().zip(layout.proof_terms.iter()) {
            let fact_id = required_fact_id(projection)?;
            if !self.emitted_fact_ids.insert(fact_id) {
                return Err(to_lean_error(
                    &projection.proposition.line_file(),
                    "existential projection FactId was emitted before its witness definition",
                ));
            }
            let proof_term = proof_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name);
            self.declarations.push(format!(
                "-- Litex stored fact {}\ntheorem {} : {} := by\n  exact {}",
                fact_id,
                lean_global_fact_name(fact_id),
                lean_fact(&projection.proposition)?,
                proof_term
            ));
        }
        Ok(())
    }

    fn emit_object_choices(&mut self, ir: &HaveObjChoiceToLeanIR) -> Result<(), RuntimeError> {
        if ir.choices.is_empty() {
            return Err(to_lean_error(
                &default_line_file(),
                "object-choice IR must contain at least one selected object",
            ));
        }
        for choice in ir.choices.iter() {
            let membership_fact_id = validate_object_choice(choice)?;
            if self.emitted_fact_ids.contains(&membership_fact_id) {
                return Err(to_lean_error(
                    &choice.membership.proposition.line_file(),
                    "object-choice membership FactId was emitted before its definition",
                ));
            }
            let source_name = lean_choice_source_name(choice.symbol_id);
            let source_proof = self.lean_proof(
                &choice.nonempty_proof.proposition,
                &choice.nonempty_proof.proof,
                &LeanProofContext::default(),
            )?;
            self.declarations.push(format!(
                "-- Litex checked choice source for `{}`\ntheorem {} : {} := {}",
                lean_comment_text(&choice.name),
                source_name,
                lean_fact(&choice.nonempty_proof.proposition)?,
                source_proof
            ));
            self.declarations.push(format!(
                "noncomputable def {} : LitexSet := Exists.choose {}",
                lean_name(&choice.name),
                source_name
            ));
            self.emitted_fact_ids.insert(membership_fact_id);
            self.declarations.push(format!(
                "-- Litex stored fact {}\ntheorem {} : {} := by\n  exact Exists.choose_spec {}",
                membership_fact_id,
                lean_global_fact_name(membership_fact_id),
                lean_fact(&choice.membership.proposition)?,
                source_name
            ));
        }
        Ok(())
    }

    fn emit_trusted_fact(&mut self, fact: &FactToLeanIR) -> Result<(), RuntimeError> {
        if !matches!(fact.proof, FactProofToLeanIR::Trusted) {
            return Err(to_lean_error(
                &fact.proposition.line_file(),
                "only an explicit Litex `trust` statement may emit a Lean axiom",
            ));
        }
        let fact_id = required_fact_id(fact)?;
        if !self.emitted_fact_ids.insert(fact_id) {
            return Ok(());
        }
        self.declarations.push(format!(
            "-- Litex trust boundary: {}\naxiom {} : {}",
            fact_id,
            lean_global_fact_name(fact_id),
            lean_fact(&fact.proposition)?
        ));
        Ok(())
    }

    fn emit_proved_fact(&mut self, fact: &FactToLeanIR) -> Result<(), RuntimeError> {
        let fact_id = required_fact_id(fact)?;
        if self.emitted_fact_ids.contains(&fact_id) {
            return Ok(());
        }
        if matches!(fact.proof, FactProofToLeanIR::Trusted) {
            return Err(to_lean_error(
                &fact.proposition.line_file(),
                "trusted evidence reached theorem emission outside a `trust` statement",
            ));
        }
        let proof =
            self.lean_proof(&fact.proposition, &fact.proof, &LeanProofContext::default())?;
        self.emitted_fact_ids.insert(fact_id);
        self.declarations.push(format!(
            "-- Litex stored fact {}\ntheorem {} : {} := {}",
            fact_id,
            lean_global_fact_name(fact_id),
            lean_fact(&fact.proposition)?,
            proof
        ));
        Ok(())
    }

    fn lean_proof(
        &mut self,
        proposition: &Fact,
        proof: &FactProofToLeanIR,
        parent_context: &LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let mut context = parent_context.new_proof_space();
        self.lean_proof_in_current_space(proposition, proof, &mut context)
    }

    fn lean_proof_in_current_space(
        &mut self,
        proposition: &Fact,
        proof: &FactProofToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        match proof {
            FactProofToLeanIR::KnownFactCitation { source_fact_id } => {
                let source = self.available_fact_name(*source_fact_id, proposition, context)?;
                Ok(format!("by\n  exact {}", source))
            }
            FactProofToLeanIR::ExistentialAlphaRenameCitation {
                source_fact_id,
                source_proposition,
            } => {
                validate_existential_alpha_rename(source_proposition, proposition)?;
                let source = self.available_fact_name(*source_fact_id, proposition, context)?;
                Ok(format!("by\n  exact {}", source))
            }
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::Builtin(rule),
                parameter_requirements,
                premises,
            } => self.lean_builtin_rule_application(
                proposition,
                rule,
                parameter_requirements,
                premises,
                context,
            ),
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::ObjectReflexivity,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "object-reflexivity evidence was attached to a non-equality",
                    ));
                };
                if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "object-reflexivity evidence has different left and right objects",
                    ));
                }
                Ok("by\n  rfl".to_string())
            }
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::ClosedRealMembership,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                Ok("by\n  change True\n  trivial".to_string())
            }
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::RealSetNonempty,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                lean_real_set_nonempty(proposition)
            }
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::ClassicalExcludedMiddle,
                parameter_requirements,
                premises,
            } if parameter_requirements.is_empty() && premises.is_empty() => {
                lean_classical_excluded_middle(proposition)
            }
            FactProofToLeanIR::RuleApplication {
                rule:
                    ProofRuleToLeanIR::KnownForallInstantiation {
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
            FactProofToLeanIR::RuleApplication {
                rule:
                    ProofRuleToLeanIR::Normalization {
                        kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                    },
                premises,
                ..
            } if premises.is_empty() => lean_rational_builtin_proof(proposition, context),
            FactProofToLeanIR::RuleApplication {
                rule:
                    ProofRuleToLeanIR::Normalization {
                        kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                    },
                premises,
                ..
            } if premises.len() == 1 => {
                self.lean_normalization_from_premise(proposition, &premises[0], context)
            }
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::DefinitionReduction { definition },
                premises,
                ..
            } if premises.is_empty() => Ok(format!("by\n  simp [{}]", lean_name(definition))),
            FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::EqualityRewrite(rewrite),
                premises,
                ..
            } => self.lean_equality_rewrite(proposition, rewrite, premises, context),
            FactProofToLeanIR::RuleApplication {
                rule:
                    ProofRuleToLeanIR::ExistIntroduction {
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
            FactProofToLeanIR::RuleApplication { rule, .. } => Err(to_lean_error(
                &proposition.line_file(),
                format!("To-Lean has no checked backend for proof rule {:?}", rule),
            )),
            FactProofToLeanIR::ForallIntroduction {
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
            FactProofToLeanIR::ObjectDefinition {
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
            FactProofToLeanIR::ObjectChoice { .. } => Err(to_lean_error(
                &proposition.line_file(),
                "object-choice membership must be emitted with its defining choice statement",
            )),
            FactProofToLeanIR::ExistentialElimination { .. } => Err(to_lean_error(
                &proposition.line_file(),
                "existential projections must be emitted with their defining elimination statement",
            )),
            FactProofToLeanIR::CaseSplit { coverage, branches } => {
                self.lean_case_split(proposition, coverage, branches, context)
            }
            FactProofToLeanIR::ByContradiction {
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
            FactProofToLeanIR::Memo { proof } => {
                self.lean_proof_in_current_space(proposition, proof, context)
            }
            FactProofToLeanIR::Composite { steps } if steps.len() == 1 => {
                self.lean_proof_in_current_space(&steps[0].proposition, &steps[0].proof, context)
            }
            FactProofToLeanIR::UserStrategy { name } => Err(to_lean_error(
                &proposition.line_file(),
                format!("To-Lean does not yet lower user strategy `{}`", name),
            )),
            FactProofToLeanIR::Inference { reason, .. } => Err(to_lean_error(
                &proposition.line_file(),
                format!(
                    "To-Lean does not yet lower inferred fact origin `{}`",
                    reason
                ),
            )),
            FactProofToLeanIR::Unsupported { reason } => {
                Err(to_lean_error(&proposition.line_file(), reason.clone()))
            }
            FactProofToLeanIR::Trusted => Err(to_lean_error(
                &proposition.line_file(),
                "trusted proof cannot be emitted as a theorem",
            )),
            FactProofToLeanIR::Composite { .. } => Err(to_lean_error(
                &proposition.line_file(),
                "To-Lean does not yet lower multi-step composite evidence",
            )),
        }
    }

    fn lean_named_local_fact(
        &mut self,
        fact: &FactToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<(String, Vec<String>), RuntimeError> {
        let local_name = self.next_proof_fact_name(context);
        if let Some(fact_id) = fact.fact_id {
            if let Some(local) = context.proof_fact_names.get(&fact_id) {
                return Ok((
                    local_name.clone(),
                    vec![format!(
                        "  have {} : {} := {}",
                        local_name,
                        lean_fact(&fact.proposition)?,
                        local
                    )],
                ));
            }
        }
        if let FactProofToLeanIR::KnownFactCitation { source_fact_id } = &fact.proof {
            let source = self.available_fact_name(*source_fact_id, &fact.proposition, context)?;
            return Ok((
                local_name.clone(),
                vec![format!(
                    "  have {} : {} := {}",
                    local_name,
                    lean_fact(&fact.proposition)?,
                    source
                )],
            ));
        }

        let proof = self.lean_proof(&fact.proposition, &fact.proof, context)?;
        let mut proof_lines = proof.lines();
        let first = proof_lines.next().ok_or_else(|| {
            to_lean_error(
                &fact.proposition.line_file(),
                "a local fact emitted an empty Lean proof",
            )
        })?;
        let mut lines = vec![format!(
            "  have {} : {} := {}",
            local_name,
            lean_fact(&fact.proposition)?,
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
        value: &ObjToLeanIR,
        value_check: Option<&FactToLeanIR>,
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
            return Err(to_lean_error(
                &proposition.line_file(),
                "a defining object equality must be an equality fact",
            ));
        };
        if lean_obj(&equality.left)? != definition
            || lean_obj(&equality.right)? != lean_obj_ir(value)?
        {
            return Err(to_lean_error(
                &proposition.line_file(),
                "a defining object equality does not match its declaration IR",
            ));
        }
        Ok("by\n  rfl".to_string())
    }

    fn lean_case_split(
        &mut self,
        proposition: &Fact,
        coverage: &FactToLeanIR,
        branches: &[CaseBranchToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::OrFact(coverage_fact) = &coverage.proposition else {
            return Err(to_lean_error(
                &coverage.proposition.line_file(),
                "case-split coverage must be a disjunction",
            ));
        };
        if coverage_fact.facts.len() != branches.len() || branches.len() < 2 {
            return Err(to_lean_error(
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
                return Err(to_lean_error(
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
                CaseBranchExitToLeanIR::Conclusion(conclusion) => {
                    if conclusion.proposition.to_string() != proposition.to_string() {
                        return Err(to_lean_error(
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
                        return Err(to_lean_error(
                            &conclusion.proposition.line_file(),
                            "case-split conclusion did not emit a Lean proof block",
                        ));
                    };
                    body.extend(proof_body.lines().map(str::to_string));
                }
                CaseBranchExitToLeanIR::Contradiction(contradiction) => {
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
        reverse_assumption: &LocalPremiseToLeanIR,
        steps: &[StmtToLeanIR],
        contradiction: &ContradictionToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::AtomicFact(target) = proposition else {
            return Err(to_lean_error(
                &proposition.line_file(),
                "this To-Lean tranche lowers `by contra` only for atomic goals",
            ));
        };
        let expected_reverse = target.logical_negation()?;
        if reverse_assumption.fact.to_string() != Fact::from(expected_reverse).to_string() {
            return Err(to_lean_error(
                &reverse_assumption.fact.line_file(),
                "by-contra reverse assumption is not the logical negation of its goal",
            ));
        }
        let _ = lean_fact(proposition)?;
        let reverse_fact_text = lean_fact(&reverse_assumption.fact)?;

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
        statement: &StmtToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let mut lines = Vec::new();
        match statement {
            StmtToLeanIR::Fact(ir) => {
                lines.extend(self.lean_local_fact(&ir.fact, context)?);
                for fact in ir.inferred_facts.iter() {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            StmtToLeanIR::Proof(ir) => {
                for fact in ir.facts.iter().chain(ir.inferred_facts.iter()) {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            StmtToLeanIR::HaveObjChoice(ir) => {
                lines.extend(self.lean_local_object_choices(ir, context)?);
            }
            StmtToLeanIR::HaveExistentialWitness(ir) => {
                lines.extend(self.lean_local_existential_witnesses(ir, context)?);
            }
            StmtToLeanIR::HaveObjEqual(ir) => {
                for definition in ir.definitions.iter() {
                    lines.push(format!(
                        "  let {} : LitexSet := {}",
                        lean_name(&definition.name),
                        lean_obj_ir(&definition.value)?
                    ));
                }
                for fact in ir.facts.iter() {
                    lines.extend(self.lean_local_fact(fact, context)?);
                }
            }
            other => {
                return Err(to_lean_error(
                    &statement_ir_line_file(other),
                    format!(
                        "To-Lean does not support local statement `{}` inside a proof scope",
                        statement_ir_display(other)
                    ),
                ));
            }
        }
        Ok(lines)
    }

    fn lean_local_existential_witnesses(
        &mut self,
        ir: &HaveExistentialWitnessToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        let layout = validate_existential_elimination(ir)?;
        let (source_name, mut lines) = self.lean_named_local_fact(&ir.source, context)?;
        for (witness, value_term) in ir.witnesses.iter().zip(layout.witness_terms.iter()) {
            lines.push(format!(
                "  let {} : LitexSet := {}",
                lean_name(&witness.name),
                value_term.replace(EXIST_SOURCE_PLACEHOLDER, &source_name)
            ));
        }
        for (projection, proof_term) in ir.projections.iter().zip(layout.proof_terms.iter()) {
            let fact_id = required_fact_id(projection)?;
            let local_name = self.next_proof_fact_name(context);
            lines.push(format!(
                "  have {} : {} := by",
                local_name,
                lean_fact(&projection.proposition)?
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
        ir: &HaveObjChoiceToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<Vec<String>, RuntimeError> {
        if ir.choices.is_empty() {
            return Err(to_lean_error(
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
            lines.push(format!(
                "  let {} : LitexSet := Exists.choose {}",
                lean_name(&choice.name),
                source_name
            ));
            let membership_name = self.next_proof_fact_name(context);
            lines.push(format!(
                "  have {} : {} := by",
                membership_name,
                lean_fact(&choice.membership.proposition)?
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
        fact: &FactToLeanIR,
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
        contradiction: &ContradictionToLeanIR,
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
            return Err(to_lean_error(
                &contradiction.fact.proposition.line_file(),
                "a contradiction exit currently requires complementary atomic facts",
            ));
        };
        let facts_are_complements = fact
            .logical_negation()
            .is_ok_and(|negation| negation.to_string() == negated_fact.to_string());
        if !facts_are_complements {
            return Err(to_lean_error(
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
        steps: &[StmtToLeanIR],
        expected_parameter_requirements: &[Fact],
        expected_body_facts: &[Fact],
        parameter_requirements: &[FactToLeanIR],
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::ExistFact(ExistFactEnum::ExistFact(body)) = proposition else {
            return Err(to_lean_error(
                &proposition.line_file(),
                "existential-introduction evidence requires a positive `exist` target",
            ));
        };
        let param_types = flattened_exist_param_types(body);
        if witnesses.is_empty() || witnesses.len() != param_types.len() {
            return Err(to_lean_error(
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
            return Err(to_lean_error(
                &proposition.line_file(),
                "existential-introduction requirement or body-premise count is inconsistent",
            ));
        }
        for (actual, expected) in parameter_requirements
            .iter()
            .zip(expected_parameter_requirements.iter())
        {
            if actual.fact_id.is_some() || actual.proposition.to_string() != expected.to_string() {
                return Err(to_lean_error(
                    &proposition.line_file(),
                    "existential-introduction parameter evidence disagrees with its retained proposition",
                ));
            }
        }
        for (actual, expected) in premises.iter().zip(expected_body_facts.iter()) {
            if actual.fact_id.is_some() || actual.proposition.to_string() != expected.to_string() {
                return Err(to_lean_error(
                    &proposition.line_file(),
                    "existential-introduction body evidence disagrees with its retained proposition",
                ));
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
            ObjToLeanIR::lower(witness)
                .map_err(|message| to_lean_error(&proposition.line_file(), message))?;
            constructor_parts.push(lean_obj(witness)?);
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

    fn lean_builtin_rule_application(
        &mut self,
        proposition: &Fact,
        rule: &BuiltinRuleToLeanIR,
        parameter_requirements: &[FactToLeanIR],
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        match rule {
            BuiltinRuleToLeanIR::DivNotEqualZero(evidence) => {
                if !parameter_requirements.is_empty() {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "div-nonzero builtin evidence does not accept parameter requirements",
                    ));
                }
                self.lean_div_not_equal_zero_builtin(proposition, evidence, premises, context)
            }
            BuiltinRuleToLeanIR::Arithmetic(rule) => {
                if !parameter_requirements.is_empty() {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "arithmetic builtin evidence does not accept parameter requirements",
                    ));
                }
                self.lean_arithmetic_builtin_rule(proposition, *rule, premises, context)
            }
            BuiltinRuleToLeanIR::PositiveRealMembership => {
                if !parameter_requirements.is_empty() {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "positive-real membership evidence does not accept parameter requirements",
                    ));
                }
                self.lean_positive_real_membership(proposition, premises, context)
            }
        }
    }

    fn lean_positive_real_membership(
        &mut self,
        proposition: &Fact,
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 1 {
            return Err(to_lean_error(
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
                return Err(to_lean_error(
                    &proposition.line_file(),
                    "positive-real membership evidence requires a strict positivity target",
                ));
            }
        };
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &premises[0].proposition else {
            return Err(to_lean_error(
                &premises[0].proposition.line_file(),
                "positive-real membership evidence requires an `R+` membership premise",
            ));
        };
        if !matches!(membership.set, Obj::StandardSet(StandardSet::RPos))
            || obj_equality_key(&membership.element) != obj_equality_key(positive_object)
        {
            return Err(to_lean_error(
                &premises[0].proposition.line_file(),
                "positive-real membership evidence premise does not match its target object",
            ));
        }

        let (premise_name, mut lines) = self.lean_named_local_fact(&premises[0], context)?;
        lines.insert(0, "by".to_string());
        lines.push(format!("  exact litexMemRPosPositive {}", premise_name));
        Ok(lines.join("\n"))
    }

    fn lean_arithmetic_builtin_rule(
        &mut self,
        proposition: &Fact,
        rule: ArithmeticBuiltinRuleToLeanIR,
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let (target_class, premise_classes) = arithmetic_builtin_contract(rule);
        if lean_fact_class(proposition) != Some(target_class) {
            return Err(to_lean_error(
                &proposition.line_file(),
                format!(
                    "arithmetic builtin {:?} has the wrong target fact family",
                    rule
                ),
            ));
        }
        if premises.len() != premise_classes.len() {
            return Err(to_lean_error(
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
                return Err(to_lean_error(
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
        let (view_lines, real_equalities) = lean_real_view_lines(context);
        lines.extend(view_lines);
        let proof = match rule {
            ArithmeticBuiltinRuleToLeanIR::MulNonnegative => {
                format!("mul_nonneg {} {}", premise_names[0], premise_names[1])
            }
            ArithmeticBuiltinRuleToLeanIR::MulPositive => {
                format!("mul_pos {} {}", premise_names[0], premise_names[1])
            }
            ArithmeticBuiltinRuleToLeanIR::DivNonnegative => format!(
                "div_nonneg {} (le_of_lt {})",
                premise_names[0], premise_names[1]
            ),
            ArithmeticBuiltinRuleToLeanIR::DivPositive => {
                format!("div_pos {} {}", premise_names[0], premise_names[1])
            }
            _ => format!("linarith only [{}]", premise_names.join(", ")),
        };
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact(proposition)?
        ));
        let mut rewrite_targets = premise_names.clone();
        rewrite_targets.push("⊢".to_string());
        lines.push(format!(
            "    simp only [{}] at {}",
            litex_real_view_simp(&real_equalities),
            rewrite_targets.join(" ")
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
        evidence: &DivNotEqualZeroToLeanIR,
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != 2 {
            return Err(to_lean_error(
                &proposition.line_file(),
                format!(
                    "div-nonzero builtin evidence expected 2 premises but received {}",
                    premises.len()
                ),
            ));
        }

        let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) = proposition else {
            return Err(to_lean_error(
                &proposition.line_file(),
                "div-nonzero builtin evidence was attached to a non-inequality",
            ));
        };
        let (quotient, zero) = match evidence.orientation {
            NonzeroExpressionOrientationToLeanIR::ExpressionOnLeft => {
                let Obj::Div(quotient) = &target.left else {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "div-nonzero evidence expected a quotient on the left",
                    ));
                };
                (quotient, &target.right)
            }
            NonzeroExpressionOrientationToLeanIR::ExpressionOnRight => {
                let Obj::Div(quotient) = &target.right else {
                    return Err(to_lean_error(
                        &proposition.line_file(),
                        "div-nonzero evidence expected a quotient on the right",
                    ));
                };
                (quotient, &target.left)
            }
        };
        if !matches!(zero, Obj::Number(number) if number.normalized_value == "0") {
            return Err(to_lean_error(
                &proposition.line_file(),
                "div-nonzero evidence requires a literal zero target",
            ));
        }
        if obj_equality_key(quotient.left.as_ref()) != obj_equality_key(&evidence.numerator)
            || obj_equality_key(quotient.right.as_ref()) != obj_equality_key(&evidence.denominator)
        {
            return Err(to_lean_error(
                &proposition.line_file(),
                "div-nonzero evidence bindings disagree with the target quotient",
            ));
        }

        let expected_operands = [&evidence.numerator, &evidence.denominator];
        for (index, premise) in premises.iter().enumerate() {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(nonzero)) = &premise.proposition else {
                return Err(to_lean_error(
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
                return Err(to_lean_error(
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
        let (view_lines, real_equalities) = lean_real_view_lines(context);
        lines.extend(view_lines);
        let forward_proof = format!("div_ne_zero {} {}", premise_names[0], premise_names[1]);
        let proof = match evidence.orientation {
            NonzeroExpressionOrientationToLeanIR::ExpressionOnLeft => forward_proof,
            NonzeroExpressionOrientationToLeanIR::ExpressionOnRight => {
                format!("Ne.symm ({})", forward_proof)
            }
        };
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact(proposition)?
        ));
        let mut rewrite_targets = premise_names.clone();
        rewrite_targets.push("⊢".to_string());
        lines.push(format!(
            "    simp only [{}] at {}",
            litex_real_view_simp(&real_equalities),
            rewrite_targets.join(" ")
        ));
        lines.push(format!("    exact {}", proof));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_known_forall_instantiation(
        &mut self,
        proposition: &Fact,
        source_fact_id: FactId,
        arguments: &[KnownForallArgumentToLeanIR],
        parameter_requirements: &[FactToLeanIR],
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if arguments.len() != parameter_requirements.len() {
            return Err(to_lean_error(
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
            let lean_argument = lean_obj(&argument.argument)?;
            let lean_param_type = lean_ir_param_type(&argument.param_type)?;
            lines.push(format!(
                "  -- Litex parameter requirement for `{}`: {} : {}",
                argument.param, lean_argument, lean_param_type
            ));
            lines.push(format!(
                "  let {} : {} := {}",
                local_name, lean_param_type, lean_argument
            ));
            argument_names.push(local_name);
            if !matches!(argument.param_type, ParamTypeToLeanIR::LitexSet) {
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
            lean_fact(proposition)?,
            terms.join(" ")
        ));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_normalization_from_premise(
        &mut self,
        proposition: &Fact,
        premise: &FactToLeanIR,
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let mut lines = vec!["by".to_string()];
        let (source_name, source_lines) = self.lean_named_local_fact(premise, context)?;
        lines.extend(source_lines);
        let (view_lines, real_equalities) = lean_real_view_lines(context);
        lines.extend(view_lines);
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact(proposition)?
        ));
        lines.push(format!(
            "    simp only [{}] at {} ⊢",
            litex_real_view_simp(&real_equalities),
            source_name
        ));
        lines.push(format!(
            "    convert {} using 1 <;> {}",
            source_name,
            rational_fact_normalization_tactic(&premise.proposition, proposition, context)?
        ));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
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
        if self.emitted_fact_ids.contains(&fact_id) {
            return Ok(lean_global_fact_name(fact_id));
        }
        Err(to_lean_error(
            &proposition.line_file(),
            format!(
                "To-Lean proof references {} before that fact has a Lean declaration",
                fact_id
            ),
        ))
    }

    fn lean_equality_rewrite(
        &mut self,
        proposition: &Fact,
        rewrite: &EqualityRewriteToLeanIR,
        premises: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        if premises.len() != rewrite.steps.len() + 1 {
            return Err(to_lean_error(
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
                return Err(to_lean_error(
                    &equality_premise.proposition.line_file(),
                    "an equality-rewrite premise is not an equality fact",
                ));
            };
            let left_key = obj_equality_key(&equality.left);
            let right_key = obj_equality_key(&equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let orientation_matches = match step.direction {
                EqualityRewriteDirectionToLeanIR::Forward => {
                    from_key == left_key && to_key == right_key
                }
                EqualityRewriteDirectionToLeanIR::Backward => {
                    from_key == right_key && to_key == left_key
                }
            };
            if !orientation_matches {
                return Err(to_lean_error(
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
            lean_fact(proposition)?
        ));
        lines.push(format!(
            "    simpa only [{}] using {}",
            rewrite_terms.join(", "),
            source_name
        ));
        lines.push(format!("  exact {}", result_name));
        Ok(lines.join("\n"))
    }

    fn lean_forall_introduction(
        &mut self,
        proposition: &Fact,
        parameter_premises: &[LocalPremiseToLeanIR],
        premises: &[LocalPremiseToLeanIR],
        inferred_premises: &[FactToLeanIR],
        conclusions: &[FactToLeanIR],
        context: &mut LeanProofContext,
    ) -> Result<String, RuntimeError> {
        let Fact::ForallFact(forall) = proposition else {
            return Err(to_lean_error(
                &proposition.line_file(),
                "forall-introduction evidence was attached to a non-forall proposition",
            ));
        };
        if conclusions.len() != 1 || forall.then_facts.len() != 1 {
            return Err(to_lean_error(
                &forall.line_file,
                "To-Lean MVP requires one conclusion in a forall proof",
            ));
        }

        let mut intro_names = forall
            .params_def_with_type
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|binding| lean_name(binding.name())))
            .collect::<Vec<_>>();
        for premise in parameter_premises.iter() {
            if matches!(premise.fact, Fact::AtomicFact(AtomicFact::IsSetFact(_))) {
                context
                    .proof_fact_names
                    .insert(premise.fact_id, "(by trivial)".to_string());
                continue;
            }
            let local_name = self.next_proof_fact_name(context);
            context
                .proof_fact_names
                .insert(premise.fact_id, local_name.clone());
            if let Some((object, membership_proof)) =
                real_membership_proof(&premise.fact, &local_name)
            {
                if !context
                    .real_memberships
                    .iter()
                    .any(|(known, _)| obj_equality_key(known) == obj_equality_key(&object))
                {
                    context.real_memberships.push((object, membership_proof));
                }
            }
            intro_names.push(local_name);
        }
        for premise in premises.iter() {
            let local_name = self.next_proof_fact_name(context);
            context
                .proof_fact_names
                .insert(premise.fact_id, local_name.clone());
            if is_nonzero_fact(&premise.fact) {
                context.nonzero_names.push(local_name.clone());
            }
            intro_names.push(local_name);
        }
        let mut inferred_lines = Vec::new();
        for inferred in inferred_premises {
            let fact_id = required_fact_id(inferred)?;
            let (local_name, local_lines) = self.lean_named_local_fact(inferred, context)?;
            inferred_lines.extend(local_lines);
            register_local_fact(fact_id, &inferred.proposition, &local_name, context);
        }
        let conclusion = &conclusions[0];
        let inner =
            self.lean_proof_in_current_space(&conclusion.proposition, &conclusion.proof, context)?;
        let inner = inner.strip_prefix("by\n").unwrap_or(inner.as_str());
        let mut lines = vec![
            "by".to_string(),
            format!("  intro {}", intro_names.join(" ")),
        ];
        lines.extend(inferred_lines);
        lines.push(inner.to_string());
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

fn arithmetic_builtin_contract(
    rule: ArithmeticBuiltinRuleToLeanIR,
) -> (LeanFactClass, &'static [LeanFactClass]) {
    use ArithmeticBuiltinRuleToLeanIR::*;
    use LeanFactClass::*;

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

fn lean_abstract_prop(ir: &AbstractPropToLeanIR) -> String {
    let name = lean_name(&ir.name);
    if ir.params.is_empty() {
        return format!("opaque {} : LitexFact", name);
    }
    format!(
        "opaque {} : {}LitexFact",
        name,
        "LitexSet → ".repeat(ir.params.len())
    )
}

fn lean_prop(ir: &PropToLeanIR) -> Result<String, RuntimeError> {
    let binders = ir
        .params
        .iter()
        .map(|group| {
            Ok(format!(
                "({} : {})",
                group
                    .names
                    .iter()
                    .map(|name| lean_name(name))
                    .collect::<Vec<_>>()
                    .join(" "),
                lean_ir_param_type(&group.param_type)?
            ))
        })
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let binder_text = if binders.is_empty() {
        String::new()
    } else {
        format!(" {}", binders.join(" "))
    };
    if ir.iff_facts.is_empty() {
        return Ok(format!(
            "opaque {}{} : LitexFact",
            lean_name(&ir.name),
            binder_text
        ));
    }
    let body = ir
        .iff_facts
        .iter()
        .map(lean_fact)
        .collect::<Result<Vec<_>, RuntimeError>>()?
        .join(" ∧ ");
    Ok(format!(
        "def {}{} : LitexFact := {}",
        lean_name(&ir.name),
        binder_text,
        parenthesize_if_many(&body, ir.iff_facts.len())
    ))
}

fn lean_ir_param_type(param_type: &ParamTypeToLeanIR) -> Result<&'static str, RuntimeError> {
    match param_type {
        ParamTypeToLeanIR::LitexSet
        | ParamTypeToLeanIR::MemberOf(_)
        | ParamTypeToLeanIR::LitexNonemptySet
        | ParamTypeToLeanIR::LitexFiniteSet => Ok("LitexSet"),
        ParamTypeToLeanIR::Unsupported(_) => Err(to_lean_error(
            &default_line_file(),
            format!("To-Lean does not support parameter type {:?}", param_type),
        )),
    }
}

fn lean_fact(fact: &Fact) -> Result<String, RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic) => lean_atomic_fact(atomic),
        Fact::AndFact(and_fact) => Ok(parenthesized_join(
            and_fact
                .facts
                .iter()
                .map(lean_atomic_fact)
                .collect::<Result<Vec<_>, RuntimeError>>()?,
            " ∧ ",
        )),
        Fact::OrFact(or_fact) => Ok(parenthesized_join(
            or_fact
                .facts
                .iter()
                .map(|branch| lean_fact(&branch.clone().into()))
                .collect::<Result<Vec<_>, RuntimeError>>()?,
            " ∨ ",
        )),
        Fact::ForallFact(forall) => lean_forall_fact(forall),
        Fact::ExistFact(exist) => lean_exist_fact(exist),
        other => Err(to_lean_error(
            &other.line_file(),
            format!(
                "To-Lean proposition backend does not support `{}`",
                other.fact_type_string()
            ),
        )),
    }
}

fn lean_exist_fact(exist: &ExistFactEnum) -> Result<String, RuntimeError> {
    let ExistFactEnum::ExistFact(body) = exist else {
        return Err(to_lean_error(
            &exist.line_file(),
            "To-Lean proposition backend currently supports positive `exist`, not `exist!` or `not exist`",
        ));
    };
    ensure_lean_binders_are_capture_free(
        body.params_def_with_type.groups.iter(),
        body.get_args_from_fact_ref(),
        &body.line_file,
        "existential",
    )?;
    let body_parts = body
        .facts
        .iter()
        .map(lean_exist_body_fact)
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let mut tail = lean_right_associated_conjunction(&body_parts);
    for group in body.params_def_with_type.groups.iter().rev() {
        for binding in group.params.iter().rev() {
            let name = lean_name(binding.name());
            if let Some(requirement) = lean_exist_param_requirement(&name, &group.param_type)? {
                tail = format!("{} ∧ {}", requirement, tail);
            }
            tail = format!("∃ {} : LitexSet, {}", name, tail);
        }
    }
    Ok(tail)
}

fn lean_exist_body_fact(fact: &ExistBodyFact) -> Result<String, RuntimeError> {
    lean_fact(&fact.from_ref_to_cloned_fact())
}

fn lean_exist_param_requirement(
    name: &str,
    param_type: &ParamType,
) -> Result<Option<String>, RuntimeError> {
    match param_type {
        ParamType::Set(_) => Ok(None),
        ParamType::NonemptySet(_) => Ok(Some(format!("litexIsNonemptySet {}", name))),
        ParamType::FiniteSet(_) => Ok(Some(format!("litexIsFiniteSet {}", name))),
        ParamType::Obj(carrier) => Ok(Some(format!("{} ∈ {}", name, lean_obj(carrier)?))),
    }
}

fn lean_right_associated_conjunction(parts: &[String]) -> String {
    match parts {
        [] => "True".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}) ∧ {}", first, lean_right_associated_conjunction(rest)),
    }
}

fn lean_classical_excluded_middle(proposition: &Fact) -> Result<String, RuntimeError> {
    let Fact::OrFact(or_fact) = proposition else {
        return Err(to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle evidence requires a disjunction",
        ));
    };
    if or_fact.facts.len() != 2 {
        return Err(to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle evidence requires exactly two branches",
        ));
    }
    let (AndChainAtomicFact::AtomicFact(first), AndChainAtomicFact::AtomicFact(second)) =
        (&or_fact.facts[0], &or_fact.facts[1])
    else {
        return Err(to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle branches must be atomic",
        ));
    };
    let branches_are_complements = first
        .logical_negation()
        .is_ok_and(|negation| negation.to_string() == second.to_string());
    if !branches_are_complements {
        return Err(to_lean_error(
            &proposition.line_file(),
            "classical excluded-middle branches are not logical complements",
        ));
    }
    let first_text = lean_fact(&Fact::from(first.clone()))?;
    let second_text = lean_fact(&Fact::from(second.clone()))?;
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

fn lean_atomic_fact(fact: &AtomicFact) -> Result<String, RuntimeError> {
    match fact {
        AtomicFact::NormalAtomicFact(normal) => {
            lean_prop_application(&normal.predicate.to_string(), &normal.body, false)
        }
        AtomicFact::NotNormalAtomicFact(normal) => {
            lean_prop_application(&normal.predicate.to_string(), &normal.body, true)
        }
        AtomicFact::EqualFact(fact) => lean_binary_fact(&fact.left, "=", &fact.right),
        AtomicFact::NotEqualFact(fact) => lean_binary_fact(&fact.left, "≠", &fact.right),
        AtomicFact::LessFact(fact) => lean_binary_fact(&fact.left, "<", &fact.right),
        AtomicFact::LessEqualFact(fact) => lean_binary_fact(&fact.left, "≤", &fact.right),
        AtomicFact::GreaterFact(fact) => lean_binary_fact(&fact.left, ">", &fact.right),
        AtomicFact::GreaterEqualFact(fact) => lean_binary_fact(&fact.left, "≥", &fact.right),
        AtomicFact::IsSetFact(fact) => Ok(format!("litexIsSet {}", lean_obj(&fact.set)?)),
        AtomicFact::IsNonemptySetFact(fact) => {
            Ok(format!("litexIsNonemptySet {}", lean_obj(&fact.set)?))
        }
        AtomicFact::IsFiniteSetFact(fact) => {
            Ok(format!("litexIsFiniteSet {}", lean_obj(&fact.set)?))
        }
        AtomicFact::InFact(fact) => Ok(format!(
            "{} ∈ {}",
            lean_obj(&fact.element)?,
            lean_obj(&fact.set)?
        )),
        AtomicFact::SubsetFact(fact) => Ok(format!(
            "litexSubset {} {}",
            lean_obj(&fact.left)?,
            lean_obj(&fact.right)?
        )),
        AtomicFact::NotIsSetFact(fact) => Ok(format!("¬ litexIsSet {}", lean_obj(&fact.set)?)),
        AtomicFact::NotIsNonemptySetFact(fact) => {
            Ok(format!("¬ litexIsNonemptySet {}", lean_obj(&fact.set)?))
        }
        AtomicFact::NotIsFiniteSetFact(fact) => {
            Ok(format!("¬ litexIsFiniteSet {}", lean_obj(&fact.set)?))
        }
        AtomicFact::NotInFact(fact) => Ok(format!(
            "{} ∉ {}",
            lean_obj(&fact.element)?,
            lean_obj(&fact.set)?
        )),
        AtomicFact::NotSubsetFact(fact) => Ok(format!(
            "¬ litexSubset {} {}",
            lean_obj(&fact.left)?,
            lean_obj(&fact.right)?
        )),
        other => Err(to_lean_error(
            &other.line_file(),
            format!("To-Lean does not support atomic proposition `{}`", other),
        )),
    }
}

fn lean_prop_application(name: &str, args: &[Obj], negated: bool) -> Result<String, RuntimeError> {
    let mut application = lean_name(name);
    for arg in args {
        application.push(' ');
        application.push_str(&lean_obj(arg)?);
    }
    if negated {
        Ok(format!("¬ ({})", application))
    } else {
        Ok(application)
    }
}

fn lean_binary_fact(left: &Obj, operator: &str, right: &Obj) -> Result<String, RuntimeError> {
    let left_text = lean_obj(left)?;
    let left_text = if closed_rational_expression(left) {
        format!("({} : LitexSet)", left_text)
    } else {
        left_text
    };
    Ok(format!("{} {} {}", left_text, operator, lean_obj(right)?))
}

fn lean_forall_fact(forall: &ForallFact) -> Result<String, RuntimeError> {
    let mut objects = Vec::new();
    collect_forall_objects_for_lean_name_check(forall, &mut objects);
    ensure_lean_binders_are_capture_free(
        forall.params_def_with_type.groups.iter(),
        objects,
        &forall.line_file,
        "universal",
    )?;
    let mut binders = Vec::new();
    let mut parameter_requirements = Vec::new();
    for group in forall.params_def_with_type.groups.iter() {
        let names = group
            .params
            .iter()
            .map(|binding| lean_name(binding.name()))
            .collect::<Vec<_>>()
            .join(" ");
        binders.push(format!(
            "({} : {})",
            names,
            lean_param_type(&group.param_type)?
        ));
        for binding in group.params.iter() {
            let name = lean_name(binding.name());
            match &group.param_type {
                ParamType::Set(_) => {}
                ParamType::NonemptySet(_) => {
                    parameter_requirements.push(format!("litexIsNonemptySet {}", name));
                }
                ParamType::FiniteSet(_) => {
                    parameter_requirements.push(format!("litexIsFiniteSet {}", name));
                }
                ParamType::Obj(set) => {
                    parameter_requirements.push(format!("{} ∈ {}", name, lean_obj(set)?));
                }
            }
        }
    }
    let conclusions = forall
        .then_facts
        .iter()
        .map(|fact| lean_fact(&fact.clone().to_fact()))
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let mut body = parenthesized_join(conclusions, " ∧ ");
    let mut requirements = parameter_requirements;
    requirements.extend(
        forall
            .dom_facts
            .iter()
            .map(lean_fact)
            .collect::<Result<Vec<_>, RuntimeError>>()?,
    );
    for premise in requirements.iter().rev() {
        body = format!("{} → {}", premise, body);
    }
    Ok(format!("∀ {}, {}", binders.join(" "), body))
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
        let object_ir =
            ObjToLeanIR::lower(object).map_err(|message| to_lean_error(line_file, message))?;
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
    object: &ObjToLeanIR,
    binders_by_id: &HashMap<SymbolId, (String, String)>,
    binders_by_lean_name: &HashMap<String, (SymbolId, String)>,
    line_file: &LineFile,
    context: &str,
) -> Result<(), RuntimeError> {
    match object {
        ObjToLeanIR::Symbol { symbol_id, name } => {
            let emitted_name = lean_name(name);
            if let Some((binder_name, source_name)) = binders_by_id.get(symbol_id) {
                if emitted_name != *binder_name {
                    return Err(to_lean_error(
                        line_file,
                        format!(
                            "To-Lean cannot safely emit the {context} binder `{source_name}` because one occurrence is named `{name}` after SymbolId resolution; preserve one binder spelling before compilation"
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
        ObjToLeanIR::BuiltinApp { arguments, .. } => {
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
        ObjToLeanIR::Collection { items, .. } => {
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
        ObjToLeanIR::Number { .. } | ObjToLeanIR::Constant(_) | ObjToLeanIR::StandardSet(_) => {}
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
    to_lean_error(
        line_file,
        format!(
            "To-Lean cannot safely emit the {context} binder `{binder_name}` because Litex name `{conflicting_name}` also becomes Lean identifier `{emitted_name}`; rename one identifier"
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

fn lean_param_type(param_type: &ParamType) -> Result<&'static str, RuntimeError> {
    match param_type {
        ParamType::Set(_)
        | ParamType::NonemptySet(_)
        | ParamType::FiniteSet(_)
        | ParamType::Obj(_) => Ok("LitexSet"),
    }
}

fn lean_obj(obj: &Obj) -> Result<String, RuntimeError> {
    let ir =
        ObjToLeanIR::lower(obj).map_err(|message| to_lean_error(&default_line_file(), message))?;
    lean_obj_ir(&ir)
}

fn lean_obj_ir(obj: &ObjToLeanIR) -> Result<String, RuntimeError> {
    match obj {
        ObjToLeanIR::Symbol { name, .. } => Ok(lean_name(name)),
        ObjToLeanIR::Number { normalized_value } => {
            if normalized_value
                .chars()
                .all(|character| character.is_ascii_digit() || character == '.')
            {
                Ok(normalized_value.clone())
            } else {
                Ok(format!("litexNumber {:?}", normalized_value))
            }
        }
        ObjToLeanIR::Constant(constant) => Ok(match constant {
            ConstantObjToLeanIR::ImaginaryUnit => "litexI",
            ConstantObjToLeanIR::EulerNumber => "litexE",
            ConstantObjToLeanIR::Pi => "litexPi",
        }
        .to_string()),
        ObjToLeanIR::StandardSet(set) => Ok(match set {
            StandardSetToLeanIR::PositiveNatural => "litexNPos",
            StandardSetToLeanIR::Natural => "litexN",
            StandardSetToLeanIR::Rational => "litexQ",
            StandardSetToLeanIR::Integer => "litexZ",
            StandardSetToLeanIR::Real => "litexR",
            StandardSetToLeanIR::Complex => "litexC",
            StandardSetToLeanIR::PositiveRational => "litexQPos",
            StandardSetToLeanIR::PositiveReal => "litexRPos",
            StandardSetToLeanIR::NegativeRational => "litexQNeg",
            StandardSetToLeanIR::NegativeInteger => "litexZNeg",
            StandardSetToLeanIR::NegativeReal => "litexRNeg",
            StandardSetToLeanIR::NonzeroRational => "litexQStar",
            StandardSetToLeanIR::NonzeroInteger => "litexZStar",
            StandardSetToLeanIR::NonzeroReal => "litexRStar",
            StandardSetToLeanIR::NonzeroComplex => "litexCStar",
        }
        .to_string()),
        ObjToLeanIR::BuiltinApp {
            operator,
            arguments,
        } => lean_builtin_obj_application(*operator, arguments),
        ObjToLeanIR::Collection {
            constructor: CollectionObjToLeanIR::ListSet,
            items,
        } => Ok(format!(
            "litexListSet [{}]",
            items
                .iter()
                .map(lean_obj_ir)
                .collect::<Result<Vec<_>, RuntimeError>>()?
                .join(", ")
        )),
    }
}

fn lean_builtin_obj_application(
    operator: BuiltinObjOperatorToLeanIR,
    arguments: &[ObjToLeanIR],
) -> Result<String, RuntimeError> {
    let rendered = arguments
        .iter()
        .map(lean_obj_ir)
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let expected_arity = match operator {
        BuiltinObjOperatorToLeanIR::Floor
        | BuiltinObjOperatorToLeanIR::Ceil
        | BuiltinObjOperatorToLeanIR::Exp
        | BuiltinObjOperatorToLeanIR::Ln
        | BuiltinObjOperatorToLeanIR::Sign
        | BuiltinObjOperatorToLeanIR::Factorial
        | BuiltinObjOperatorToLeanIR::Abs
        | BuiltinObjOperatorToLeanIR::Sin
        | BuiltinObjOperatorToLeanIR::Cos
        | BuiltinObjOperatorToLeanIR::Tan
        | BuiltinObjOperatorToLeanIR::Cot
        | BuiltinObjOperatorToLeanIR::RealPart
        | BuiltinObjOperatorToLeanIR::ImaginaryPart
        | BuiltinObjOperatorToLeanIR::ComplexAbs
        | BuiltinObjOperatorToLeanIR::Sqrt
        | BuiltinObjOperatorToLeanIR::BigUnion
        | BuiltinObjOperatorToLeanIR::BigIntersect
        | BuiltinObjOperatorToLeanIR::PowerSet => 1,
        _ => 2,
    };
    if rendered.len() != expected_arity {
        return Err(to_lean_error(
            &default_line_file(),
            format!(
                "To-Lean Obj IR operator {:?} expects {} arguments but received {}",
                operator,
                expected_arity,
                rendered.len()
            ),
        ));
    }

    let result = match operator {
        BuiltinObjOperatorToLeanIR::Add => format!("({} + {})", rendered[0], rendered[1]),
        BuiltinObjOperatorToLeanIR::Sub => format!("({} - {})", rendered[0], rendered[1]),
        BuiltinObjOperatorToLeanIR::Mul => format!("({} * {})", rendered[0], rendered[1]),
        BuiltinObjOperatorToLeanIR::Div => format!("({} / {})", rendered[0], rendered[1]),
        BuiltinObjOperatorToLeanIR::Pow => format!("({} ^ {})", rendered[0], rendered[1]),
        BuiltinObjOperatorToLeanIR::Mod => named_binary("litexMod", &rendered),
        BuiltinObjOperatorToLeanIR::Gcd => named_binary("litexGcd", &rendered),
        BuiltinObjOperatorToLeanIR::Lcm => named_binary("litexLcm", &rendered),
        BuiltinObjOperatorToLeanIR::Floor => named_unary("litexFloor", &rendered),
        BuiltinObjOperatorToLeanIR::Ceil => named_unary("litexCeil", &rendered),
        BuiltinObjOperatorToLeanIR::Min => named_binary("litexMin", &rendered),
        BuiltinObjOperatorToLeanIR::Max => named_binary("litexMax", &rendered),
        BuiltinObjOperatorToLeanIR::Exp => named_unary("litexExp", &rendered),
        BuiltinObjOperatorToLeanIR::Ln => named_unary("litexLn", &rendered),
        BuiltinObjOperatorToLeanIR::Sign => named_unary("litexSign", &rendered),
        BuiltinObjOperatorToLeanIR::Factorial => named_unary("litexFactorial", &rendered),
        BuiltinObjOperatorToLeanIR::Abs => named_unary("litexAbs", &rendered),
        BuiltinObjOperatorToLeanIR::Sin => named_unary("litexSin", &rendered),
        BuiltinObjOperatorToLeanIR::Cos => named_unary("litexCos", &rendered),
        BuiltinObjOperatorToLeanIR::Tan => named_unary("litexTan", &rendered),
        BuiltinObjOperatorToLeanIR::Cot => named_unary("litexCot", &rendered),
        BuiltinObjOperatorToLeanIR::RealPart => named_unary("litexRealPart", &rendered),
        BuiltinObjOperatorToLeanIR::ImaginaryPart => named_unary("litexImaginaryPart", &rendered),
        BuiltinObjOperatorToLeanIR::ComplexAbs => named_unary("litexComplexAbs", &rendered),
        BuiltinObjOperatorToLeanIR::Sqrt => named_unary("litexSqrt", &rendered),
        BuiltinObjOperatorToLeanIR::Log => named_binary("litexLog", &rendered),
        BuiltinObjOperatorToLeanIR::Union => named_binary("litexUnion", &rendered),
        BuiltinObjOperatorToLeanIR::Intersect => named_binary("litexIntersect", &rendered),
        BuiltinObjOperatorToLeanIR::SetMinus => named_binary("litexSetMinus", &rendered),
        BuiltinObjOperatorToLeanIR::SetDiff => named_binary("litexSetDiff", &rendered),
        BuiltinObjOperatorToLeanIR::BigUnion => named_unary("litexBigUnion", &rendered),
        BuiltinObjOperatorToLeanIR::BigIntersect => named_unary("litexBigIntersect", &rendered),
        BuiltinObjOperatorToLeanIR::PowerSet => named_unary("litexPowerSet", &rendered),
    };
    Ok(result)
}

fn named_unary(name: &str, arguments: &[String]) -> String {
    format!("{} {}", name, arguments[0])
}

fn named_binary(name: &str, arguments: &[String]) -> String {
    format!("{} {} {}", name, arguments[0], arguments[1])
}

fn lean_rational_builtin_proof(
    proposition: &Fact,
    context: &LeanProofContext,
) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = proposition else {
        return Err(to_lean_error(
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
    let (view_lines, real_equalities) = lean_real_view_lines(context);
    lines.extend(view_lines);
    let mut rewrite_targets = context.nonzero_names.clone();
    rewrite_targets.push("⊢".to_string());
    lines.push(format!(
        "  simp only [{}] at {}",
        litex_real_view_simp(&real_equalities),
        rewrite_targets.join(" ")
    ));
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
        return Err(to_lean_error(
            &goal.line_file(),
            "fact normalization currently requires atomic source and target facts",
        ));
    };
    if source.key() != goal.key() || source.is_true() != goal.is_true() {
        return Err(to_lean_error(
            &goal.line_file(),
            "fact normalization source and target have different proposition shapes",
        ));
    }

    let source_args = source.args_ref();
    let goal_args = goal.args_ref();
    if source_args.len() != goal_args.len() {
        return Err(to_lean_error(
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
        if !objs_equal_by_rational_expression_evaluation(source_arg, goal_arg) {
            return Err(to_lean_error(
                &goal.line_file(),
                format!(
                    "fact normalization argument `{}` is not rationally equal to `{}`",
                    source_arg, goal_arg
                ),
            ));
        }
        changed = true;
        all_closed &=
            closed_rational_expression(source_arg) && closed_rational_expression(goal_arg);
        has_denominator |= LeanRationalExpression::from_obj(source_arg)?.has_denominator()
            || LeanRationalExpression::from_obj(goal_arg)?.has_denominator();
    }

    if !changed {
        return Ok("rfl".to_string());
    }
    if all_closed {
        return Ok(format!("norm_num [{}]", LITEX_REAL_VIEW_SIMP));
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

fn lean_real_set_nonempty(proposition: &Fact) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) = proposition else {
        return Err(to_lean_error(
            &proposition.line_file(),
            "real-set nonemptiness evidence was attached to a different fact family",
        ));
    };
    if !matches!(fact.set, Obj::StandardSet(StandardSet::R)) {
        return Err(to_lean_error(
            &proposition.line_file(),
            "real-set nonemptiness evidence was attached to a non-real carrier",
        ));
    }
    Ok("by\n  change ∃ element : LitexSet, element ∈ litexR\n  refine ⟨0, ?_⟩\n  change True\n  trivial".to_string())
}

fn validate_object_choice(choice: &ObjectChoiceToLeanIR) -> Result<FactId, RuntimeError> {
    if choice.nonempty_proof.fact_id.is_some() {
        return Err(to_lean_error(
            &choice.nonempty_proof.proposition.line_file(),
            "object-choice nonemptiness proof must be a verification-only node",
        ));
    }
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) =
        &choice.nonempty_proof.proposition
    else {
        return Err(to_lean_error(
            &choice.nonempty_proof.proposition.line_file(),
            "object-choice source is not a nonempty-set fact",
        ));
    };
    let nonempty_carrier = ObjToLeanIR::lower(&nonempty.set).map_err(|message| {
        to_lean_error(&choice.nonempty_proof.proposition.line_file(), message)
    })?;
    if nonempty_carrier != choice.carrier {
        return Err(to_lean_error(
            &choice.nonempty_proof.proposition.line_file(),
            "object-choice nonemptiness proof does not match its selected carrier",
        ));
    }

    let FactProofToLeanIR::ObjectChoice {
        definition,
        carrier,
    } = &choice.membership.proof
    else {
        return Err(to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership has no choice-introduction evidence",
        ));
    };
    if definition != &choice.name || carrier != &choice.carrier {
        return Err(to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership evidence does not match its definition",
        ));
    }
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = &choice.membership.proposition else {
        return Err(to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice stored fact is not a membership fact",
        ));
    };
    let membership_carrier = ObjToLeanIR::lower(&membership.set)
        .map_err(|message| to_lean_error(&choice.membership.proposition.line_file(), message))?;
    if membership_carrier != choice.carrier {
        return Err(to_lean_error(
            &choice.membership.proposition.line_file(),
            "object-choice membership uses a different carrier",
        ));
    }
    let selected = ObjToLeanIR::lower(&membership.element)
        .map_err(|message| to_lean_error(&choice.membership.proposition.line_file(), message))?;
    if !matches!(
        selected,
        ObjToLeanIR::Symbol { symbol_id, .. } if symbol_id == choice.symbol_id
    ) {
        return Err(to_lean_error(
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
    ir: &HaveExistentialWitnessToLeanIR,
) -> Result<ExistentialEliminationLayout, RuntimeError> {
    if ir.source.fact_id.is_some() {
        return Err(to_lean_error(
            &ir.source.proposition.line_file(),
            "existential-elimination source must be a verification-only node",
        ));
    }
    let Fact::ExistFact(ExistFactEnum::ExistFact(body)) = &ir.source.proposition else {
        return Err(to_lean_error(
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
        return Err(to_lean_error(
            &ir.source.proposition.line_file(),
            "existential-elimination witness or projection count does not match its source",
        ));
    }

    let mut symbol_ids = HashSet::new();
    for (witness, source_type) in ir.witnesses.iter().zip(param_types.iter()) {
        if !symbol_ids.insert(witness.symbol_id) {
            return Err(to_lean_error(
                &ir.source.proposition.line_file(),
                "existential-elimination witness symbols must be distinct",
            ));
        }
        let family_matches = matches!(
            (source_type, &witness.param_type),
            (ParamType::Set(_), ParamTypeToLeanIR::LitexSet)
                | (
                    ParamType::NonemptySet(_),
                    ParamTypeToLeanIR::LitexNonemptySet
                )
                | (ParamType::FiniteSet(_), ParamTypeToLeanIR::LitexFiniteSet)
                | (ParamType::Obj(_), ParamTypeToLeanIR::MemberOf(_))
        );
        if !family_matches {
            return Err(to_lean_error(
                &ir.source.proposition.line_file(),
                "existential-elimination witness type family does not match its source binder",
            ));
        }
    }

    let mut fact_ids = HashSet::new();
    for (index, projection) in ir.projections.iter().enumerate() {
        let fact_id = required_fact_id(projection)?;
        if !fact_ids.insert(fact_id) {
            return Err(to_lean_error(
                &projection.proposition.line_file(),
                "existential-elimination projection FactIds must be distinct",
            ));
        }
        let FactProofToLeanIR::ExistentialElimination {
            source_proposition,
            role,
            expected_proposition,
        } = &projection.proof
        else {
            return Err(to_lean_error(
                &projection.proposition.line_file(),
                "existential projection has no elimination evidence",
            ));
        };
        if source_proposition.to_string() != ir.source.proposition.to_string() {
            return Err(to_lean_error(
                &projection.proposition.line_file(),
                "existential projection cites a different source proposition",
            ));
        }
        if expected_proposition.to_string() != projection.proposition.to_string() {
            return Err(to_lean_error(
                &projection.proposition.line_file(),
                "existential projection disagrees with its retained expected proposition",
            ));
        }
        if index < ir.witnesses.len() {
            let expected_role = ExistentialProjectionRoleToLeanIR::ParameterType {
                witness_index: index,
            };
            if *role != expected_role {
                return Err(to_lean_error(
                    &projection.proposition.line_file(),
                    "existential type projections are not in witness order",
                ));
            }
            validate_existential_type_projection(&ir.witnesses[index], &projection.proposition)?;
        } else {
            let body_index = index - ir.witnesses.len();
            let expected_role = ExistentialProjectionRoleToLeanIR::BodyFact { body_index };
            if *role != expected_role {
                return Err(to_lean_error(
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
        return Err(to_lean_error(
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
        return Err(to_lean_error(
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
        return Err(to_lean_error(
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
    witness: &ExistentialWitnessToLeanIR,
    proposition: &Fact,
) -> Result<(), RuntimeError> {
    let selected_matches = |obj: &Obj| {
        matches!(
            ObjToLeanIR::lower(obj),
            Ok(ObjToLeanIR::Symbol { symbol_id, .. }) if symbol_id == witness.symbol_id
        )
    };
    let valid = match (&witness.param_type, proposition) {
        (ParamTypeToLeanIR::LitexSet, Fact::AtomicFact(AtomicFact::IsSetFact(fact))) => {
            selected_matches(&fact.set)
        }
        (
            ParamTypeToLeanIR::LitexNonemptySet,
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)),
        ) => selected_matches(&fact.set),
        (
            ParamTypeToLeanIR::LitexFiniteSet,
            Fact::AtomicFact(AtomicFact::IsFiniteSetFact(fact)),
        ) => selected_matches(&fact.set),
        (ParamTypeToLeanIR::MemberOf(carrier), Fact::AtomicFact(AtomicFact::InFact(fact))) => {
            selected_matches(&fact.element)
                && ObjToLeanIR::lower(&fact.set).is_ok_and(|actual| actual == carrier.clone())
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(to_lean_error(
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
    let witness_ir = ObjToLeanIR::lower(witness)
        .map_err(|message| to_lean_error(&proposition.line_file(), message))?;
    let object_matches =
        |obj: &Obj| ObjToLeanIR::lower(obj).is_ok_and(|candidate| candidate == witness_ir);
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
        Err(to_lean_error(
            &proposition.line_file(),
            "existential-introduction parameter proof has the wrong fact family or witness",
        ))
    }
}

fn required_fact_id(fact: &FactToLeanIR) -> Result<FactId, RuntimeError> {
    fact.fact_id.ok_or_else(|| {
        to_lean_error(
            &fact.proposition.line_file(),
            "a top-level stored fact reached To-Lean without a FactId",
        )
    })
}

fn lean_global_fact_name(fact_id: FactId) -> String {
    format!("global_fact_{}", fact_id.value())
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

fn real_membership_proof(fact: &Fact, name: &str) -> Option<(Obj, String)> {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = fact else {
        return None;
    };
    match membership.set {
        Obj::StandardSet(StandardSet::R) => Some((membership.element.clone(), name.to_string())),
        Obj::StandardSet(StandardSet::RPos) => Some((
            membership.element.clone(),
            format!("(litexMemRPosReal {})", name),
        )),
        _ => None,
    }
}

fn lean_real_view_lines(context: &LeanProofContext) -> (Vec<String>, Vec<String>) {
    let mut lines = Vec::with_capacity(context.real_memberships.len());
    let mut equalities = Vec::with_capacity(context.real_memberships.len());
    for (index, (_, membership_name)) in context.real_memberships.iter().enumerate() {
        let witness = format!("litex_real_value_{}", index + 1);
        let equality = format!("litex_real_eq_{}", index + 1);
        lines.push(format!(
            "  obtain ⟨{}, {}⟩ := litexMemRealElim {}",
            witness, equality, membership_name
        ));
        equalities.push(equality);
    }
    (lines, equalities)
}

fn register_local_fact(fact_id: FactId, fact: &Fact, name: &str, context: &mut LeanProofContext) {
    context.proof_fact_names.insert(fact_id, name.to_string());
    if is_nonzero_fact(fact) && !context.nonzero_names.iter().any(|known| known == name) {
        context.nonzero_names.push(name.to_string());
    }
    if let Some((object, membership_proof)) = real_membership_proof(fact, name) {
        if !context
            .real_memberships
            .iter()
            .any(|(known, _)| obj_equality_key(known) == obj_equality_key(&object))
        {
            context.real_memberships.push((object, membership_proof));
        }
    }
}

fn push_lean_bullet(lines: &mut Vec<String>, body: &[String]) -> Result<(), RuntimeError> {
    let Some((first, rest)) = body.split_first() else {
        return Err(to_lean_error(
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

fn litex_real_view_simp(real_equalities: &[String]) -> String {
    if real_equalities.is_empty() {
        return LITEX_REAL_VIEW_SIMP.to_string();
    }
    format!("{}, {}", real_equalities.join(", "), LITEX_REAL_VIEW_SIMP)
}

const LITEX_REAL_VIEW_SIMP: &str = "litexOfNatEq, litexOfNat, litexOfScientificEq, litexOfScientific, litexAddEq, litexAdd, litexSubEq, litexSub, litexMulEq, litexMul, litexDivEq, litexDiv, litexPowEq, litexPow, litexNegEq, litexNeg, litexLTIff, litexLT, litexLEIff, litexLE, litexRealValueEqIff";

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

fn to_lean_error(line_file: &LineFile, message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}

fn statement_ir_display(statement: &StmtToLeanIR) -> String {
    match statement {
        StmtToLeanIR::AbstractProp(ir) => format!("abstract_prop {}", ir.name),
        StmtToLeanIR::Prop(ir) => format!("prop {}", ir.name),
        StmtToLeanIR::HaveObjChoice(ir) => format!(
            "have {} <by checked choice>",
            ir.choices
                .iter()
                .map(|choice| choice.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        StmtToLeanIR::HaveObjEqual(ir) => format!(
            "have {} = <value>",
            ir.definitions
                .iter()
                .map(|definition| definition.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
        StmtToLeanIR::HaveExistentialWitness(ir) => format!(
            "obtain {} from {}",
            ir.witnesses
                .iter()
                .map(|witness| witness.name.as_str())
                .collect::<Vec<_>>()
                .join(", "),
            ir.source.proposition
        ),
        StmtToLeanIR::Proof(ir) => match ir.facts.first() {
            Some(fact) if ir.facts.len() == 1 => fact.proposition.to_string(),
            Some(_) => format!("proof <{} facts>", ir.facts.len()),
            None => "proof <empty>".to_string(),
        },
        StmtToLeanIR::Trust(ir) => match ir.facts.first() {
            Some(fact) if ir.facts.len() == 1 => format!("trust {}", fact.proposition),
            Some(_) => format!("trust <{} facts>", ir.facts.len()),
            None => "trust <empty>".to_string(),
        },
        StmtToLeanIR::Fact(ir) => ir.fact.proposition.to_string(),
    }
}

fn statement_ir_line_file(statement: &StmtToLeanIR) -> LineFile {
    match statement {
        StmtToLeanIR::AbstractProp(_) => default_line_file(),
        StmtToLeanIR::Prop(ir) => ir
            .iff_facts
            .first()
            .map(Fact::line_file)
            .unwrap_or_else(default_line_file),
        StmtToLeanIR::HaveObjChoice(ir) => ir
            .choices
            .first()
            .map(|choice| choice.membership.proposition.line_file())
            .unwrap_or_else(default_line_file),
        StmtToLeanIR::HaveObjEqual(ir) => ir
            .facts
            .first()
            .map(|fact| fact.proposition.line_file())
            .unwrap_or_else(default_line_file),
        StmtToLeanIR::HaveExistentialWitness(ir) => ir.source.proposition.line_file(),
        StmtToLeanIR::Proof(ir) => ir
            .facts
            .first()
            .map(|fact| fact.proposition.line_file())
            .unwrap_or_else(default_line_file),
        StmtToLeanIR::Trust(ir) => ir
            .facts
            .first()
            .map(|fact| fact.proposition.line_file())
            .unwrap_or_else(default_line_file),
        StmtToLeanIR::Fact(ir) => ir.fact.proposition.line_file(),
    }
}

fn lean_comment_text(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::process::Command;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn ordinary_runtime_does_not_return_to_lean_ir() {
        run_with_large_stack("ordinary_runtime_does_not_return_to_lean_ir", || {
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
            assert!(results.iter().all(|result| result.to_lean_ir().is_none()));
            assert!(!runtime.to_lean_mode());
        });
    }

    #[test]
    fn source_identity_selects_the_lean_namespace() {
        run_with_large_stack("source_identity_selects_the_lean_namespace", || {
            let mut standalone_runtime = Runtime::new();
            standalone_runtime
                .new_file_path_new_env_new_name_scope("/virtual/chapter01-introduction.lit");
            let standalone = to_lean("abstract_prop marked(x)", &mut standalone_runtime).unwrap();
            assert!(standalone.contains("\nnamespace chapter01_introduction\n\n"));
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
            let registered = to_lean(
                "prop is_one(x R):\n    x = 1\n\n$is_one(1)",
                &mut registered_runtime,
            )
            .unwrap();
            assert!(registered.contains("\nnamespace A.chap2\n\n"));
            assert!(registered.ends_with("\nend A.chap2\n"));
            assert!(!registered.contains("namespace chapter02"));
            assert!(registered.contains("def is_one (x : LitexSet) : LitexFact :="));
            assert!(registered.contains("simp [is_one]"));

            let anonymous =
                to_lean_from_source("abstract_prop marked(x)", "/virtual/diagnostic-only.lit")
                    .unwrap();
            assert!(!anonymous.contains("\nnamespace "));
        });
    }

    #[test]
    fn to_lean_mode_records_recursive_ir_and_emits_only_trust_as_axiom() {
        run_with_large_stack(
            "to_lean_mode_records_recursive_ir_and_emits_only_trust_as_axiom",
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
                runtime.new_file_path_new_env_new_name_scope("to-lean-ir-mvp.lit");
                let output = to_lean(source, &mut runtime).unwrap();

                assert!(output.starts_with("import Mathlib\n\nnamespace to_lean_ir_mvp\n\n"));
                assert!(output.contains("inductive LitexSet where"));
                assert!(output.contains("abbrev LitexFact := Prop"));
                assert!(
                    output.find("inductive LitexSet").unwrap()
                        < output.find("abbrev LitexFact").unwrap()
                );
                assert!(output.contains("opaque marked : LitexSet → LitexFact"));
                assert!(!output.contains("namespace LitexGenerated"));
                assert!(!output.contains("end LitexGenerated"));
                assert!(!output.lines().any(|line| line == "universe u"));
                assert!(output.ends_with("\nend to_lean_ir_mvp\n"));
                assert!(output.contains("def is_one (x : LitexSet) : LitexFact :="));
                assert_eq!(output.matches("\naxiom global_fact_").count(), 1);
                assert!(output.contains(":= global_fact_"));
                assert!(output.contains("is_one 1"));
                assert!(output.contains("simp [is_one]"));
                assert!(output.contains("let proof_arg_"));
                assert!(output.contains("intro a b x proof_fact_"));
                assert!(output.contains("field_simp [proof_fact_"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn to_lean_statement_scopes_lower_have_cases_and_contra() {
        run_with_large_stack(
            "to_lean_statement_scopes_lower_have_cases_and_contra",
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
                let statement_irs = test_to_lean_ir(source, "statement-scopes-ir.lit");
                assert!(matches!(statement_irs[0], StmtToLeanIR::HaveObjEqual(_)));
                let StmtToLeanIR::Proof(by_cases) = &statement_irs[1] else {
                    panic!("second statement should be proof IR");
                };
                assert!(matches!(
                    by_cases.facts[0].proof,
                    FactProofToLeanIR::CaseSplit { .. }
                ));
                let StmtToLeanIR::Proof(by_contra) = &statement_irs[2] else {
                    panic!("third statement should be proof IR");
                };
                assert!(matches!(
                    by_contra.facts[0].proof,
                    FactProofToLeanIR::ByContradiction { .. }
                ));

                let output = to_lean_from_source(source, "statement-scopes-output").unwrap();
                assert!(output.contains("def x : LitexSet := 2"), "{output}");
                assert!(output.contains("let y : LitexSet := 3"), "{output}");
                assert!(output.contains("simpa only [x] using"), "{output}");
                assert!(output.contains("Classical.em (x = 2)"), "{output}");
                assert!(output.contains("rcases"), "{output}");
                assert!(
                    output.contains("apply Classical.byContradiction"),
                    "{output}"
                );
                assert!(!output.contains("axiom global_fact_"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn to_lean_statement_scopes_reject_malformed_local_premises() {
        run_with_large_stack(
            "to_lean_statement_scopes_reject_malformed_local_premises",
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
                let mut malformed_cases = test_to_lean_ir(source, "malformed-case-assumption.lit");
                let StmtToLeanIR::Proof(by_cases) = &mut malformed_cases[1] else {
                    panic!("second statement should be proof IR");
                };
                let FactProofToLeanIR::CaseSplit { branches, .. } = &mut by_cases.facts[0].proof
                else {
                    panic!("second statement should contain case-split evidence");
                };
                branches[0].assumption.fact = branches[1].assumption.fact.clone();
                let error = emit_lean_from_ir(&malformed_cases)
                    .expect_err("a branch premise that disagrees with coverage must be rejected")
                    .trace_message();
                assert!(
                    error.contains("case-split assumption does not match its coverage branch"),
                    "{error}"
                );

                let mut malformed_contra =
                    test_to_lean_ir(source, "malformed-contra-assumption.lit");
                let StmtToLeanIR::Proof(by_contra) = &mut malformed_contra[2] else {
                    panic!("third statement should be proof IR");
                };
                let target = by_contra.facts[0].proposition.clone();
                let FactProofToLeanIR::ByContradiction {
                    reverse_assumption, ..
                } = &mut by_contra.facts[0].proof
                else {
                    panic!("third statement should contain contradiction evidence");
                };
                reverse_assumption.fact = target;
                let error = emit_lean_from_ir(&malformed_contra)
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
    fn to_lean_choice_have_uses_checked_nonempty_certificate() {
        run_with_large_stack(
            "to_lean_choice_have_uses_checked_nonempty_certificate",
            || {
                let source =
                    include_str!("../../examples/05_compiler_interop/to_lean_choice_have.lit");
                let statement_irs = test_to_lean_ir(source, "choice-have-ir.lit");
                let StmtToLeanIR::HaveObjChoice(top_level_choice) = &statement_irs[0] else {
                    panic!("first statement should be object-choice IR");
                };
                assert_eq!(top_level_choice.choices.len(), 1);
                assert!(matches!(
                    underlying_test_proof(&top_level_choice.choices[0].nonempty_proof.proof),
                    FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::RealSetNonempty,
                        ..
                    }
                ));
                assert!(matches!(
                    top_level_choice.choices[0].membership.proof,
                    FactProofToLeanIR::ObjectChoice { .. }
                ));

                let StmtToLeanIR::Proof(by_contra) = &statement_irs[2] else {
                    panic!("third statement should be proof IR");
                };
                let FactProofToLeanIR::ByContradiction { steps, .. } = &by_contra.facts[0].proof
                else {
                    panic!("third statement should retain contradiction evidence");
                };
                assert!(matches!(steps[0], StmtToLeanIR::HaveObjChoice(_)));

                let output = to_lean_from_source(source, "choice-have-output").unwrap();
                assert!(
                    output.contains("def litexIsNonemptySet (set : LitexSet) : Prop := ∃ element, litexMem element set"),
                    "{output}"
                );
                assert!(output.contains("theorem litex_choice_source_"), "{output}");
                assert!(
                    output.contains("noncomputable def selected : LitexSet := Exists.choose litex_choice_source_"),
                    "{output}"
                );
                assert!(
                    output.contains("let local_choice : LitexSet := Exists.choose proof_fact_"),
                    "{output}"
                );
                assert!(output.contains("Exists.choose_spec"), "{output}");
                assert!(!output.contains("axiom global_fact_"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn to_lean_choice_have_rejects_missing_or_mismatched_evidence() {
        run_with_large_stack(
            "to_lean_choice_have_rejects_missing_or_mismatched_evidence",
            || {
                let source = "have selected R";
                let mut missing = test_to_lean_ir(source, "choice-have-missing-proof.lit");
                let StmtToLeanIR::HaveObjChoice(choice) = &mut missing[0] else {
                    panic!("statement should be object-choice IR");
                };
                choice.choices[0].nonempty_proof.proof = FactProofToLeanIR::Unsupported {
                    reason: "missing checked nonemptiness backend".to_string(),
                };
                let error = emit_lean_from_ir(&missing)
                    .expect_err("choice without a checked nonemptiness backend must fail")
                    .trace_message();
                assert!(
                    error.contains("missing checked nonemptiness backend"),
                    "{error}"
                );

                let mut mismatched = test_to_lean_ir(source, "choice-have-wrong-source.lit");
                let StmtToLeanIR::HaveObjChoice(choice) = &mut mismatched[0] else {
                    panic!("statement should be object-choice IR");
                };
                choice.choices[0].nonempty_proof.proposition =
                    choice.choices[0].membership.proposition.clone();
                let error = emit_lean_from_ir(&mismatched)
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
    fn to_lean_exist_have_uses_checked_introduction_and_projections() {
        run_with_large_stack(
            "to_lean_exist_have_uses_checked_introduction_and_projections",
            || {
                let source =
                    include_str!("../../examples/05_compiler_interop/to_lean_exist_have.lit");
                let statement_irs = test_to_lean_ir(source, "exist-have-ir.lit");
                let StmtToLeanIR::Proof(introduction) = &statement_irs[0] else {
                    panic!("first statement should be existential-introduction proof IR");
                };
                assert!(matches!(
                    introduction.facts[0].proof,
                    FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::ExistIntroduction { .. },
                        ..
                    }
                ));
                let StmtToLeanIR::HaveExistentialWitness(obtain) = &statement_irs[1] else {
                    panic!("second statement should be existential-elimination IR");
                };
                assert_eq!(obtain.witnesses.len(), 1);
                assert_eq!(obtain.projections.len(), 3);
                assert!(matches!(
                    obtain.projections[0].proof,
                    FactProofToLeanIR::ExistentialElimination {
                        role: ExistentialProjectionRoleToLeanIR::ParameterType { witness_index: 0 },
                        ..
                    }
                ));
                assert!(matches!(
                    obtain.projections[2].proof,
                    FactProofToLeanIR::ExistentialElimination {
                        role: ExistentialProjectionRoleToLeanIR::BodyFact { body_index: 1 },
                        ..
                    }
                ));
                assert!(matches!(
                    statement_irs[5],
                    StmtToLeanIR::HaveExistentialWitness(_)
                ));
                let StmtToLeanIR::Proof(by_contra) = &statement_irs[9] else {
                    panic!("last statement should be contradiction proof IR");
                };
                let FactProofToLeanIR::ByContradiction { steps, .. } = &by_contra.facts[0].proof
                else {
                    panic!("last statement should retain contradiction evidence");
                };
                assert!(matches!(steps[0], StmtToLeanIR::HaveExistentialWitness(_)));

                let output = to_lean_from_source(source, "exist-have-output").unwrap();
                assert!(output.contains("∃ source : LitexSet"), "{output}");
                assert!(output.contains("theorem litex_exist_source_"), "{output}");
                assert!(
                    output.contains("noncomputable def selected : LitexSet := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("noncomputable def shorthand : LitexSet := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("let local_selected : LitexSet := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("noncomputable def chosen_left : LitexSet := Exists.choose"),
                    "{output}"
                );
                assert!(
                    output.contains("noncomputable def chosen_right : LitexSet := Exists.choose ("),
                    "{output}"
                );
                assert!(output.contains("Exists.choose_spec"), "{output}");
                assert!(!output.contains("axiom global_fact_"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn to_lean_exist_have_rejects_malformed_evidence() {
        run_with_large_stack("to_lean_exist_have_rejects_malformed_evidence", || {
            let source = include_str!("../../examples/05_compiler_interop/to_lean_exist_have.lit");
            let mut malformed_projection = test_to_lean_ir(source, "exist-wrong-projection.lit");
            let StmtToLeanIR::HaveExistentialWitness(obtain) = &mut malformed_projection[1] else {
                panic!("second statement should be existential-elimination IR");
            };
            let FactProofToLeanIR::ExistentialElimination {
                expected_proposition,
                ..
            } = &mut obtain.projections[0].proof
            else {
                panic!("first projection should contain elimination evidence");
            };
            *expected_proposition = obtain.source.proposition.clone();
            let error = emit_lean_from_ir(&malformed_projection)
                .expect_err("a mismatched existential projection must be rejected")
                .trace_message();
            assert!(
                error.contains("disagrees with its retained expected proposition"),
                "{error}"
            );

            let mut malformed_introduction =
                test_to_lean_ir(source, "exist-wrong-introduction.lit");
            let StmtToLeanIR::Proof(introduction) = &mut malformed_introduction[0] else {
                panic!("first statement should be proof IR");
            };
            let wrong_body = introduction.facts[0].proposition.clone();
            let FactProofToLeanIR::RuleApplication {
                rule:
                    ProofRuleToLeanIR::ExistIntroduction {
                        expected_body_facts,
                        ..
                    },
                ..
            } = &mut introduction.facts[0].proof
            else {
                panic!("first proof should contain existential-introduction evidence");
            };
            expected_body_facts[0] = wrong_body;
            let error = emit_lean_from_ir(&malformed_introduction)
                .expect_err("mismatched existential-introduction evidence must be rejected")
                .trace_message();
            assert!(
                error.contains("body evidence disagrees with its retained proposition"),
                "{error}"
            );

            let mut malformed_alpha = test_to_lean_ir(source, "exist-wrong-alpha-source.lit");
            let StmtToLeanIR::HaveExistentialWitness(obtain) = &mut malformed_alpha[1] else {
                panic!("second statement should be existential-elimination IR");
            };
            let wrong_source = obtain.projections[0].proposition.clone();
            let FactProofToLeanIR::ExistentialAlphaRenameCitation {
                source_proposition, ..
            } = underlying_test_proof_mut(&mut obtain.source.proof)
            else {
                panic!("source proof should retain alpha-renaming evidence");
            };
            *source_proposition = wrong_source;
            let error = emit_lean_from_ir(&malformed_alpha)
                .expect_err("a non-existential alpha source must be rejected")
                .trace_message();
            assert!(
                error.contains("requires two positive `exist` facts"),
                "{error}"
            );
        });
    }

    #[test]
    fn to_lean_exist_have_rejects_sanitized_binder_capture() {
        run_with_large_stack(
            "to_lean_exist_have_rejects_sanitized_binder_capture",
            || {
                let source = r#"
prop captured(xα set):
    exist xβ xα st {xβ = xβ}
"#;
                let error = to_lean_from_source(source, "exist-name-capture.lit")
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
    fn to_lean_statement_scope_boundaries_remain_explicit() {
        run_with_large_stack("to_lean_statement_scope_boundaries_remain_explicit", || {
            let selection = to_lean_from_source_with_report(
                "have arbitrary_nonempty_set nonempty_set",
                "unsupported-meta-selection-have",
            )
            .unwrap();
            assert_eq!(selection.status, ToLeanCompilationStatus::Incomplete);
            assert_eq!(selection.unsupported.len(), 1);
            assert!(selection.unsupported[0]
                .reason
                .contains("meta-level parameter type `nonempty_set`"));

            let unsupported_value_check = to_lean_from_source_with_report(
                "have carrier set = R",
                "unsupported-have-value-check",
            )
            .unwrap();
            assert_eq!(
                unsupported_value_check.status,
                ToLeanCompilationStatus::Incomplete
            );
            assert_eq!(unsupported_value_check.unsupported.len(), 1);
            assert!(unsupported_value_check.unsupported[0]
                .reason
                .contains("Every object is a set"));
            assert!(!unsupported_value_check.lean_code.contains("def carrier"));
            assert!(!unsupported_value_check.lean_code.contains("sorry"));

            let proof_step = to_lean_from_source_with_report(
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
            assert_eq!(proof_step.status, ToLeanCompilationStatus::Incomplete);
            assert_eq!(proof_step.unsupported.len(), 1);
            assert!(proof_step.unsupported[0].reason.contains("DoNothingStmt"));
            assert!(!proof_step.lean_code.contains("sorry"));
            assert!(!proof_step.lean_code.contains("axiom global_fact_"));

            let preimage = to_lean_from_source_with_report(
                r#"
have fn square(x R) R = x^2
square(2) $in fn_range(square)
have by preimage root from square(2) $in fn_range(square)
"#,
                "unsupported-function-preimage",
            )
            .unwrap();
            assert_eq!(preimage.status, ToLeanCompilationStatus::Incomplete);
            assert!(preimage
                .unsupported
                .iter()
                .any(|item| item.reason.contains("HaveFnEqualStmt")));
            assert!(preimage
                .unsupported
                .iter()
                .any(|item| item.reason.contains("HaveByPreimageStmt")));
            assert!(!preimage.lean_code.contains("sorry"));
            assert!(!preimage.lean_code.contains("axiom global_fact_"));
        });
    }

    #[test]
    fn to_lean_ir_preserves_fact_ids_and_verified_routes() {
        run_with_large_stack("to_lean_ir_preserves_fact_ids_and_verified_routes", || {
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
            runtime.new_file_path_new_env_new_name_scope("to-lean-ir-shape");
            runtime.replace_to_lean_mode(true);
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .unwrap();
            let mut statement_irs = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).unwrap();
                let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                statement_irs.push(result.to_lean_ir().unwrap().clone());
            }

            assert!(matches!(statement_irs[0], StmtToLeanIR::AbstractProp(_)));
            assert!(matches!(statement_irs[1], StmtToLeanIR::Prop(_)));
            let StmtToLeanIR::Trust(trust) = &statement_irs[2] else {
                panic!("third IR item should be trust");
            };
            let trusted_forall_id = trust.facts[0]
                .fact_id
                .expect("trusted fact must have an ID");
            assert!(matches!(trust.facts[0].proof, FactProofToLeanIR::Trusted));

            let StmtToLeanIR::Fact(by_definition) = &statement_irs[3] else {
                panic!("fourth IR item should be a fact");
            };
            assert!(matches!(
                underlying_test_proof(&by_definition.fact.proof),
                FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::DefinitionReduction { definition },
                    ..
                } if definition == "is_one"
            ));

            let StmtToLeanIR::Fact(local_requirement_forall) = &statement_irs[4] else {
                panic!("fifth IR item should be a forall fact");
            };
            let FactProofToLeanIR::ForallIntroduction {
                premises,
                conclusions,
                ..
            } = &local_requirement_forall.fact.proof
            else {
                panic!("sixth fact should retain forall-introduction evidence");
            };
            assert_eq!(premises.len(), 2);
            let local_nonzero_id = premises[0].fact_id;
            let FactProofToLeanIR::RuleApplication {
                rule: ProofRuleToLeanIR::KnownForallInstantiation { source_fact_id, .. },
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
                FactProofToLeanIR::KnownFactCitation { source_fact_id }
                    if *source_fact_id == local_nonzero_id
            ));

            let StmtToLeanIR::Fact(forall) = &statement_irs[5] else {
                panic!("sixth IR item should be a fact");
            };
            let FactProofToLeanIR::ForallIntroduction {
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
                FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::Normalization {
                        kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
                    },
                    ..
                }
            ));
        });
    }

    #[test]
    fn to_lean_builtin_rule_ir_preserves_recursive_evidence() {
        run_with_large_stack(
            "to_lean_builtin_rule_ir_preserves_recursive_evidence",
            || {
                let source = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
"#;
                let statement_irs = test_to_lean_ir(source, "builtin-rule-ir-shape");
                let StmtToLeanIR::Fact(forall) = &statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction {
                    premises,
                    conclusions,
                    ..
                } = &forall.fact.proof
                else {
                    panic!("tracer should retain its temporary forall environment");
                };
                assert_eq!(premises.len(), 2);
                assert_eq!(conclusions.len(), 1);

                let FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::DivNotEqualZero(evidence)),
                    parameter_requirements,
                    premises: rule_premises,
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("forall conclusion should retain typed div-nonzero evidence");
                };
                assert!(parameter_requirements.is_empty());
                let Fact::AtomicFact(AtomicFact::NotEqualFact(target)) =
                    &conclusions[0].proposition
                else {
                    panic!("tracer conclusion should remain a non-equality fact");
                };
                let Obj::Div(quotient) = &target.left else {
                    panic!("tracer conclusion should retain its quotient");
                };
                assert_eq!(
                    obj_equality_key(&evidence.numerator),
                    obj_equality_key(quotient.left.as_ref())
                );
                assert_eq!(
                    obj_equality_key(&evidence.denominator),
                    obj_equality_key(quotient.right.as_ref())
                );
                assert_eq!(
                    evidence.orientation,
                    NonzeroExpressionOrientationToLeanIR::ExpressionOnLeft
                );
                assert_eq!(rule_premises.len(), 2);
                for (rule_premise, local_premise) in rule_premises.iter().zip(premises.iter()) {
                    assert!(matches!(
                        underlying_test_proof(&rule_premise.proof),
                        FactProofToLeanIR::KnownFactCitation { source_fact_id }
                            if *source_fact_id == local_premise.fact_id
                    ));
                }
            },
        );
    }

    #[test]
    fn to_lean_builtin_rule_ir_emits_checked_lemma_application() {
        run_with_large_stack(
            "to_lean_builtin_rule_ir_emits_checked_lemma_application",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_builtin_rule_ir.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(&path.to_string_lossy());
                let output = to_lean(&source, &mut runtime).unwrap();

                assert!(output.contains("namespace to_lean_builtin_rule_ir"));
                assert!(output.contains("div_ne_zero proof_fact_"));
                assert!(output.contains("have proof_fact_"));
                assert!(!output.contains("OtherUnsupported"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn to_lean_builtin_rule_ir_preserves_reverse_orientation() {
        run_with_large_stack(
            "to_lean_builtin_rule_ir_preserves_reverse_orientation",
            || {
                let source = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        0 != a / b
"#;
                let output = to_lean_from_source(source, "builtin-rule-reverse").unwrap();
                assert!(output.contains("Ne.symm (div_ne_zero proof_fact_"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn to_lean_builtin_rule_ir_rejects_malformed_certificate() {
        run_with_large_stack(
            "to_lean_builtin_rule_ir_rejects_malformed_certificate",
            || {
                let source = r#"
forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
"#;
                let mut statement_irs = test_to_lean_ir(source, "builtin-rule-invalid-ir");
                let StmtToLeanIR::Fact(forall) = &mut statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                let FactProofToLeanIR::RuleApplication { premises, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("tracer conclusion should be a rule application");
                };
                premises.pop();

                let error = emit_lean_from_ir(&statement_irs)
                    .expect_err("malformed builtin certificate must stop emission")
                    .trace_message();
                assert!(error.contains("expected 2 premises but received 1"));
            },
        );
    }

    #[test]
    fn to_lean_builtin_rule_ir_rejects_resolved_zero_without_equality_evidence() {
        run_with_large_stack(
            "to_lean_builtin_rule_ir_rejects_resolved_zero_without_equality_evidence",
            || {
                let source = r#"
forall a, b, z R:
    z = 0
    a != 0
    b != 0
    =>:
        a / b != z
"#;
                let error = to_lean_from_source(source, "builtin-rule-resolved-zero")
                    .expect_err("a resolved zero alias lacks compiler equality evidence")
                    .trace_message();
                assert!(error.contains("no checked backend"));
                assert!(error.contains("div_not_equal_zero_from_numerator_nonzero"));
            },
        );
    }

    #[test]
    fn to_lean_builtin_rules_20_preserve_distinct_typed_rules_and_compile() {
        run_with_large_stack(
            "to_lean_builtin_rules_20_preserve_distinct_typed_rules_and_compile",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_builtin_rules_20.lit");
                let source = fs::read_to_string(&path).unwrap();
                let statement_irs = test_to_lean_ir(&source, "builtin-rules-20-ir");
                let mut rule_names = Vec::new();
                for statement in statement_irs.iter() {
                    let StmtToLeanIR::Fact(forall) = statement else {
                        panic!("each tracer statement should be a stored forall fact");
                    };
                    let FactProofToLeanIR::ForallIntroduction { conclusions, .. } =
                        &forall.fact.proof
                    else {
                        panic!("each tracer statement should retain forall evidence");
                    };
                    let FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::Arithmetic(rule)),
                        ..
                    } = underlying_test_proof(&conclusions[0].proof)
                    else {
                        panic!("each tracer conclusion should retain typed arithmetic evidence");
                    };
                    rule_names.push(format!("{:?}", rule));
                }
                rule_names.sort();
                rule_names.dedup();
                assert_eq!(rule_names.len(), 20, "{rule_names:#?}");

                let output = emit_lean_from_ir(&statement_irs).unwrap();
                assert_eq!(output.matches("theorem global_fact_").count(), 20);
                assert_eq!(output.matches("linarith only").count(), 16);
                assert!(output.contains("mul_nonneg proof_fact_"));
                assert!(output.contains("mul_pos proof_fact_"));
                assert!(output.contains("div_nonneg proof_fact_"));
                assert!(output.contains("div_pos proof_fact_"));
                assert!(!output.contains("axiom"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn to_lean_builtin_rules_20_reject_malformed_premise_arity() {
        run_with_large_stack(
            "to_lean_builtin_rules_20_reject_malformed_premise_arity",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_builtin_rules_20.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut statement_irs = test_to_lean_ir(&source, "builtin-rules-20-malformed");
                let StmtToLeanIR::Fact(forall) = &mut statement_irs[0] else {
                    panic!("first tracer statement should be a stored forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("first tracer statement should retain forall evidence");
                };
                let FactProofToLeanIR::RuleApplication { premises, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("first tracer conclusion should be a rule application");
                };
                premises.clear();

                let error = emit_lean_from_ir(&statement_irs)
                    .expect_err("malformed arithmetic evidence must stop strict emission")
                    .trace_message();
                assert!(error.contains("expected 1 premises but received 0"));
            },
        );
    }

    #[test]
    fn to_lean_recursive_strategy_ir_preserves_typed_tree_and_compiles() {
        run_with_large_stack(
            "to_lean_recursive_strategy_ir_preserves_typed_tree_and_compiles",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_recursive_strategy_ir.lit");
                let source = fs::read_to_string(&path).unwrap();
                let statement_irs = test_to_lean_ir(&source, "recursive-strategy-ir");
                let StmtToLeanIR::Fact(forall) = &statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction {
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
                    FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::Builtin(
                            BuiltinRuleToLeanIR::PositiveRealMembership
                        ),
                        ..
                    }
                )));
                let FactProofToLeanIR::RuleApplication {
                    rule:
                        ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::Arithmetic(
                            ArithmeticBuiltinRuleToLeanIR::AddPositiveLeftStrict,
                        )),
                    premises: outer_premises,
                    ..
                } = underlying_test_proof(&conclusions[0].proof)
                else {
                    panic!("outer strategy should lower to typed strict-addition evidence");
                };
                assert_eq!(outer_premises.len(), 2);

                assert!(matches!(
                    underlying_test_proof(&outer_premises[0].proof),
                    FactProofToLeanIR::RuleApplication {
                        rule: ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::Arithmetic(
                            ArithmeticBuiltinRuleToLeanIR::AddPositive
                        )),
                        premises,
                        ..
                    } if premises.len() == 2
                ));

                let FactProofToLeanIR::RuleApplication {
                    rule:
                        ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::Arithmetic(
                            ArithmeticBuiltinRuleToLeanIR::AddNonnegative,
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
                        FactProofToLeanIR::RuleApplication {
                            rule: ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::Arithmetic(
                                ArithmeticBuiltinRuleToLeanIR::LessEqualFromStrictOrder
                            )),
                            premises,
                            ..
                        } if premises.len() == 1
                            && matches!(
                                underlying_test_proof(&premises[0].proof),
                                FactProofToLeanIR::KnownFactCitation { .. }
                            )
                    ));
                }

                let output = emit_lean_from_ir(&statement_irs).unwrap();
                assert!(output.contains("linarith only"), "{output}");
                assert!(!output.contains("OtherUnsupported"), "{output}");
                assert!(!output.contains("axiom"), "{output}");
                assert!(!output.contains("sorry"), "{output}");
            },
        );
    }

    #[test]
    fn to_lean_recursive_strategy_ir_rejects_malformed_certificate() {
        run_with_large_stack(
            "to_lean_recursive_strategy_ir_rejects_malformed_certificate",
            || {
                let source = include_str!(
                    "../../examples/05_compiler_interop/to_lean_recursive_strategy_ir.lit"
                );
                let mut statement_irs = test_to_lean_ir(source, "recursive-strategy-malformed");
                let StmtToLeanIR::Fact(forall) = &mut statement_irs[0] else {
                    panic!("tracer should produce one stored forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction { conclusions, .. } =
                    &mut forall.fact.proof
                else {
                    panic!("tracer should retain forall-introduction evidence");
                };
                let FactProofToLeanIR::RuleApplication { rule, .. } =
                    underlying_test_proof_mut(&mut conclusions[0].proof)
                else {
                    panic!("outer strategy should be a rule application");
                };
                *rule = ProofRuleToLeanIR::Builtin(BuiltinRuleToLeanIR::Arithmetic(
                    ArithmeticBuiltinRuleToLeanIR::AddPositiveRightStrict,
                ));

                let error = emit_lean_from_ir(&statement_irs)
                    .expect_err("a strategy certificate with the wrong premise order must fail")
                    .trace_message();
                assert!(error.contains("premise 1 expected WeakOrder"), "{error}");
            },
        );
    }

    #[test]
    fn to_lean_non_additive_structural_strategy_remains_explicitly_unsupported() {
        run_with_large_stack(
            "to_lean_non_additive_structural_strategy_remains_explicitly_unsupported",
            || {
                let source = r#"
forall x, y R:
    x^2 < y^2
    =>:
        abs(x) < abs(y)
"#;
                let error = to_lean_from_source(source, "unsupported-structural-strategy")
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
            let output = to_lean_from_source("1 / 2 / 3 / 4 = 1 / 24", "closed-ir").unwrap();

            assert!(output.contains("theorem global_fact_1"));
            assert!(output.contains(
                "-- native proof view, left fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))"
            ));
            assert!(output.contains("norm_num"));
            assert!(!output.contains("sorry"));
        });
    }

    #[test]
    fn temporary_forall_premise_is_emitted_as_local_exact() {
        run_with_large_stack("temporary_forall_premise_is_emitted_as_local_exact", || {
            let output = to_lean_from_source(
                "forall x R:\n    x != 0\n    =>:\n        x != 0",
                "temporary-local-fact",
            )
            .unwrap();

            assert!(output.contains("intro x proof_fact_1_1 proof_fact_1_2"));
            assert!(output.contains("exact proof_fact_1_2"));
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
                let output = to_lean_from_source(source, "local-proof-spaces").unwrap();

                assert_eq!(output.matches("\ntheorem global_fact_").count(), 2);
                assert!(output.contains("intro x proof_fact_1_1 proof_fact_1_2"));
                assert!(output.contains("exact proof_fact_1_2"));
                assert!(output.contains("intro y proof_fact_2_1 proof_fact_2_2"));
                assert!(output.contains("exact proof_fact_2_2"));
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
                runtime.replace_to_lean_mode(true);
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
                    statement_irs.push(result.to_lean_ir().unwrap().clone());
                }

                let StmtToLeanIR::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction {
                    premises: local_premises,
                    conclusions,
                    ..
                } = &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::EqualityRewrite(rewrite),
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
                    EqualityRewriteDirectionToLeanIR::Forward
                );
                assert!(rewrite_premises.iter().all(|premise| {
                    premise.fact_id.is_some_and(|fact_id| {
                        local_premises.iter().any(|local| local.fact_id == fact_id)
                    })
                }));

                let output = to_lean_from_source(source, "equality-transport-output").unwrap();
                assert!(output
                    .contains("intro a b proof_fact_1_1 proof_fact_1_2\n  have proof_fact_1_3"));
                assert!(output.contains("have proof_fact_1_3 : p a := proof_fact_1_1"));
                assert!(output.contains("have proof_fact_1_4 : a = b := proof_fact_1_2"));
                assert!(output.contains("have proof_fact_1_5 : p b := by"));
                assert!(output.contains("simpa only [proof_fact_1_4] using proof_fact_1_3"));
                assert!(output.contains("exact proof_fact_1_5"));
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
                let output = to_lean_from_source(source, "multi-equality-transport").unwrap();

                assert!(output.contains("have proof_fact_1_4 : q c := proof_fact_1_1"));
                assert!(output.contains("have proof_fact_1_7 : q a := by"));
                assert!(output
                    .contains("simpa only [proof_fact_1_5, proof_fact_1_6] using proof_fact_1_4"));
                let related_proof = output
                    .split("have proof_fact_2_3 : related a b")
                    .nth(1)
                    .expect("binary transport proof");
                assert_eq!(
                    related_proof
                        .split("simpa only")
                        .next()
                        .unwrap()
                        .matches("have proof_fact_2_4")
                        .count(),
                    1,
                    "one equality used at two argument positions should be emitted once"
                );
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
                runtime.replace_to_lean_mode(true);
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut statement_irs = Vec::new();
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    statement_irs.push(result.to_lean_ir().unwrap().clone());
                }

                let StmtToLeanIR::Fact(forall) = &statement_irs[1] else {
                    panic!("second IR item should be the forall fact");
                };
                let FactProofToLeanIR::ForallIntroduction { conclusions, .. } = &forall.fact.proof
                else {
                    panic!("forall should retain introduction evidence");
                };
                let FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::EqualityRewrite(rewrite),
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
                    EqualityRewriteDirectionToLeanIR::Backward
                );

                let first_output = to_lean_from_source(source, "branched-equality-output").unwrap();
                assert!(!first_output.contains(": a = c :="));
                assert!(!first_output.contains(": h = b :="));
                assert!(!first_output.contains(": h = u :="));
                assert!(!first_output.contains(": u = v :="));
                assert!(!first_output.contains(": w = z :="));
                assert!(!first_output.contains("sorry"));
                for _ in 0..12 {
                    assert_eq!(
                        to_lean_from_source(source, "branched-equality-output").unwrap(),
                        first_output
                    );
                }
            },
        );
    }

    #[test]
    fn unstructured_fact_transport_is_an_explicit_unsupported_rule() {
        run_with_large_stack(
            "unstructured_fact_transport_is_an_explicit_unsupported_rule",
            || {
                let source = "forall a, b R:\n    a > b\n    =>:\n        b < a";
                let error = to_lean_from_source(source, "unstructured-transport")
                    .expect_err("an unrecorded transport must stop emission")
                    .trace_message();

                assert!(error.contains("OtherUnsupported"));
                assert!(error.contains("without structured rewrite evidence"));
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
                let error = to_lean_from_source(source, "derived-equality-transport")
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
            runtime.replace_to_lean_mode(true);
            let tokenizer = Tokenizer::new();
            let blocks = tokenizer
                .parse_blocks(source, runtime.current_file_path_rc())
                .unwrap();
            let mut statement_irs = Vec::new();
            for mut block in blocks {
                let statement = runtime.parse_stmt(&mut block).unwrap();
                let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                statement_irs.push(result.to_lean_ir().unwrap().clone());
            }

            let StmtToLeanIR::Fact(first) = &statement_irs[0] else {
                panic!("first IR item should be a forall fact");
            };
            let first_id = first.fact.fact_id.expect("first forall must have an ID");
            let StmtToLeanIR::Fact(second) = &statement_irs[1] else {
                panic!("second IR item should be a cited forall fact");
            };
            assert!(matches!(
                underlying_test_proof(&second.fact.proof),
                FactProofToLeanIR::KnownFactCitation { source_fact_id }
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
                let output = to_lean_from_source(source, "temporary-domain-evidence").unwrap();

                assert!(
                    output.contains("intro x proof_fact_1_1 proof_fact_1_2 proof_fact_1_3"),
                    "{output}"
                );
                assert!(
                    output.contains("-- Litex parameter requirement for `x`: x : LitexSet"),
                    "{output}"
                );
                assert!(
                    output.contains("let proof_arg_1_4 : LitexSet := x"),
                    "{output}"
                );
                assert!(
                    output.contains("have proof_fact_1_5 : x ∈ litexR := proof_fact_1_1"),
                    "{output}"
                );
                assert!(
                    output.contains("have proof_fact_1_6 : x ≠ 0 := proof_fact_1_2"),
                    "{output}"
                );
                assert!(output.contains(":= global_fact_"), "{output}");
                assert!(
                    output.contains(" proof_arg_1_4 proof_fact_1_5 proof_fact_1_6"),
                    "{output}"
                );
                assert_eq!(output.matches("\naxiom global_fact_").count(), 1);
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
                runtime.replace_to_lean_mode(true);
                let tokenizer = Tokenizer::new();
                let blocks = tokenizer
                    .parse_blocks(source, runtime.current_file_path_rc())
                    .unwrap();
                let mut statement_irs = Vec::new();
                for mut block in blocks {
                    let statement = runtime.parse_stmt(&mut block).unwrap();
                    let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
                    statement_irs.push(result.to_lean_ir().unwrap().clone());
                }

                let StmtToLeanIR::Fact(target) = &statement_irs[2] else {
                    panic!("third IR item should be the proved marked2 fact");
                };
                let FactProofToLeanIR::RuleApplication {
                    rule:
                        ProofRuleToLeanIR::Normalization {
                            kind: NormalizationKindToLeanIR::RationalExpressionSimplification,
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
                let FactProofToLeanIR::RuleApplication {
                    rule: ProofRuleToLeanIR::KnownForallInstantiation { arguments, .. },
                    parameter_requirements,
                    premises: domain_requirements,
                } = underlying_test_proof(&direct_instance.proof)
                else {
                    panic!("the normalization premise should be the direct forall instance");
                };
                assert_eq!(arguments.len(), 1);
                assert_eq!(arguments[0].param, "x");
                assert!(matches!(
                    arguments[0].param_type,
                    ParamTypeToLeanIR::MemberOf(ObjToLeanIR::StandardSet(
                        StandardSetToLeanIR::Real
                    ))
                ));
                assert_eq!(parameter_requirements.len(), 1);
                assert!(domain_requirements.is_empty());

                let output = emit_lean_from_ir(&statement_irs).unwrap();
                assert!(
                    output.contains("-- Litex parameter requirement for `x`: (2 - 1) : LitexSet"),
                    "{output}"
                );
                assert!(
                    output.contains("let proof_arg_2_1 : LitexSet := (2 - 1)"),
                    "{output}"
                );
                assert!(
                    output.contains("have proof_fact_2_2 : (2 - 1) ∈ litexR := by"),
                    "{output}"
                );
                assert!(output.contains("have proof_fact_2_3 : marked2"), "{output}");
                assert!(output.contains(":= global_fact_"), "{output}");
                assert!(output.contains(" proof_arg_2_1"), "{output}");
                assert!(
                    output.contains("convert proof_fact_1_1 using 1 <;> norm_num ["),
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
                let output = to_lean_from_source(source, "closed-membership-citation").unwrap();

                assert!(
                    output.contains("have proof_fact_2_2 : (2 - 1) ∈ litexR := by"),
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

                let error = to_lean("1 = 1", &mut runtime)
                    .expect_err("a preloaded ID has no declaration in this emitted Lean module")
                    .trace_message();
                assert!(error.contains("before that fact has a Lean declaration"));
                assert!(!runtime.to_lean_mode());
            },
        );
    }

    #[test]
    fn to_lean_set_obj_abi_uses_one_carrier_and_structural_set_operations() {
        run_with_large_stack(
            "to_lean_set_obj_abi_uses_one_carrier_and_structural_set_operations",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_set_obj_abi.lit");
                let source = fs::read_to_string(path).unwrap();
                let output = to_lean_from_source(&source, "set-obj-abi").unwrap();

                assert!(output.contains("inductive LitexSet where"));
                assert!(output.contains("def litexUnion := litexBinary \"union\""));
                assert!(output.contains("litexUnion A B = litexUnion A B"));
                assert!(output.contains("litexIntersect A B = litexIntersect A B"));
                assert!(output.contains("litexSetMinus A B = litexSetMinus A B"));
                assert_eq!(output.matches("intro A B\n  rfl").count(), 3);
                assert!(!output.contains("LitexObj"));
                assert!(!output.contains("Type uLitex"));
                assert!(!output.contains("(A B : ℝ)"));
                assert!(!output.contains("sorry"));
            },
        );
    }

    #[test]
    fn to_lean_set_builder_fails_during_obj_ir_construction() {
        run_with_large_stack(
            "to_lean_set_builder_fails_during_obj_ir_construction",
            || {
                let source = "{x R: x = x} = {x R: x = x}";
                let report =
                    to_lean_from_source_with_report(source, "set-builder-boundary").unwrap();

                assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                assert_eq!(report.unsupported.len(), 1);
                assert_eq!(
                    report.unsupported[0].phase,
                    ToLeanUnsupportedPhase::IrConstruction
                );
                assert!(report.unsupported[0].reason.contains("SetBuilder"));
                assert!(!report.lean_code.contains("theorem global_fact_"));
                assert!(!report.lean_code.contains("axiom global_fact_"));
                assert!(!report.lean_code.contains("sorry"));
            },
        );
    }

    #[test]
    fn unsupported_builtin_never_falls_back_to_axiom_or_sorry() {
        run_with_large_stack(
            "unsupported_builtin_never_falls_back_to_axiom_or_sorry",
            || {
                let error = to_lean_from_source("sin(0) = 0", "unsupported-builtin")
                    .expect_err("unsupported builtin must stop emission")
                    .trace_message();

                assert!(error.contains("no checked backend") || error.contains("does not support"));
            },
        );
    }

    #[test]
    fn to_lean_partial_report_keeps_supported_statements_and_marks_incomplete() {
        run_with_large_stack(
            "to_lean_partial_report_keeps_supported_statements_and_marks_incomplete",
            || {
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_partial_report.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(&path.to_string_lossy());
                let report = to_lean_with_report(&source, &mut runtime).unwrap();

                assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                assert!(!report.is_complete());
                assert_eq!(report.unsupported.len(), 1);
                assert_eq!(report.unsupported[0].statement_index, 2);
                assert_eq!(
                    report.unsupported[0].phase,
                    ToLeanUnsupportedPhase::LeanEmission
                );
                assert!(report.unsupported[0].statement.contains("sin"));
                assert!(report.lean_code.contains("-- To-Lean status: incomplete"));
                assert!(report
                    .lean_code
                    .contains("-- To-Lean omitted statement 2 during Lean emission"));
                assert_eq!(report.lean_code.matches("theorem global_fact_").count(), 2);
                assert!(!report.lean_code.contains("axiom"));
                assert!(!report.lean_code.contains("sorry"));
                assert!(!runtime.to_lean_mode());
            },
        );
    }

    #[test]
    fn to_lean_partial_report_rolls_back_a_partly_emitted_statement() {
        run_with_large_stack(
            "to_lean_partial_report_rolls_back_a_partly_emitted_statement",
            || {
                let mut source_ir = test_to_lean_ir("trust 1 = 1\n\n2 = 2", "partial-rollback");
                let StmtToLeanIR::Trust(mut trusted) = source_ir.remove(0) else {
                    panic!("first test statement should produce trust IR");
                };
                let StmtToLeanIR::Fact(proved) = source_ir.remove(0) else {
                    panic!("second test statement should produce fact IR");
                };
                trusted.facts.push(proved.fact);
                let report = emit_lean_from_ir_with_report(&[StmtToLeanIR::Trust(trusted)]);

                assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);
                assert_eq!(report.unsupported.len(), 1);
                assert_eq!(
                    report.unsupported[0].phase,
                    ToLeanUnsupportedPhase::LeanEmission
                );
                assert!(report.unsupported[0]
                    .reason
                    .contains("only an explicit Litex `trust` statement may emit a Lean axiom"));
                assert!(!report.lean_code.contains("axiom global_fact_"));
                assert!(report.lean_code.contains("-- To-Lean omitted statement 1"));
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
            let error = to_lean_from_source(source, "unsupported-nested-requirement")
                .expect_err("numeric nonzero requirement has no Lean backend yet")
                .trace_message();

            assert!(error.contains("no checked backend"));
            assert!(!error.contains("sorry"));
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN pointing to a Lean 4 executable"]
    fn generated_to_lean_set_obj_abi_compiles_with_lean_core() {
        run_with_large_stack(
            "generated_to_lean_set_obj_abi_compiles_with_lean_core",
            || {
                let lean =
                    std::env::var("LITEX_LEAN").expect("set LITEX_LEAN to a Lean 4 executable");
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_set_obj_abi.lit");
                let source = fs::read_to_string(path).unwrap();
                let generated = to_lean_from_source(&source, "set-obj-abi-kernel").unwrap();
                let generated = generated
                    .replacen("import Mathlib", "import Init", 1)
                    .replace("ℝ", "Rat");

                let lean_file = private_tmp_lean_file("litex_to_lean_set_obj_abi");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lean).arg(&lean_file).output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "set-Obj generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN pointing to a Lean 4 executable"]
    fn generated_to_lean_statement_scopes_compile_with_lean_core() {
        run_with_large_stack(
            "generated_to_lean_statement_scopes_compile_with_lean_core",
            || {
                let lean =
                    std::env::var("LITEX_LEAN").expect("set LITEX_LEAN to a Lean 4 executable");
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_statement_scopes.lit");
                let source = fs::read_to_string(path).unwrap();
                let generated = to_lean_from_source(&source, "statement-scopes-kernel").unwrap();
                let generated = generated
                    .replacen("import Mathlib", "import Init", 1)
                    .replace("ℝ", "Rat");

                let lean_file = private_tmp_lean_file("litex_to_lean_statement_scopes");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lean).arg(&lean_file).output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "statement-scope generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN pointing to a Lean 4 executable"]
    fn generated_to_lean_choice_have_compiles_with_lean_core() {
        run_with_large_stack(
            "generated_to_lean_choice_have_compiles_with_lean_core",
            || {
                let lean =
                    std::env::var("LITEX_LEAN").expect("set LITEX_LEAN to a Lean 4 executable");
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_choice_have.lit");
                let source = fs::read_to_string(path).unwrap();
                let generated = to_lean_from_source(&source, "choice-have-kernel").unwrap();
                let generated = generated
                    .replacen("import Mathlib", "import Init", 1)
                    .replace("ℝ", "Rat");

                let lean_file = private_tmp_lean_file("litex_to_lean_choice_have");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lean).arg(&lean_file).output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "choice-have generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN pointing to a Lean 4 executable"]
    fn generated_to_lean_exist_have_compiles_with_lean_core() {
        run_with_large_stack(
            "generated_to_lean_exist_have_compiles_with_lean_core",
            || {
                let lean =
                    std::env::var("LITEX_LEAN").expect("set LITEX_LEAN to a Lean 4 executable");
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_exist_have.lit");
                let source = fs::read_to_string(path).unwrap();
                let generated = to_lean_from_source(&source, "exist-have-kernel").unwrap();
                let generated = generated
                    .replacen("import Mathlib", "import Init", 1)
                    .replace("ℝ", "Rat");

                let lean_file = private_tmp_lean_file("litex_to_lean_exist_have");
                fs::write(&lean_file, &generated).unwrap();
                let output = Command::new(lean).arg(&lean_file).output();
                let _ = fs::remove_file(&lean_file);
                let output = output.unwrap();
                assert!(
                    output.status.success(),
                    "exist-have generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                    generated
                );
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn generated_partial_to_lean_report_compiles_with_lean() {
        run_with_large_stack(
            "generated_partial_to_lean_report_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_partial_report.lit");
                let source = fs::read_to_string(&path).unwrap();
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(&path.to_string_lossy());
                let report = to_lean_with_report(&source, &mut runtime).unwrap();
                assert_eq!(report.status, ToLeanCompilationStatus::Incomplete);

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
            },
        );
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn generated_to_lean_recursive_strategy_ir_compiles_with_lean() {
        run_with_large_stack(
            "generated_to_lean_recursive_strategy_ir_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_recursive_strategy_ir.lit");
                let source = fs::read_to_string(&path).unwrap();
                let generated = to_lean_from_source(&source, &path.to_string_lossy()).unwrap();

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
    fn generated_to_lean_builtin_rules_20_compiles_with_lean() {
        run_with_large_stack(
            "generated_to_lean_builtin_rules_20_compiles_with_lean",
            || {
                let project = std::env::var("LITEX_LEAN_PROJECT")
                    .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
                let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
                let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("examples/05_compiler_interop/to_lean_builtin_rules_20.lit");
                let source = fs::read_to_string(&path).unwrap();
                let generated = to_lean_from_source(&source, &path.to_string_lossy()).unwrap();

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
    fn generated_to_lean_mvp_compiles_with_lean() {
        run_with_large_stack("generated_to_lean_mvp_compiles_with_lean", || {
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
            let generated = to_lean(source, &mut runtime).unwrap();
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

    fn test_to_lean_ir(source: &str, entry_label: &str) -> Vec<StmtToLeanIR> {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope(entry_label);
        runtime.replace_to_lean_mode(true);
        let tokenizer = Tokenizer::new();
        let blocks = tokenizer
            .parse_blocks(source, runtime.current_file_path_rc())
            .unwrap();
        let mut statement_irs = Vec::new();
        for mut block in blocks {
            let statement = runtime.parse_stmt(&mut block).unwrap();
            let result = run_stmt_at_global_env(&statement, &mut runtime).unwrap();
            statement_irs.push(result.to_lean_ir().unwrap().clone());
        }
        statement_irs
    }

    fn underlying_test_proof(mut proof: &FactProofToLeanIR) -> &FactProofToLeanIR {
        while let FactProofToLeanIR::Memo { proof: source } = proof {
            proof = source.as_ref();
        }
        proof
    }

    fn underlying_test_proof_mut(mut proof: &mut FactProofToLeanIR) -> &mut FactProofToLeanIR {
        loop {
            match proof {
                FactProofToLeanIR::Memo { proof: source } => proof = source.as_mut(),
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
