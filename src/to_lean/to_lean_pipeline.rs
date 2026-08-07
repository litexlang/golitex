use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use super::rational_expression::{lean_name, LeanRationalExpression};

pub fn to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let namespace = lean_namespace_for_runtime(runtime);
    to_lean_with_namespace(source_code, runtime, namespace)
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

/// Pure backend boundary: this function has no Runtime and cannot inspect raw
/// Litex statements or re-run proof search.
pub fn emit_lean_from_ir(ir: &[StmtToLeanIR]) -> Result<String, RuntimeError> {
    emit_lean_from_ir_with_namespace(ir, None)
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
    local_space_id: Option<usize>,
    next_local_index: usize,
}

impl LeanProofContext {
    fn new_proof_space(&self) -> Self {
        LeanProofContext {
            proof_fact_names: self.proof_fact_names.clone(),
            nonzero_names: self.nonzero_names.clone(),
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
        let body = format!(
            "-- Litex's primitive notion of a set.\nabbrev LitexSet := Type uLitex\n\n-- Every generated proposition has this codomain.\nabbrev LitexFact := Prop\n\n{}",
            self.declarations.join("\n\n")
        );
        match self.namespace {
            Some(namespace) => format!(
                "import Mathlib\n\nuniverse uLitex\n\nnamespace {}\n\n{}\n\nend {}\n",
                namespace, body, namespace
            ),
            None => format!("import Mathlib\n\nuniverse uLitex\n\n{}\n", body),
        }
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
            FactProofToLeanIR::RuleApplication { rule, .. } => Err(to_lean_error(
                &proposition.line_file(),
                format!("To-Lean has no checked backend for proof rule {:?}", rule),
            )),
            FactProofToLeanIR::ForallIntroduction {
                parameter_premises: _,
                premises,
                conclusions,
            } => self.lean_forall_introduction(proposition, premises, conclusions, context),
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
        Ok((
            local_name.clone(),
            vec![format!(
                "  have {} : {} := {}",
                local_name,
                lean_fact(&fact.proposition)?,
                proof.replace('\n', "\n  ")
            )],
        ))
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
        for (argument, _requirement) in arguments.iter().zip(parameter_requirements.iter()) {
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
        let result_name = self.next_proof_fact_name(context);
        lines.push(format!(
            "  have {} : {} := by",
            result_name,
            lean_fact(proposition)?
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
        premises: &[LocalPremiseToLeanIR],
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
        let conclusion = &conclusions[0];
        let inner =
            self.lean_proof_in_current_space(&conclusion.proposition, &conclusion.proof, context)?;
        let inner = inner.strip_prefix("by\n").unwrap_or(inner.as_str());
        Ok(format!("by\n  intro {}\n{}", intro_names.join(" "), inner))
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

fn lean_abstract_prop(ir: &AbstractPropToLeanIR) -> String {
    let name = lean_name(&ir.name);
    if ir.params.is_empty() {
        return format!("opaque {} : LitexFact", name);
    }
    let type_names = ir
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| format!("α_{}_{}", lean_name(param), index + 1))
        .collect::<Vec<_>>();
    format!(
        "opaque {} {{{} : Sort uLitex}} : {} → LitexFact",
        name,
        type_names.join(" "),
        type_names.join(" → ")
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
        ParamTypeToLeanIR::Real => Ok("ℝ"),
        ParamTypeToLeanIR::LitexSet => Ok("LitexSet"),
        ParamTypeToLeanIR::Rational
        | ParamTypeToLeanIR::Integer
        | ParamTypeToLeanIR::Natural
        | ParamTypeToLeanIR::LitexNonemptySet
        | ParamTypeToLeanIR::Unsupported(_) => Err(to_lean_error(
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
        other => Err(to_lean_error(
            &other.line_file(),
            format!(
                "To-Lean proposition backend does not support `{}`",
                other.fact_type_string()
            ),
        )),
    }
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
    Ok(format!(
        "{} {} {}",
        lean_obj(left)?,
        operator,
        lean_obj(right)?
    ))
}

fn lean_forall_fact(forall: &ForallFact) -> Result<String, RuntimeError> {
    let mut binders = Vec::new();
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
    }
    let conclusions = forall
        .then_facts
        .iter()
        .map(|fact| lean_fact(&fact.clone().to_fact()))
        .collect::<Result<Vec<_>, RuntimeError>>()?;
    let mut body = parenthesized_join(conclusions, " ∧ ");
    for premise in forall.dom_facts.iter().rev() {
        body = format!("{} → {}", lean_fact(premise)?, body);
    }
    Ok(format!("∀ {}, {}", binders.join(" "), body))
}

fn lean_param_type(param_type: &ParamType) -> Result<&'static str, RuntimeError> {
    match param_type {
        ParamType::Obj(Obj::StandardSet(StandardSet::R)) => Ok("ℝ"),
        ParamType::Set(_) => Ok("LitexSet"),
        other => Err(to_lean_error(
            &default_line_file(),
            format!(
                "To-Lean does not support quantified parameter type `{}`",
                other
            ),
        )),
    }
}

fn lean_obj(obj: &Obj) -> Result<String, RuntimeError> {
    match obj {
        Obj::StandardSet(StandardSet::R) => Ok("ℝ".to_string()),
        Obj::StandardSet(StandardSet::Q) => Ok("ℚ".to_string()),
        Obj::StandardSet(StandardSet::Z) => Ok("ℤ".to_string()),
        Obj::StandardSet(StandardSet::N) => Ok("ℕ".to_string()),
        _ => LeanRationalExpression::from_obj(obj).map(|expression| expression.expression),
    }
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
    Ok(format!(
        "by\n  -- left recursive fraction: {}\n  -- right recursive fraction: {}\n  calc\n    {} = {} := by\n      {}\n    _ = {} := by\n      {}\n    _ = {} := by\n      {}",
        left.fraction(),
        right.fraction(),
        left.expression,
        left.fraction_expression(),
        tactic,
        right.fraction_expression(),
        tactic,
        right.expression,
        tactic
    ))
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
    format!(
        "solve\n        | {}\n        | {} <;> ring",
        field_simp, field_simp
    )
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

fn lean_proof_fact_name(local_space_id: usize, proof_fact_index: usize) -> String {
    format!("proof_fact_{}_{}", local_space_id, proof_fact_index)
}

fn lean_proof_arg_name(local_space_id: usize, local_index: usize) -> String {
    format!("proof_arg_{}_{}", local_space_id, local_index)
}

fn is_nonzero_fact(fact: &Fact) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::NotEqualFact(_)))
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
            assert!(registered.contains("def is_one (x : ℝ) : LitexFact :="));
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

forall x R:
    x != 0
    =>:
        x != 0
"#;
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("to-lean-ir-mvp.lit");
                let output = to_lean(source, &mut runtime).unwrap();

                assert!(output.starts_with(
                    "import Mathlib\n\nuniverse uLitex\n\nnamespace to_lean_ir_mvp\n\n"
                ));
                assert!(output.contains("abbrev LitexSet := Type uLitex"));
                assert!(output.contains("abbrev LitexFact := Prop"));
                assert!(
                    output.find("abbrev LitexSet").unwrap()
                        < output.find("abbrev LitexFact").unwrap()
                );
                assert!(output.contains("opaque marked {α_x_1 : Sort uLitex} : α_x_1 → LitexFact"));
                assert!(!output.contains("namespace LitexGenerated"));
                assert!(!output.contains("end LitexGenerated"));
                assert!(!output.lines().any(|line| line == "universe u"));
                assert!(output.ends_with("\nend to_lean_ir_mvp\n"));
                assert!(output.contains("def is_one (x : ℝ) : LitexFact :="));
                assert_eq!(output.matches("\naxiom global_fact_").count(), 1);
                assert!(output.contains(":= global_fact_"));
                assert!(output.contains(" (1 : ℝ)"));
                assert!(output.contains("simp [is_one]"));
                assert!(output.contains("let proof_arg_"));
                assert!(output.contains("intro a b x proof_fact_"));
                assert!(output.contains("field_simp [proof_fact_"));
                assert!(!output.contains("sorry"));
            },
        );
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
                conclusions,
            } = &forall.fact.proof
            else {
                panic!("last fact should retain forall-introduction evidence");
            };
            assert_eq!(parameter_premises.len(), 3);
            assert_eq!(premises.len(), 1);
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
    fn closed_rational_builtin_is_emitted_from_ir() {
        run_with_large_stack("closed_rational_builtin_is_emitted_from_ir", || {
            let output = to_lean_from_source("1 / 2 / 3 / 4 = 1 / 24", "closed-ir").unwrap();

            assert!(output.contains("theorem global_fact_1"));
            assert!(output
                .contains("-- left recursive fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))"));
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

            assert!(output.contains("intro x proof_fact_1_1"));
            assert!(output.contains("exact proof_fact_1_1"));
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
                assert!(output.contains("intro x proof_fact_1_1"));
                assert!(output.contains("exact proof_fact_1_1"));
                assert!(output.contains("intro y proof_fact_2_1"));
                assert!(output.contains("exact proof_fact_2_1"));
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

                assert!(output.contains("intro x proof_fact_1_1"), "{output}");
                assert!(
                    output.contains("-- Litex parameter requirement for `x`: x : ℝ"),
                    "{output}"
                );
                assert!(output.contains("let proof_arg_1_3 : ℝ := x"), "{output}");
                assert!(
                    output.contains("have proof_fact_1_4 : x ≠ (0 : ℝ) := proof_fact_1_1"),
                    "{output}"
                );
                assert!(output.contains(":= global_fact_"), "{output}");
                assert!(output.contains(" proof_arg_1_3 proof_fact_1_4"), "{output}");
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
                assert!(matches!(arguments[0].param_type, ParamTypeToLeanIR::Real));
                assert_eq!(parameter_requirements.len(), 1);
                assert!(domain_requirements.is_empty());

                let output = emit_lean_from_ir(&statement_irs).unwrap();
                assert!(
                    output.contains(
                        "-- Litex parameter requirement for `x`: ((2 : ℝ) - (1 : ℝ)) : ℝ"
                    ),
                    "{output}"
                );
                assert!(
                    output.contains("let proof_arg_2_1 : ℝ := ((2 : ℝ) - (1 : ℝ))"),
                    "{output}"
                );
                assert!(output.contains("have proof_fact_2_2 : marked2"), "{output}");
                assert!(output.contains(":= global_fact_"), "{output}");
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
            assert!(error.contains("not_equal_numeric"));
        });
    }

    #[test]
    #[ignore = "requires LITEX_LEAN_PROJECT pointing to a fetched Mathlib Lake project"]
    fn generated_to_lean_mvp_compiles_with_lean() {
        run_with_large_stack("generated_to_lean_mvp_compiles_with_lean", || {
            let project = std::env::var("LITEX_LEAN_PROJECT")
                .expect("set LITEX_LEAN_PROJECT to a Mathlib Lake project");
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
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let lean_file = std::env::temp_dir().join(format!(
                "litex_to_lean_mvp_{}_{}.lean",
                std::process::id(),
                nonce
            ));
            fs::write(&lean_file, &generated).unwrap();
            let output = Command::new("lake")
                .args(["env", "lean"])
                .arg(&lean_file)
                .current_dir(project)
                .output()
                .unwrap();
            let _ = fs::remove_file(&lean_file);
            assert!(
                output.status.success(),
                "generated Lean failed\nstdout:\n{}\nstderr:\n{}\nsource:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
                generated
            );
        });
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

    fn underlying_test_proof(mut proof: &FactProofToLeanIR) -> &FactProofToLeanIR {
        while let FactProofToLeanIR::Memo { proof: source } = proof {
            proof = source.as_ref();
        }
        proof
    }
}
