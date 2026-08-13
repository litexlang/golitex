use crate::common::keywords::IS_CHOICE_FUNCTION_FOR;
use crate::prelude::*;
use crate::verify::rule_schema::{canonical_atomic_facts_equal, MatchLimits};
use std::collections::{HashMap, HashSet};

use super::shared_lean_library::generated_import_header;
use super::{
    LitexToLeanCompilationPhase, LitexToLeanCompilationReport, LitexToLeanUnsupportedStatement,
};

pub fn compile_to_lean(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    let previous_mode = runtime.replace_litex_to_lean_ir_mode(true);
    let result = compile_to_lean_in_mode(source_code, runtime);
    runtime.replace_litex_to_lean_ir_mode(previous_mode);
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
                "Litex-to-Lean mode completed a statement without producing IR",
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
    emit_lean_from_litex_to_lean_ir(&ir)
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
}

#[derive(Clone, Default)]
struct RenderContext {
    symbol_names: HashMap<SymbolId, String>,
    local_fact_names: HashMap<FactId, String>,
    local_fact_propositions: HashMap<FactId, Fact>,
    local_forall_facts: HashMap<FactId, Fact>,
    well_defined_fact_names: HashMap<WellDefinedFactId, String>,
    function_bindings: HashMap<SymbolId, FunctionBinding>,
    well_definedness: LitexToLeanWellDefinednessCertificateIr,
    function_set_depth: usize,
}

struct ForallEmission {
    context: RenderContext,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
    parameter_symbol_ids: Vec<SymbolId>,
    parameter_fact_ids: Vec<FactId>,
    domain_fact_ids: Vec<FactId>,
    conclusions: Vec<LitexToLeanFactIr>,
}

#[derive(Clone)]
struct ApplicationScope {
    source_occurrence_id: SourceObjectOccurrenceId,
    context: RenderContext,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
}

#[derive(Clone)]
struct WellDefinedHelperBinding {
    theorem_name: String,
    binder_names: Vec<String>,
    binder_types: Vec<String>,
}

struct UniversalEmitter {
    declarations: Vec<String>,
    global_facts: HashMap<FactId, GlobalFactBinding>,
    well_defined_helpers: HashMap<WellDefinedFactId, WellDefinedHelperBinding>,
}

impl UniversalEmitter {
    fn new() -> Self {
        Self {
            declarations: Vec::new(),
            global_facts: HashMap::new(),
            well_defined_helpers: HashMap::new(),
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
        match statement {
            LitexToLeanStatementIr::AbstractProp(ir) => self.emit_abstract_prop(ir),
            LitexToLeanStatementIr::Trust(ir) => self.emit_trust(ir),
            LitexToLeanStatementIr::ProjectedForall(ir) => self.emit_projected_forall(ir),
            LitexToLeanStatementIr::Fact(ir) => {
                self.emit_stored_fact(&ir.fact, &ir.well_definedness)
            }
            other => Err(universal_error(
                &statement_line_file(other),
                format!(
                    "the universal-object MVP does not yet emit statement `{}`",
                    statement_label(other)
                ),
            )),
        }
    }

    fn emit_abstract_prop(&mut self, ir: &LitexToLeanAbstractPropIr) -> Result<(), RuntimeError> {
        let name = lean_name(&ir.name);
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

    fn emit_trust(&mut self, ir: &LitexToLeanTrustIr) -> Result<(), RuntimeError> {
        if !ir.inferred_facts.is_empty() {
            return Err(universal_error(
                &ir.inferred_facts[0].proposition.line_file(),
                "trusted inferred consequences require their own checked proof routes",
            ));
        }
        for (index, fact) in ir.facts.iter().enumerate() {
            let theorem_name = fact
                .fact_id
                .map(|fact_id| format!("fact{}", fact_id.value()))
                .unwrap_or_else(|| format!("trusted_fact_{}", index + 1));
            let theorem_type = self.render_top_level_fact_type(&fact.proposition)?;
            self.declarations
                .push(format!("axiom {theorem_name} : {theorem_type}"));
            if let Some(fact_id) = fact.fact_id {
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
        Ok(())
    }

    fn render_top_level_fact_type(&self, fact: &Fact) -> Result<String, RuntimeError> {
        match fact {
            Fact::ForallFact(forall) => {
                let mut context = RenderContext::default();
                let mut binders = Vec::new();
                let mut parameter_index = 0;
                for group in forall.params_def_with_type.groups.iter() {
                    for binding in group.params.iter() {
                        let name = lean_name(binding.name());
                        context.symbol_names.insert(binding.id(), name.clone());
                        binders.push(format!("({name} : Litex.Object)"));
                        parameter_index += 1;
                        binders.push(format!(
                            "(litex_param_fact_{} : {})",
                            parameter_index,
                            self.render_parameter_requirement(&name, &group.param_type, &context,)?
                        ));
                    }
                }
                for (index, domain) in forall.dom_facts.iter().enumerate() {
                    binders.push(format!(
                        "(litex_domain_fact_{} : {})",
                        index + 1,
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
                    Ok(format!("∀ {}, {}", binders.join(" "), conclusion))
                }
            }
            _ => self.render_fact(fact, &RenderContext::default()),
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

    fn emit_projected_forall(
        &mut self,
        ir: &LitexToLeanProjectedForallIr,
    ) -> Result<(), RuntimeError> {
        let Fact::ForallFact(source) = &ir.source else {
            return Err(universal_error(
                &ir.source.line_file(),
                "projected-forall IR does not retain a forall source",
            ));
        };
        let mut ordered = ir
            .facts
            .iter()
            .map(|fact| Ok((projection_source_index(source, fact)?, fact)))
            .collect::<Result<Vec<_>, RuntimeError>>()?;
        ordered.sort_by_key(|(index, _)| *index);
        for (_, fact) in ordered {
            self.emit_stored_fact(fact, &ir.well_definedness)?;
        }
        if !ir.inferred_facts.is_empty() {
            return Err(universal_error(
                &ir.source.line_file(),
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
        let theorem_name = format!("fact{}", fact_id.value());
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
        let theorem_type = if binders.is_empty() {
            conclusion_text
        } else {
            format!("∀ {}, {}", binders.join(" "), conclusion_text)
        };
        let mut proof_lines = vec!["by".to_string()];
        if !emission.binder_names.is_empty() {
            proof_lines.push(format!("  intro {}", emission.binder_names.join(" ")));
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
            "theorem {theorem_name} : {theorem_type} :=\n{}",
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
        let theorem_name = format!("fact{}", fact_id.value());
        let theorem_type = self.render_top_level_fact_type(&fact.proposition)?;
        let context = RenderContext {
            well_definedness: well_definedness.clone(),
            ..RenderContext::default()
        };
        let proof = self.render_proof_term(fact, &context)?;
        self.declarations.push(format!(
            "theorem {theorem_name} : {theorem_type} := by\n  exact {proof}"
        ));
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
        if !inferred_premises.is_empty() {
            return Err(universal_error(
                &forall.line_file,
                "the universal-object MVP does not yet emit inferred forall premises",
            ));
        }
        let parameter_count = forall.params_def_with_type.number_of_params();
        if parameter_count != parameter_premises.len() || forall.dom_facts.len() != premises.len() {
            return Err(universal_error(
                &forall.line_file,
                "forall evidence does not match its parameter or domain arity",
            ));
        }

        let mut context = RenderContext {
            well_definedness: well_definedness.clone(),
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
                let proof_name = format!("litex_param_fact_{}", parameter_index + 1);
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
                    context.function_bindings.insert(
                        binding.id(),
                        FunctionBinding {
                            function: LitexToLeanFunctionTypeIr::lower(function_set)
                                .map_err(|message| universal_error(&forall.line_file, message))?,
                            membership_proof_name: proof_name,
                        },
                    );
                }
                parameter_index += 1;
            }
        }

        let mut domain_fact_ids = Vec::new();
        for premise in premises.iter() {
            self.prepare_well_defined_facts_for_fact_type(
                &mut context,
                &premise.fact,
                &binder_names,
                &binder_types,
            )?;
        }
        for (index, premise) in premises.iter().enumerate() {
            let proof_name = format!("litex_domain_fact_{}", index + 1);
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

        for conclusion in conclusions.iter() {
            self.prepare_well_defined_facts_for_fact_type(
                &mut context,
                &conclusion.proposition,
                &binder_names,
                &binder_types,
            )?;
        }

        Ok(ForallEmission {
            context,
            binder_names,
            binder_types,
            parameter_symbol_ids,
            parameter_fact_ids,
            domain_fact_ids,
            conclusions: conclusions.clone(),
        })
    }

    fn prepare_scoped_well_defined_facts(
        &mut self,
        context: &mut RenderContext,
        well_definedness: &LitexToLeanWellDefinednessCertificateIr,
        application_occurrence_ids: &HashSet<SourceObjectOccurrenceId>,
        binder_names: &[String],
        binder_types: &[String],
    ) -> Result<(), RuntimeError> {
        if application_occurrence_ids.is_empty() {
            return Ok(());
        }
        let mut canonical_proof_ids = HashSet::new();
        let mut selected_ids = HashSet::new();
        let mut selected_roles = HashSet::new();
        for requirement in well_definedness.target_requirements.iter() {
            if !application_occurrence_ids.contains(&requirement.source_occurrence_id)
                || !selected_roles.insert((requirement.source_occurrence_id, requirement.role))
            {
                continue;
            }
            canonical_proof_ids.insert(requirement.well_defined_obj_proof_id);
            selected_ids.insert(requirement.well_defined_fact_id);
        }
        for object in well_definedness.objects.iter() {
            if canonical_proof_ids.contains(&object.well_defined_obj_proof_id) {
                selected_ids.extend(object.well_defined_fact_ids.iter().copied());
            }
        }

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
                if let Some(helper) = self.well_defined_helpers.get(&fact.well_defined_fact_id) {
                    let mut arguments = Vec::with_capacity(helper.binder_names.len());
                    let mut compatible = true;
                    for (name, expected_type) in
                        helper.binder_names.iter().zip(helper.binder_types.iter())
                    {
                        let Some(index) =
                            binder_names.iter().position(|candidate| candidate == name)
                        else {
                            compatible = false;
                            break;
                        };
                        if binder_types.get(index) != Some(expected_type) {
                            compatible = false;
                            break;
                        }
                        arguments.push(name.clone());
                    }
                    if compatible {
                        let applied_name = if arguments.is_empty() {
                            helper.theorem_name.clone()
                        } else {
                            format!("({} {})", helper.theorem_name, arguments.join(" "))
                        };
                        context
                            .well_defined_fact_names
                            .insert(fact.well_defined_fact_id, applied_name);
                        made_progress = true;
                        continue;
                    }
                }
                let proof_type = self.render_fact(&fact.expected_proposition, context)?;
                match self.render_proof_term(&fact.fact, context) {
                    Ok(proof) => {
                        let name =
                            format!("well_defined_fact_{}", fact.well_defined_fact_id.value());
                        let binders = binder_names
                            .iter()
                            .zip(binder_types.iter())
                            .map(|(binder_name, binder_type)| {
                                format!("({binder_name} : {binder_type})")
                            })
                            .collect::<Vec<_>>();
                        let helper_type = if binders.is_empty() {
                            proof_type
                        } else {
                            format!("∀ {}, {proof_type}", binders.join(" "))
                        };
                        let helper_proof = if binder_names.is_empty() {
                            format!("by\n  exact {proof}")
                        } else {
                            format!("by\n  intro {}\n  exact {proof}", binder_names.join(" "))
                        };
                        self.declarations
                            .push(format!("theorem {name} : {helper_type} :=\n{helper_proof}"));
                        self.well_defined_helpers.insert(
                            fact.well_defined_fact_id,
                            WellDefinedHelperBinding {
                                theorem_name: name.clone(),
                                binder_names: binder_names.to_vec(),
                                binder_types: binder_types.to_vec(),
                            },
                        );
                        let applied_name = if binder_names.is_empty() {
                            name
                        } else {
                            format!("({name} {})", binder_names.join(" "))
                        };
                        context
                            .well_defined_fact_names
                            .insert(fact.well_defined_fact_id, applied_name);
                        made_progress = true;
                    }
                    Err(_) => next.push(fact),
                }
            }
            if next.is_empty() || !made_progress {
                break;
            }
            remaining = next;
        }
        Ok(())
    }

    fn prepare_well_defined_facts_for_fact_type(
        &mut self,
        context: &mut RenderContext,
        fact: &Fact,
        binder_names: &[String],
        binder_types: &[String],
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
            let occurrence_ids = HashSet::from([scope.source_occurrence_id]);
            self.prepare_scoped_well_defined_facts(
                &mut scope.context,
                &well_definedness,
                &occurrence_ids,
                &scope.binder_names,
                &scope.binder_types,
            )?;
            context
                .well_defined_fact_names
                .extend(scope.context.well_defined_fact_names);
        }
        Ok(())
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
            LitexToLeanObjectIr::AnonymousFunction(function) => self
                .collect_application_scopes_from_object(
                    function.body.as_ref(),
                    context,
                    binder_names,
                    binder_types,
                    scopes,
                ),
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
        for group in forall.params_def_with_type.groups.iter() {
            for binding in group.params.iter() {
                let name = lean_name(binding.name());
                nested.symbol_names.insert(binding.id(), name.clone());
                names.push(name.clone());
                types.push("Litex.Object".to_string());

                let proof_name = format!("litex_nested_param_fact_{}", binding.id().value());
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
                    let retained_type = self.render_fact(&evidence.proposition, &nested)?;
                    if retained_type != proof_type {
                        return Err(universal_error(
                            &evidence.proposition.line_file(),
                            format!(
                                "nested parameter FactId {} does not match SymbolId {}'s declared requirement",
                                evidence.fact_id.value(),
                                binding.id().value()
                            ),
                        ));
                    }
                    nested
                        .local_fact_names
                        .insert(evidence.fact_id, proof_name.clone());
                    nested
                        .local_fact_propositions
                        .insert(evidence.fact_id, evidence.proposition.clone());
                }

                if let ParamType::Obj(Obj::FnSet(function_set)) = &group.param_type {
                    nested.function_bindings.insert(
                        binding.id(),
                        FunctionBinding {
                            function: LitexToLeanFunctionTypeIr::lower(function_set)
                                .map_err(|message| universal_error(&forall.line_file, message))?,
                            membership_proof_name: proof_name,
                        },
                    );
                }
            }
        }
        Ok((nested, names, types))
    }

    fn render_proof_term(
        &self,
        fact: &LitexToLeanFactIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match &fact.proof {
            LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => {
                self.resolve_fact_id(*source_fact_id, context)
            }
            LitexToLeanFactProofIr::Memo { proof } => {
                self.render_proof_node(&fact.proposition, proof.as_ref(), context)
            }
            proof => self.render_proof_node(&fact.proposition, proof, context),
        }
    }

    fn render_proof_node(
        &self,
        proposition: &Fact,
        proof: &LitexToLeanFactProofIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        match proof {
            LitexToLeanFactProofIr::KnownFactCitation { source_fact_id } => {
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
                LitexToLeanProofRuleIr::ClosedStandardMembership => {
                    if !parameter_requirements.is_empty() || !premises.is_empty() {
                        return Err(universal_error(
                            &proposition.line_file(),
                            "closed numeral membership unexpectedly retained premises",
                        ));
                    }
                    render_closed_standard_membership(proposition)
                }
                LitexToLeanProofRuleIr::Builtin(LitexToLeanBuiltinRuleIr::NotEqualSymmetry) => self
                    .render_not_equal_symmetry(
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
                    Ok(format!(
                        "(by\n  have litex_normalization_source := ({source})\n  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex] at litex_normalization_source ⊢\n  norm_num at litex_normalization_source ⊢\n  exact litex_normalization_source)"
                    ))
                }
                other => Err(universal_error(
                    &proposition.line_file(),
                    format!("the universal-object MVP does not yet emit proof rule `{other:?}`"),
                )),
            },
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

    fn render_known_forall_instantiation(
        &self,
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
            terms.push(self.render_proof_term(requirement, context)?);
        }
        for premise in premises {
            terms.push(self.render_proof_term(premise, context)?);
        }
        Ok(format!("({})", terms.join(" ")))
    }

    fn render_not_equal_symmetry(
        &self,
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
            "(Litex.BuiltinRules.notEqualSymmetry ({source_proof}))"
        ))
    }

    fn render_real_arithmetic_membership(
        &self,
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
        let (left, right, theorem) = match (rule, &target.element) {
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Add, Obj::Add(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "Litex.BuiltinRules.realAddClosure",
            ),
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Sub, Obj::Sub(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "Litex.BuiltinRules.realSubClosure",
            ),
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Mul, Obj::Mul(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "Litex.BuiltinRules.realMulClosure",
            ),
            (LitexToLeanRealArithmeticMembershipClosureBuiltinRuleIr::Div, Obj::Div(value)) => (
                value.left.as_ref(),
                value.right.as_ref(),
                "Litex.BuiltinRules.realDivClosure",
            ),
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
        Ok(format!("({theorem} ({left_proof}) ({right_proof}))"))
    }

    fn render_known_equality_path(
        &self,
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
        let binding = self.global_facts.get(&fact_id).ok_or_else(|| {
            universal_error(
                &default_line_file(),
                format!("no emitted Lean proof is registered for source FactId {fact_id}"),
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
            AtomicFact::EqualFact(fact) => Ok(format!(
                "{} = {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
            )),
            AtomicFact::NotEqualFact(fact) => Ok(format!(
                "{} ≠ {}",
                self.render_obj(&fact.left, context)?,
                self.render_obj(&fact.right, context)?
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
            LitexToLeanObjectIr::Number { normalized_value } => Err(universal_error(
                &default_line_file(),
                format!(
                    "the universal-object MVP currently supports natural numerals, not `{normalized_value}`"
                ),
            )),
            LitexToLeanObjectIr::StandardSet(set) => Ok(standard_set_name(*set).to_string()),
            LitexToLeanObjectIr::FunctionSet { function } => {
                self.render_function_set(function, context)
            }
            LitexToLeanObjectIr::FunctionApplication(application) => {
                self.render_function_application(application, context)
            }
            LitexToLeanObjectIr::BuiltinApp {
                operator,
                arguments,
            } => self.render_builtin_application(*operator, arguments, context),
            other => Err(universal_error(
                &default_line_file(),
                format!("the universal-object MVP does not yet render object `{other:?}`"),
            )),
        }
    }

    fn render_builtin_application(
        &self,
        operator: LitexToLeanBuiltinObjectOperatorIr,
        arguments: &[LitexToLeanObjectIr],
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
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

    fn render_function_set(
        &self,
        function: &LitexToLeanFunctionTypeIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
        let arguments_name = format!("litex_args_{}", context.function_set_depth);
        let mut nested = context.clone();
        nested.function_set_depth += 1;
        let mut requirements = Vec::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            nested.symbol_names.insert(
                parameter.symbol_id,
                format!("Litex.arg {arguments_name} {index}"),
            );
            requirements.push(format!(
                "Litex.In (Litex.arg {arguments_name} {index}) {}",
                self.render_obj_ir(&parameter.set, &nested)?
            ));
        }
        for fact in function.domain_facts.iter() {
            requirements.push(self.render_fact(fact, &nested)?);
        }
        let requirements = right_associated(requirements, " ∧ ", "True");
        let range = self.render_obj_ir(function.return_set.as_ref(), &nested)?;
        Ok(format!(
            "(Litex.FnSet ({{ arity := {}, requirements := fun {arguments_name} => {}, range := fun {arguments_name} => {} }} : Litex.FnSpec))",
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
        let LitexToLeanObjectIr::Symbol { symbol_id, .. } = application.head.as_ref() else {
            return Err(universal_error(
                &default_line_file(),
                "the universal-object MVP requires a named function head",
            ));
        };
        let binding = context.function_bindings.get(symbol_id).ok_or_else(|| {
            universal_error(
                &default_line_file(),
                "the function application has no in-scope FnSet membership fact",
            )
        })?;
        let mut current_head = self.render_obj_ir(application.head.as_ref(), context)?;
        let mut current_function = binding.function.clone();
        let mut current_membership = binding.membership_proof_name.clone();

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
            let mut rendered_arguments = Vec::new();
            for argument in arguments {
                rendered_arguments.push(self.render_obj_ir(argument, context)?);
            }
            let requirement_proof = self.render_application_requirements(
                application,
                layer_index,
                &current_function,
                context,
            )?;
            let applicable =
                format!("Litex.fnSetApplicable {current_membership} rfl ({requirement_proof})");
            let rendered_head = if layer_index == 0 {
                current_head.clone()
            } else {
                format!("({current_head})")
            };
            let applied = format!(
                "{rendered_head} [{}] ({applicable})",
                rendered_arguments.join(", ")
            );
            if layer_index + 1 == application.argument_layers.len() {
                return Ok(applied);
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
            current_membership = format!(
                "(by simpa using (Litex.fnSetResult {current_membership} rfl ({requirement_proof})))"
            );
            current_head = applied;
            current_function = next.as_ref().clone();
        }
        unreachable!("nonempty application layers return from the loop")
    }

    fn render_application_requirements(
        &self,
        application: &LitexToLeanFunctionApplicationIr,
        layer_index: usize,
        function: &LitexToLeanFunctionTypeIr,
        context: &RenderContext,
    ) -> Result<String, RuntimeError> {
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
        if requirement_proofs.is_empty() {
            return Ok("True.intro".to_string());
        }
        let mut proofs = requirement_proofs.into_iter().rev();
        let mut proof = proofs.next().expect("nonempty requirements");
        for preceding in proofs {
            proof = format!("And.intro ({preceding}) ({proof})");
        }
        Ok(format!("by simpa [Litex.arg] using ({proof})"))
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

fn render_closed_standard_membership(proposition: &Fact) -> Result<String, RuntimeError> {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
        return Err(universal_error(
            &proposition.line_file(),
            "closed standard membership proof targets a non-membership fact",
        ));
    };
    render_closed_standard_membership_object(
        &membership.element,
        &membership.set,
        &membership.line_file,
    )
}

fn render_closed_standard_membership_object(
    element: &Obj,
    set: &Obj,
    line_file: &LineFile,
) -> Result<String, RuntimeError> {
    if matches!(set, Obj::StandardSet(StandardSet::R)) {
        let (left, right, theorem) = match element {
            Obj::Add(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "Litex.BuiltinRules.realAddClosure",
            ),
            Obj::Sub(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "Litex.BuiltinRules.realSubClosure",
            ),
            Obj::Mul(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "Litex.BuiltinRules.realMulClosure",
            ),
            Obj::Div(value) => (
                Some(value.left.as_ref()),
                Some(value.right.as_ref()),
                "Litex.BuiltinRules.realDivClosure",
            ),
            _ => (None, None, ""),
        };
        if let (Some(left), Some(right)) = (left, right) {
            let left = render_closed_standard_membership_object(left, set, line_file)?;
            let right = render_closed_standard_membership_object(right, set, line_file)?;
            return Ok(format!("({theorem} ({left}) ({right}))"));
        }
    }

    let Obj::Number(number) = element else {
        return Err(universal_error(
            line_file,
            "closed standard membership proof targets an unsupported non-numeral expression",
        ));
    };
    if !number
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
    let theorem = match set {
        StandardSet::N => "Litex.BuiltinRules.numeralInN",
        StandardSet::Z => "Litex.BuiltinRules.numeralInZ",
        StandardSet::Q => "Litex.BuiltinRules.numeralInQ",
        StandardSet::R => "Litex.BuiltinRules.numeralInR",
        StandardSet::C => "Litex.BuiltinRules.numeralInC",
        _ => {
            return Err(universal_error(
                line_file,
                "refined standard-set numerals require a separate builtin theorem",
            ))
        }
    };
    Ok(format!("{} {}", theorem, number.normalized_value))
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

fn statement_label(statement: &LitexToLeanStatementIr) -> &'static str {
    match statement {
        LitexToLeanStatementIr::AbstractProp(_) => "abstract_prop",
        LitexToLeanStatementIr::Prop(_) => "prop",
        LitexToLeanStatementIr::HaveObjChoice(_) => "have object choice",
        LitexToLeanStatementIr::HaveObjEqual(_) => "have object equality",
        LitexToLeanStatementIr::HaveFnEqual(_) => "have function equality",
        LitexToLeanStatementIr::HaveExistentialWitness(_) => "existential witness",
        LitexToLeanStatementIr::NamedTheorem(_) => "named theorem",
        LitexToLeanStatementIr::Proof(_) => "proof",
        LitexToLeanStatementIr::Trust(_) => "trust",
        LitexToLeanStatementIr::Fact(_) => "fact",
        LitexToLeanStatementIr::ProjectedForall(_) => "projected forall",
    }
}

fn statement_line_file(statement: &LitexToLeanStatementIr) -> LineFile {
    match statement {
        LitexToLeanStatementIr::AbstractProp(_) | LitexToLeanStatementIr::Prop(_) => {
            default_line_file()
        }
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
        LitexToLeanStatementIr::HaveFnEqual(ir) => ir.membership.proposition.line_file(),
        LitexToLeanStatementIr::HaveExistentialWitness(ir) => ir.source.proposition.line_file(),
        LitexToLeanStatementIr::NamedTheorem(ir) => ir.theorem.proposition.line_file(),
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
        LitexToLeanStatementIr::ProjectedForall(ir) => ir.source.line_file(),
    }
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
            assert!(
                output.starts_with(
                    "import Litex.BuiltinRules\n\nexample : Litex.abiVersion = 1 := rfl\n"
                ),
                "{output}"
            );
            assert!(!output.contains("import Mathlib"), "{output}");
            assert!(!output.contains("axiom Object : Type"), "{output}");
            assert!(!output.contains("LitexObject"), "{output}");
            assert!(
                output.contains("(a : Litex.Object)")
                    && output.contains("Litex.In a Litex.C")
                    && output.contains("Litex.In a Litex.R"),
                "{output}"
            );
            assert!(output.contains("f [a] (Litex.fnSetApplicable"), "{output}");
            assert!(
                output.contains("theorem well_defined_fact_2")
                    && output.contains("theorem well_defined_fact_3")
                    && output.contains("well_defined_fact_3"),
                "{output}"
            );
            assert!(!output.contains("Set ℝ"), "{output}");
            assert!(!output.contains("(a : ℂ)"), "{output}");
            assert!(!output.contains("downcast"), "{output}");
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
            assert!(output.contains("axiom fact"), "{output}");
            assert!(output.contains("marked a"), "{output}");
            assert!(!output.contains("assumption"), "{output}");
            assert!(!output.contains("Set ℝ"), "{output}");
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
            assert!(
                output.contains("Litex.BuiltinRules.notEqualSymmetry"),
                "{output}"
            );
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
            assert!(output.contains("Eq.symm (litex_domain_fact_1)"), "{output}");
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
            runtime.replace_litex_to_lean_ir_mode(true);
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
                &mut statement.fact.proof
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
    fn exact_source_application_layers_use_lists_and_fn_set_result() {
        run_with_large_stack(|| {
            let source = r#"forall f fn(x, y, z R) R:
    f(1, 2, 3) = f(1, 2, 3)

forall g fn(x R) fn(y R) R:
    g(1)(2) = g(1)(2)
"#;
            let output = compile_to_lean_from_source(source, "exact-application-layers.lit")
                .expect("one-layer and nested applications should compile");
            assert!(output.contains("f [1, 2, 3]"), "{output}");
            assert!(output.contains("g [1]"), "{output}");
            assert!(output.contains(") [2]"), "{output}");
            assert!(output.contains("Litex.fnSetResult"), "{output}");
            assert!(
                output.contains("And.intro ((well_defined_fact_")
                    && output.matches("theorem well_defined_fact_").count() >= 5,
                "{output}"
            );
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
            assert!(output.contains("Litex.BuiltinRules"), "{output}");
            assert!(output.contains("well_defined_fact_"), "{output}");
            assert!(!output.contains("(y : ℝ)"), "{output}");
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
            runtime.replace_litex_to_lean_ir_mode(true);
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
                    .map(|requirement| requirement.well_defined_obj_proof_id)
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
