use super::*;

/// Compiles the recursive output of Litex statement execution into Lean source.
///
/// The compiler owns a stack of Lean-generation environments in the same way
/// that [`Runtime`] owns execution environments. The stack contains generated
/// names and source fragments only; all proof evidence comes from `StmtResult`.
pub struct StmtResultToLeanCompiler {
    /// Dedicated allocator for compiler-synthesized fact views. These facts
    /// are still canonical runtime facts; the compiler keeps its own runtime
    /// because it does not execute source statements.
    pub(super) runtime: Runtime,
    pub(super) source_label: String,
    pub(super) environment_stack: StmtResultToLeanCompilerEnvironmentStack,
    pub(super) declarations: Vec<String>,
    pub(super) next_fact_name_index: usize,
    pub(super) next_local_inference_name_index: usize,
    pub(super) next_sketch_namespace_index: usize,
}

pub(super) struct CompiledOrdinaryFactGoalProofBody {
    pub(super) local_proof_lines: Vec<String>,
    pub(super) proposition: String,
    pub(super) conclusion_proof: String,
}

pub(super) struct CompiledNamedForallStatementProofBody {
    pub(super) binder_declarations: Vec<String>,
    pub(super) binder_intro_names: Vec<String>,
    pub(super) proof_lines: Vec<String>,
    pub(super) conclusion_type: String,
}

/// Borrowed, compiler-only view of the common recursive Result shape shared
/// by a named theorem and a verified strategy definition. This is not another
/// semantic IR: every field points into the canonical `SuccessStmtResult`.
pub(super) struct NamedForallStatementResultCompilationInput<'a> {
    pub(super) name: &'a str,
    pub(super) forall_fact: &'a ForallFact,
    pub(super) well_definedness: &'a WellDefinedFactResult,
    pub(super) proof_scope_assumption_infers: &'a SuccessInferResult,
    pub(super) proof_scope_assumption_components: &'a [(FactId, Fact)],
    pub(super) proof_steps: &'a [StmtResult],
    /// Borrowed leaves selected from the recursive Result. This Vec only
    /// carries references and therefore is not a second semantic IR.
    pub(super) conclusion_checks: Vec<&'a VerifyFactResult>,
    pub(super) outer_environment_effects: Option<&'a SuccessInferResult>,
    pub(super) source_fact_id: Option<FactId>,
}

#[derive(Clone, Copy)]
pub(super) enum RegisteredPredicatePropertyCompilationKind {
    Reflexive,
    Symmetric,
    Transitive,
}

impl RegisteredPredicatePropertyCompilationKind {
    pub(super) fn result_name(self) -> &'static str {
        match self {
            Self::Reflexive => "reflexive",
            Self::Symmetric => "symmetric",
            Self::Transitive => "transitive",
        }
    }
}

pub(super) struct CompiledExistentialWitnessProofBody {
    pub(super) proposition: String,
    pub(super) proof_expression: String,
}

pub(super) struct CompiledNonemptySetWitnessProofBody {
    pub(super) proposition: String,
    pub(super) local_proof_lines: Vec<String>,
}

pub(super) struct CompiledFactProofBody {
    pub(super) fact: Fact,
    pub(super) proposition: String,
    pub(super) proof_expression: String,
}

pub(super) struct CompiledDirectForallProofBody {
    pub(super) proposition: String,
    pub(super) proof_expression: String,
    pub(super) parameter_premises: Vec<LeanLocalFactPremise>,
    pub(super) premises: Vec<LeanLocalFactPremise>,
    pub(super) conclusions: Vec<(FactId, Fact)>,
}

/// One exact theorem publication selected from a successful `ForallProof`
/// store Result. Runtime may store the complete source forall, or one theorem
/// per conclusion with source binders that the conclusion does not use
/// removed. This is a short-lived compiler selection over Result-owned data,
/// not another proof or statement IR.
pub(super) struct DirectForallResultPublicationSelection {
    pub(super) forall_fact: ForallFact,
    pub(super) stored_fact_id: Option<FactId>,
    pub(super) source_parameter_indices: Vec<usize>,
    /// Distinct source conclusions whose child Results must be replayed.
    pub(super) source_conclusion_indices: Vec<usize>,
    /// Conclusions exposed by the published forall, in target order. Each
    /// item is backed either by the source conclusion's FactId or by one of
    /// that child's typed inferred FactIds.
    pub(super) published_conclusions: Vec<(usize, FactId, Fact)>,
}

pub(super) struct CompiledByDefinitionComponentProofBody {
    pub(super) fact: Fact,
    pub(super) retained_fact_id: Option<FactId>,
    pub(super) proposition: String,
    pub(super) proof_expression: String,
}

pub(super) struct CompiledByDefinitionProofBody {
    pub(super) target: CompiledFactProofBody,
    pub(super) components: Vec<CompiledByDefinitionComponentProofBody>,
}

pub(super) struct CompiledTheoremApplicationConclusionProofBody {
    pub(super) retained_fact_id: Option<FactId>,
    pub(super) fact: Fact,
    pub(super) proposition: String,
    pub(super) proof_expression: String,
}

pub(super) struct CompiledRealAnalysisTheoremApplicationProofBody {
    pub(super) local_prerequisite_lines: Vec<String>,
    pub(super) conclusion: CompiledTheoremApplicationConclusionProofBody,
}

pub(super) struct CompiledByTheoremSelectionProofBody {
    pub(super) fact: Fact,
    pub(super) retained_fact_id: FactId,
    pub(super) proposition: String,
    pub(super) proof_lines: Vec<String>,
}

pub(super) struct CompiledFiniteAssignmentBranch {
    pub(super) local_lines: Vec<String>,
    pub(super) exit_proof: String,
}

pub(super) enum StructuredIntegerInductionConclusionPosition {
    Base,
    Step,
}

/// Target-language construction output for one reviewed native-numeric function
/// Result. This is not another statement IR: it exists only while the parent
/// `SuccessHaveFnEqualStmtResult` method wraps its child-scope compilation in
/// persistent Lean declarations.
pub(super) struct CompiledNamedFunctionDefinitionBody {
    pub(super) function: LeanTargetFunctionTypeRepresentation,
    pub(super) source_body: Obj,
    pub(super) lowered_body: LeanTargetObjectRepresentation,
    pub(super) value: String,
    pub(super) native_body_carrier: NativeFunctionBodyCarrier,
    pub(super) parameter_premises: Vec<LeanLocalFactPremise>,
    pub(super) domain_premises: Vec<LeanLocalFactPremise>,
}

/// Exact target-side views retained while replaying one checked named-function
/// reduction. The source argument remains necessary because an outer compiler
/// environment may render it through a membership-selected numeric
/// representative, while a closed literal continues to render as the source
/// value itself.
pub(super) struct CheckedNamedFunctionReductionArgumentEvidence {
    pub(super) source_argument: Obj,
    pub(super) rendered_source_argument: String,
    pub(super) membership_proof: String,
    pub(super) parameter_set: LeanTargetObjectRepresentation,
    pub(super) native_integer_argument: Option<String>,
    pub(super) native_real_argument: Option<String>,
    pub(super) closed_positive_natural_argument: Option<String>,
}

/// Target-language construction output returned from the tuple index scope.
/// The recursive WD Result remains owned by the statement result; this value
/// contains only what the parent needs after the compiler environment pops.
pub(super) struct CompiledIndexedTupleDefinitionBody {
    pub(super) dimension: usize,
    pub(super) value: String,
    pub(super) positive_dimension_proof: String,
    pub(super) at_least_two_dimension_proof: String,
}

/// Target-language construction output returned from one indexed-function
/// child scope. Sequence, finite-sequence, and matrix Results differ only in
/// how many parameter and domain premises their nested scopes publish, so the
/// parent compiler consumes one common shape instead of three parallel
/// temporary structures.
pub(super) struct CompiledIndexedFunctionDefinitionBody {
    pub(super) function: LeanTargetFunctionTypeRepresentation,
    pub(super) source_body: Obj,
    pub(super) lowered_body: LeanTargetObjectRepresentation,
    pub(super) value: String,
    pub(super) parameter_premises: Vec<LeanLocalFactPremise>,
    pub(super) domain_premises: Vec<LeanLocalFactPremise>,
}

#[derive(Clone, Copy)]
pub(super) enum DefinedPredicateInferenceConclusionPublication {
    PersistentLeanTheorem,
    LocalProofExpression,
}

impl StmtResultToLeanCompiler {
    pub fn new(source_label: &str) -> Self {
        Self {
            runtime: Runtime::new_with_fact_id_start(RuntimeOptions::default(), 1 << 63),
            source_label: source_label.to_string(),
            environment_stack: StmtResultToLeanCompilerEnvironmentStack::default(),
            declarations: Vec::new(),
            next_fact_name_index: 0,
            next_local_inference_name_index: 0,
            next_sketch_namespace_index: 0,
        }
    }

    /// Build the temporary Lean-rendering index directly from the recursive
    /// WD Result, then compile every retained argument/domain verification
    /// through the ordinary direct fact-result compiler.
    pub(super) fn construct_well_definedness_to_lean_compilation_context(
        &mut self,
        result: &WellDefinedFactResult,
    ) -> Result<StmtResultWellDefinednessToLeanCompilationContext, String> {
        let context = self.collect_well_definedness_to_lean_compilation_context(result)?;
        self.compile_precollected_well_definedness_context(context, &[result.proof.as_ref()])
    }

    pub(super) fn collect_well_definedness_to_lean_compilation_context(
        &self,
        result: &WellDefinedFactResult,
    ) -> Result<StmtResultWellDefinednessToLeanCompilationContext, String> {
        let mut context = StmtResultWellDefinednessToLeanCompilationContext::default();
        collect_well_definedness_to_lean_context_from_fact_result(
            result.proof.as_ref(),
            &mut context,
        )?;
        Ok(context)
    }

    /// Compile a context assembled from one enclosing local binder and all of
    /// its ordered body facts. Concrete proposition definitions use this
    /// because their WD evidence is owned by the definition Result rather than
    /// by a synthetic fact statement.
    pub(super) fn construct_def_prop_well_definedness_to_lean_compilation_context(
        &mut self,
        local: &SuccessVerifyDefPropLocalEnvResult,
    ) -> Result<StmtResultWellDefinednessToLeanCompilationContext, String> {
        let context = self.collect_def_prop_well_definedness_to_lean_compilation_context(local)?;
        let mut roots = Vec::with_capacity(local.body.len());
        for body in &local.body {
            roots.push(body.well_definedness.as_ref());
        }
        self.compile_precollected_well_definedness_context(context, &roots)
    }

    /// Validate and index every Result-owned binder/body WD node without
    /// prematurely rendering proofs that live below those lexical binders.
    /// Exact semantic lowerings consume this complete index directly; generic
    /// predicate lowering additionally freezes its renderable proof slots.
    pub(super) fn collect_def_prop_well_definedness_to_lean_compilation_context(
        &self,
        local: &SuccessVerifyDefPropLocalEnvResult,
    ) -> Result<StmtResultWellDefinednessToLeanCompilationContext, String> {
        let mut context = StmtResultWellDefinednessToLeanCompilationContext::default();
        collect_well_definedness_to_lean_context_from_fact_binder(&local.binder, &mut context)?;
        for body in &local.body {
            collect_well_definedness_to_lean_context_from_fact_result(
                &body.well_definedness,
                &mut context,
            )?;
        }
        Ok(context)
    }

    pub(super) fn compile_precollected_well_definedness_context(
        &mut self,
        context: StmtResultWellDefinednessToLeanCompilationContext,
        roots: &[&SuccessVerifyFactWellDefinedProofResult],
    ) -> Result<StmtResultWellDefinednessToLeanCompilationContext, String> {
        // Compile the certificate inside a disposable lexical frame. Exact
        // intrinsic stores owned by this WD tree may be cited by another
        // sibling object requirement (notably a comparison chain), but must
        // not escape into the enclosing statement environment.
        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(context);
        let requirement_locations = self
            .environment_stack
            .well_definedness
            .as_ref()
            .expect("WD compilation context was just installed")
            .function_applications
            .iter()
            .flat_map(|(object_key, application)| {
                application
                    .layers
                    .iter()
                    .enumerate()
                    .flat_map(move |(layer_index, layer)| {
                        layer.requirements.iter().enumerate().map(
                            move |(requirement_index, requirement)| {
                                (
                                    object_key.clone(),
                                    layer_index,
                                    requirement_index,
                                    requirement.verification.clone(),
                                )
                            },
                        )
                    })
            })
            .collect::<Vec<_>>();

        let compilation_result: Result<(), String> = (|| {
            // Anonymous-function rendering is needed by aggregate intrinsic
            // stores, while its own body proof can replay application
            // requirements under the binder aliases. Compile those closures
            // first, then expose the exact sibling stores, then freeze the
            // remaining application requirement proofs.
            let anonymous_function_keys = self
                .environment_stack
                .well_definedness
                .as_ref()
                .expect("WD compilation context remains active")
                .anonymous_functions
                .keys()
                .cloned()
                .collect::<Vec<_>>();
            for object_key in anonymous_function_keys {
                self.compile_anonymous_function_well_definedness_context(&object_key)
                    .map_err(|error| {
                        format!("compiling anonymous-function WD context `{object_key}`: {error}")
                    })?;
            }
            for recursive in roots {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    recursive,
                    &mut self.environment_stack,
                )
                .map_err(|error| format!("installing fact-WD intrinsic stores: {error}"))?;
            }
            for (object_key, layer_index, requirement_index, verification) in requirement_locations
            {
                let proof_expression = match self
                    .construct_lean_proof_from_shared_verify_fact_result(verification.as_ref())
                {
                    Ok(Some(proof_expression)) => Some(proof_expression),
                    // A requirement nested below a forall binder can cite a
                    // parameter FactId that is intentionally unavailable in
                    // this outer environment. Retain the recursive Result and
                    // construct its proof only when the renderer enters that
                    // binder and installs its exact aliases.
                    Err(error) if error.contains("unavailable cited fact") => None,
                    Ok(None) => {
                        return Err(format!(
                            "function application `{}` layer {} requirement {} has no direct fact-result proof compiler",
                            object_key,
                            layer_index,
                            requirement_index,
                        ));
                    }
                    Err(error) => return Err(error),
                };
                self.environment_stack
                    .well_definedness
                    .as_mut()
                    .expect("WD compilation context remains active")
                    .function_applications
                    .get_mut(&object_key)
                    .expect("collected function application remains indexed")
                    .layers[layer_index]
                    .requirements[requirement_index]
                    .proof_expression = proof_expression;
            }
            Ok(())
        })();
        let completed = self
            .environment_stack
            .well_definedness
            .take()
            .expect("WD compilation context remains active");
        self.environment_stack.pop_local_environment();
        compilation_result?;
        Ok(completed)
    }

    pub(super) fn compile_anonymous_function_well_definedness_context(
        &mut self,
        object_key: &str,
    ) -> Result<(), String> {
        let anonymous_context = self
            .environment_stack
            .well_definedness
            .as_ref()
            .and_then(|context| context.anonymous_functions.get(object_key))
            .cloned()
            .ok_or_else(|| {
                format!("anonymous function `{object_key}` disappeared from its WD Result context")
            })?;
        let Obj::AnonymousFn(source_function) = &anonymous_context.source_function else {
            return Err("anonymous-function compilation context retained another object".into());
        };
        let function = LeanTargetFunctionTypeRepresentation::lower_anonymous(source_function)?;
        if function.parameters.len() != anonymous_context.parameters.len()
            || function.domain_facts.len() != anonymous_context.domains.len()
        {
            return Err("anonymous-function WD Result changed its binder arity".into());
        }

        self.environment_stack.push_inherited_environment();
        let compilation: Result<_, String> = (|| {
            let uses_telescope = function_uses_telescope(&function);
            let mut allowed_sources = Vec::new();
            for (parameter_index, (parameter, premise)) in function
                .parameters
                .iter()
                .zip(anonymous_context.parameters.iter())
                .enumerate()
            {
                if premise.symbol_id != Some(parameter.symbol_id)
                    || !matches!(
                        premise.role,
                        WellDefinedBinderPremiseRole::ParameterMembership { .. }
                    )
                {
                    return Err(format!(
                        "anonymous function parameter {parameter_index} changed its Result-owned premise"
                    ));
                }
                let suffix = if uses_telescope {
                    (parameter_index + 1).to_string()
                } else {
                    String::new()
                };
                let argument = format!("__arg{suffix}");
                let membership = format!("__arg{suffix}_in");
                self.environment_stack
                    .symbol_names
                    .insert(parameter.symbol_id, argument.clone());
                self.environment_stack
                    .fact_names
                    .insert(premise.fact_id, membership.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(premise.fact_id, premise.proposition.clone());
                install_numeric_representations_from_membership(
                    parameter.symbol_id,
                    &parameter.set,
                    &argument,
                    &membership,
                    &mut self.environment_stack,
                );
                allowed_sources.push((premise.fact_id, premise.proposition.clone()));
            }
            for (domain_index, premise) in anonymous_context.domains.iter().enumerate() {
                if !matches!(premise.role, WellDefinedBinderPremiseRole::Domain { .. }) {
                    return Err(format!(
                        "anonymous function domain {domain_index} changed its Result-owned role"
                    ));
                }
                let selector = conjunction_selector(domain_index, anonymous_context.domains.len())?;
                let name = if anonymous_context.domains.len() == 1 {
                    "__arg_domain".to_string()
                } else {
                    format!("__arg_domain{selector}")
                };
                self.environment_stack
                    .fact_names
                    .insert(premise.fact_id, name);
                self.environment_stack
                    .fact_propositions
                    .insert(premise.fact_id, premise.proposition.clone());
                allowed_sources.push((premise.fact_id, premise.proposition.clone()));
            }

            let compiled_inference_fact_proof_steps =
                if anonymous_context.assumption_infers.is_empty() {
                    Vec::new()
                } else {
                    self.compile_typed_inference_results_in_current_compiler_environment(
                        &anonymous_context.assumption_infers,
                        &allowed_sources,
                        CompiledInferenceFactAvailabilityInLeanEnvironment::LocalProofName,
                        "anonymous-function binder inference Result",
                        None,
                    )?
                };
            let mut visited_body_results = HashSet::new();
            install_object_well_definedness_store_results_for_source(
                &anonymous_context.body_source_object,
                anonymous_context.body_well_definedness.as_ref(),
                &mut self.environment_stack,
                &mut visited_body_results,
            )?;
            let closure_proof = match anonymous_context.closure.role {
                WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => Some(
                    self.construct_lean_proof_from_shared_verify_fact_result(
                        anonymous_context.closure.verification.as_ref(),
                    )?
                    .ok_or_else(|| {
                        "anonymous function body-membership Result has no direct proof compiler"
                            .to_string()
                    })?,
                ),
                WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
                    ..
                } => None,
                role => {
                    return Err(format!(
                        "anonymous function retained unsupported closure role {role:?}"
                    ));
                }
            };
            Ok((compiled_inference_fact_proof_steps, closure_proof))
        })();
        self.environment_stack.pop_local_environment();
        let (compiled_inference_fact_proof_steps, closure_proof) = compilation?;
        let retained = self
            .environment_stack
            .well_definedness
            .as_mut()
            .and_then(|context| context.anonymous_functions.get_mut(object_key))
            .expect("anonymous function remains in active WD Result context");
        retained.compiled_inference_fact_proof_steps = compiled_inference_fact_proof_steps;
        retained.closure.proof_expression = closure_proof;
        Ok(())
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/kernel_contracts/stmt_result_to_lean_compiler/mod.rs"]
mod tests;
