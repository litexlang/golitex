use super::compiler_environment::*;
use super::lean_compilation_types::*;
use super::registered_local_builtin_rule_identifiers_for_lean::*;
use super::represent_litex_function_contracts_in_lean::*;
use super::represent_litex_objects_in_lean::*;
use crate::prelude::*;
use crate::verify::local_builtin_catalog::registered_local_builtin_fingerprint_by_id;
use crate::verify::rule_schema::{canonical_objs_equal, MatchLimits, RuleFingerprint, RuleId};
use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};
use std::collections::{HashMap, HashSet};
use std::mem;
use std::path::Path;
use std::rc::Rc;

#[path = "implementation/builtin_evidence_compilation.rs"]
mod builtin_evidence_compilation;
#[path = "implementation/compilation_lifecycle.rs"]
mod compilation_lifecycle;
#[path = "implementation/fact_compilation.rs"]
mod fact_compilation;
#[path = "implementation/fact_proof_dispatch.rs"]
mod fact_proof_dispatch;
#[path = "implementation/fact_proof_replay.rs"]
mod fact_proof_replay;
#[path = "implementation/object_statements.rs"]
mod object_statements;
#[path = "implementation/proof_rendering.rs"]
mod proof_rendering;
#[path = "implementation/result_dispatch.rs"]
mod result_dispatch;
#[path = "implementation/source_rendering.rs"]
mod source_rendering;
#[path = "implementation/structured_proofs.rs"]
mod structured_proofs;
#[path = "implementation/theorem_compilation.rs"]
mod theorem_compilation;
#[path = "implementation/validation.rs"]
mod validation;

use proof_rendering::*;
use source_rendering::*;
use validation::*;

/// Compiles the recursive output of Litex statement execution into Lean source.
///
/// The compiler owns a stack of Lean-generation environments in the same way
/// that [`Runtime`] owns execution environments. The stack contains generated
/// names and source fragments only; all proof evidence comes from `StmtResult`.
pub struct StmtResultToLeanCompiler {
    source_label: String,
    environment_stack: StmtResultToLeanCompilerEnvironmentStack,
    declarations: Vec<String>,
    next_fact_name_index: usize,
    next_local_inference_name_index: usize,
    next_sketch_namespace_index: usize,
}

struct CompiledOrdinaryFactGoalProofBody {
    local_proof_lines: Vec<String>,
    proposition: String,
    conclusion_proof: String,
}

struct CompiledNamedForallStatementProofBody {
    binder_declarations: Vec<String>,
    binder_intro_names: Vec<String>,
    proof_lines: Vec<String>,
    conclusion_type: String,
}

/// Borrowed, compiler-only view of the common recursive Result shape shared
/// by a named theorem and a verified strategy definition. This is not another
/// semantic IR: every field points into the canonical `SuccessStmtResult`.
struct NamedForallStatementResultCompilationInput<'a> {
    name: &'a str,
    forall_fact: &'a ForallFact,
    well_definedness: &'a SuccessVerifyFactWellDefinedResult,
    proof_scope_assumption_infers: &'a SuccessInferResult,
    proof_scope_assumption_components: &'a [(FactId, Fact)],
    proof_steps: &'a [StmtResult],
    /// Borrowed leaves selected from the recursive Result. This Vec only
    /// carries references and therefore is not a second semantic IR.
    conclusion_checks: Vec<&'a StmtResult>,
    outer_statement_common: Option<&'a SuccessStmtCommonResult>,
}

#[derive(Clone, Copy)]
enum RegisteredPredicatePropertyCompilationKind {
    Reflexive,
    Symmetric,
    Transitive,
    Antisymmetric,
}

impl RegisteredPredicatePropertyCompilationKind {
    fn result_name(self) -> &'static str {
        match self {
            Self::Reflexive => "reflexive",
            Self::Symmetric => "symmetric",
            Self::Transitive => "transitive",
            Self::Antisymmetric => "antisymmetric",
        }
    }
}

struct CompiledExistentialWitnessProofBody {
    proposition: String,
    proof_expression: String,
}

struct CompiledNonemptySetWitnessProofBody {
    proposition: String,
    local_proof_lines: Vec<String>,
}

struct CompiledFactProofBody {
    fact: Fact,
    proposition: String,
    proof_expression: String,
}

struct CompiledDirectForallProofBody {
    proposition: String,
    proof_expression: String,
    parameter_premises: Vec<LeanLocalFactPremise>,
    premises: Vec<LeanLocalFactPremise>,
    conclusions: Vec<(FactId, Fact)>,
}

/// One exact theorem publication selected from a successful `ForallProof`
/// store Result. Runtime may store the complete source forall, or one theorem
/// per conclusion with source binders that the conclusion does not use
/// removed. This is a short-lived compiler selection over Result-owned data,
/// not another proof or statement IR.
struct DirectForallResultPublicationSelection {
    forall_fact: ForallFact,
    stored_fact_id: Option<FactId>,
    source_parameter_indices: Vec<usize>,
    source_conclusion_indices: Vec<usize>,
}

struct CompiledByDefinitionComponentProofBody {
    fact: Fact,
    retained_fact_id: Option<FactId>,
    proposition: String,
    proof_expression: String,
}

struct CompiledByDefinitionProofBody {
    target: CompiledFactProofBody,
    components: Vec<CompiledByDefinitionComponentProofBody>,
}

struct CompiledLitexTheoremInstantiationConclusionProofBody {
    retained_fact_id: Option<FactId>,
    fact: Fact,
    proposition: String,
    proof_expression: String,
}

struct CompiledFiniteAssignmentBranch {
    local_lines: Vec<String>,
    exit_proof: String,
}

enum StructuredIntegerInductionConclusionPosition {
    Base,
    Step,
}

/// Target-language construction output for one reviewed native-numeric function
/// Result. This is not another statement IR: it exists only while the parent
/// `SuccessHaveFnEqualStmtResult` method wraps its child-scope compilation in
/// persistent Lean declarations.
struct CompiledNamedFunctionDefinitionBody {
    function: LeanTargetFunctionTypeRepresentation,
    source_body: Obj,
    lowered_body: LeanTargetObjectRepresentation,
    value: String,
    native_body_carrier: NativeFunctionBodyCarrier,
    parameter_premises: Vec<LeanLocalFactPremise>,
    domain_premises: Vec<LeanLocalFactPremise>,
}

/// Exact target-side views retained while replaying one checked named-function
/// reduction. The source argument remains necessary because an outer compiler
/// environment may render it through a membership-selected numeric
/// representative, while a closed literal continues to render as the source
/// value itself.
struct CheckedNamedFunctionReductionArgumentEvidence {
    source_argument: Obj,
    rendered_source_argument: String,
    membership_proof: String,
    parameter_set: LeanTargetObjectRepresentation,
    native_integer_argument: Option<String>,
}

/// Target-language construction output returned from the tuple index scope.
/// The recursive WD Result remains owned by the statement result; this value
/// contains only what the parent needs after the compiler environment pops.
struct CompiledIndexedTupleDefinitionBody {
    dimension: usize,
    value: String,
    positive_dimension_proof: String,
    at_least_two_dimension_proof: String,
}

/// Target-language construction output returned from one indexed-function
/// child scope. Sequence, finite-sequence, and matrix Results differ only in
/// how many parameter and domain premises their nested scopes publish, so the
/// parent compiler consumes one common shape instead of three parallel
/// temporary structures.
struct CompiledIndexedFunctionDefinitionBody {
    function: LeanTargetFunctionTypeRepresentation,
    source_body: Obj,
    lowered_body: LeanTargetObjectRepresentation,
    value: String,
    parameter_premises: Vec<LeanLocalFactPremise>,
    domain_premises: Vec<LeanLocalFactPremise>,
}

#[derive(Clone, Copy)]
enum DefinedPredicateInferenceConclusionPublication {
    PersistentLeanTheorem,
    LocalProofExpression,
}

impl StmtResultToLeanCompiler {
    pub fn new(source_label: &str) -> Self {
        Self {
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
    fn construct_well_definedness_to_lean_compilation_context(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
    ) -> Result<StmtResultWellDefinednessToLeanCompilationContext, String> {
        let mut context = StmtResultWellDefinednessToLeanCompilationContext::default();
        let recursive = result
            .recursive
            .as_deref()
            .ok_or_else(|| "successful fact WD result has no recursive proof".to_string())?;
        collect_well_definedness_to_lean_context_from_fact_result(recursive, &mut context)?;

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
            .flat_map(|(occurrence_id, application)| {
                application
                    .layers
                    .iter()
                    .enumerate()
                    .flat_map(move |(layer_index, layer)| {
                        layer.requirements.iter().enumerate().map(
                            move |(requirement_index, requirement)| {
                                (
                                    *occurrence_id,
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
            let anonymous_function_occurrences = self
                .environment_stack
                .well_definedness
                .as_ref()
                .expect("WD compilation context remains active")
                .anonymous_functions
                .keys()
                .copied()
                .collect::<Vec<_>>();
            for occurrence_id in anonymous_function_occurrences {
                self.compile_anonymous_function_well_definedness_context(occurrence_id)?;
            }
            install_fact_well_definedness_proof_store_results_in_active_environment(
                recursive,
                &mut self.environment_stack,
            )?;
            for (occurrence_id, layer_index, requirement_index, verification) in
                requirement_locations
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
                            "function application occurrence {} layer {} requirement {} has no direct fact-result proof compiler",
                            occurrence_id.value(),
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
                    .get_mut(&occurrence_id)
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

    fn compile_anonymous_function_well_definedness_context(
        &mut self,
        occurrence_id: SourceObjectOccurrenceId,
    ) -> Result<(), String> {
        let anonymous_context = self
            .environment_stack
            .well_definedness
            .as_ref()
            .and_then(|context| context.anonymous_functions.get(&occurrence_id))
            .cloned()
            .ok_or_else(|| {
                format!(
                    "anonymous function occurrence {} disappeared from its WD Result context",
                    occurrence_id.value()
                )
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
            .and_then(|context| context.anonymous_functions.get_mut(&occurrence_id))
            .expect("anonymous function remains in active WD Result context");
        retained.compiled_inference_fact_proof_steps = compiled_inference_fact_proof_steps;
        retained.closure.proof_expression = closure_proof;
        Ok(())
    }
}

#[cfg(test)]
#[path = "../../tests/unit/kernel_contracts/stmt_result_to_lean_compiler/mod.rs"]
mod tests;
