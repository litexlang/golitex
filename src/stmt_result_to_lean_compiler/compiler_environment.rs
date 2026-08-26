use super::lean_compilation_types::{CompiledInferenceFactProofStep, LeanLocalFactPremise};
use super::represent_litex_function_contracts_in_lean::LeanTargetFunctionTypeRepresentation;
use super::represent_litex_objects_in_lean::LeanTargetObjectRepresentation;
use crate::prelude::*;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

/// Lexical Lean-generation environments owned by `StmtResultToLeanCompiler`.
///
/// A child frame inherits every binding visible in its parent. Bindings added
/// to the child disappear when the child Result scope is left.
#[derive(Clone)]
pub(super) struct StmtResultToLeanCompilerEnvironmentStack {
    pub(super) environments: Vec<StmtResultToLeanCompilerEnvironment>,
    /// WD compilation context follows Result nesting, but is deliberately not
    /// cloned into the persistent symbol/fact binding repository.
    pub(super) well_definedness: Option<StmtResultWellDefinednessToLeanCompilationContext>,
    parent_well_definedness_contexts:
        Vec<Option<StmtResultWellDefinednessToLeanCompilationContext>>,
}

impl Default for StmtResultToLeanCompilerEnvironmentStack {
    fn default() -> Self {
        Self {
            environments: vec![StmtResultToLeanCompilerEnvironment::default()],
            well_definedness: None,
            parent_well_definedness_contexts: Vec::new(),
        }
    }
}

impl Deref for StmtResultToLeanCompilerEnvironmentStack {
    type Target = StmtResultToLeanCompilerEnvironment;

    fn deref(&self) -> &Self::Target {
        self.environments
            .last()
            .expect("compiler environment stack must retain its top-level environment")
    }
}

impl DerefMut for StmtResultToLeanCompilerEnvironmentStack {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.environments
            .last_mut()
            .expect("compiler environment stack must retain its top-level environment")
    }
}

impl StmtResultToLeanCompilerEnvironmentStack {
    pub(super) fn push_inherited_environment(&mut self) {
        let inherited = self
            .environments
            .last()
            .cloned()
            .expect("compiler environment stack must retain its top-level environment");
        self.environments.push(inherited);
        self.parent_well_definedness_contexts
            .push(self.well_definedness.clone());
    }

    pub(super) fn pop_local_environment(&mut self) {
        assert!(
            self.environments.len() > 1,
            "compiler cannot pop its top-level environment"
        );
        self.environments.pop();
        self.well_definedness = self
            .parent_well_definedness_contexts
            .pop()
            .expect("compiler WD context stack must match lexical environments");
    }

    pub(super) fn is_top_level(&self) -> bool {
        self.environments.len() == 1
    }
}

/// Names and target-representation choices visible in one Lean lexical scope.
/// This is compiler state, not a second statement/proof IR.
#[derive(Clone, Default)]
pub(super) struct StmtResultToLeanCompilerEnvironment {
    /// All source identities and chosen Lean representations visible in this
    /// lexical environment. Grouping them makes it explicit that they are one
    /// compiler symbol/fact binding repository, not statement proof evidence.
    pub(super) bindings: StmtResultToLeanCompilerBindings,
}

impl Deref for StmtResultToLeanCompilerEnvironment {
    type Target = StmtResultToLeanCompilerBindings;

    fn deref(&self) -> &Self::Target {
        &self.bindings
    }
}

impl DerefMut for StmtResultToLeanCompilerEnvironment {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bindings
    }
}

#[derive(Clone, Default)]
pub(super) struct StmtResultToLeanCompilerBindings {
    pub(super) symbol_names: HashMap<SymbolId, String>,
    /// Executed `let` definitions only. This is separate from numeric
    /// substitutions because WD rendering may transport a callable contract
    /// across a transparent alias, while ordinary `have a = b` must not gain
    /// that behavior.
    pub(super) transparent_object_definitions:
        HashMap<SymbolId, CompilerTransparentObjectDefinition>,
    /// Canonical complex observations for numeric symbols whose Lean carrier
    /// is locally heterogeneous (for example a dependent function binder).
    pub(super) numeric_representations: HashMap<SymbolId, String>,
    /// Exact semantic-equality bridge from the source symbol to the numeric
    /// Complex observation selected by its visible membership proof. Proof
    /// consumers use this to transport source-domain sign facts into the same
    /// representative used when their target expression is rendered.
    pub(super) numeric_representation_equalities: HashMap<SymbolId, String>,
    pub(super) numeric_representation_memberships: HashMap<SymbolId, String>,
    pub(super) numeric_real_values: HashMap<SymbolId, String>,
    /// Exact integer representatives selected by visible `N+`/`N`/`Z`
    /// membership proofs. Integer-only source operators such as `%` consume
    /// this target representation instead of pretending Complex has a native
    /// remainder operation.
    pub(super) numeric_integer_values: HashMap<SymbolId, String>,
    /// Exact rational representatives selected by visible `N+`/`N`/`Z`/`Q`
    /// memberships. Rational integer powers are rendered in `ℚ` and then
    /// observed through the ordinary Litex complex carrier.
    pub(super) numeric_rational_values: HashMap<SymbolId, String>,
    /// Native integer equalities introduced by an enclosing finite iteration
    /// Result. Runtime-resolved numeric child Results may use them only while
    /// that exact assignment frame is active.
    pub(super) runtime_resolved_numeric_comparison_rewrites: Vec<String>,
    /// Exact source substitutions installed by enclosing successful object
    /// definition or finite-assignment Results. They are used only to validate
    /// Runtime-resolved numeric evidence; Lean still receives the named
    /// definitions/equalities owned by those Results.
    pub(super) runtime_resolved_numeric_substitutions: HashMap<String, Obj>,
    pub(super) runtime_resolved_numeric_definition_names: Vec<String>,
    pub(super) exact_tuple_indices: HashMap<SymbolId, String>,
    pub(super) indexed_tuple_bindings: HashMap<SymbolId, IndexedTupleBinding>,
    pub(super) existential_names: HashMap<String, String>,
    pub(super) fact_names: HashMap<FactId, String>,
    pub(super) fact_propositions: HashMap<FactId, Fact>,
    /// Exact WD certificate environment owned by a published theorem FactId.
    /// Theorem instantiation specializes this context alongside the theorem's
    /// source parameters instead of borrowing the caller's unrelated WD map.
    pub(super) fact_well_definedness:
        HashMap<FactId, StmtResultWellDefinednessToLeanCompilationContext>,
    pub(super) forall_conclusion_bindings: HashMap<FactId, ForallConclusionBinding>,
    pub(super) function_bindings: HashMap<FactId, FunctionBinding>,
    pub(super) named_function_definitions: HashMap<FactId, NamedFunctionDefinitionBinding>,
    pub(super) template_set_alias_bindings: HashMap<String, TemplateSetAliasBinding>,
    pub(super) predicate_bindings: HashMap<String, PredicateBinding>,
    pub(super) registered_reflexive_predicate_theorem_bindings:
        HashMap<String, RegisteredPredicatePropertyTheoremBinding>,
    pub(super) registered_symmetric_predicate_theorem_bindings:
        HashMap<String, Vec<RegisteredPredicatePropertyTheoremBinding>>,
    pub(super) registered_transitive_predicate_theorem_bindings:
        HashMap<String, RegisteredPredicatePropertyTheoremBinding>,
    pub(super) registered_antisymmetric_predicate_theorem_bindings:
        HashMap<String, RegisteredPredicatePropertyTheoremBinding>,
}

#[derive(Clone)]
pub(super) struct CompilerTransparentObjectDefinition {
    pub(super) value: Obj,
    pub(super) defining_equality: Fact,
    pub(super) defining_equality_fact_id: FactId,
}

#[derive(Clone, Default)]
pub(super) struct StmtResultWellDefinednessToLeanCompilationContext {
    pub(super) parameter_fact_aliases: Vec<StmtResultWellDefinednessParameterFactAlias>,
    pub(super) function_applications: HashMap<
        SourceObjectOccurrenceId,
        StmtResultFunctionApplicationWellDefinednessToLeanCompilationContext,
    >,
    pub(super) anonymous_functions: HashMap<
        SourceObjectOccurrenceId,
        StmtResultAnonymousFunctionWellDefinednessToLeanCompilationContext,
    >,
    pub(super) iterations: HashMap<
        SourceObjectOccurrenceId,
        StmtResultIterationWellDefinednessToLeanCompilationContext,
    >,
    /// Explicit Result-validated rebindings used when a structured proof owns
    /// a second parser occurrence of the exact theorem goal. This is never a
    /// semantic-key fallback: the structured-proof compiler installs every
    /// source/owner pair before rendering.
    pub(super) iteration_occurrence_aliases:
        HashMap<SourceObjectOccurrenceId, SourceObjectOccurrenceId>,
}

#[derive(Clone)]
pub(super) struct StmtResultIterationWellDefinednessToLeanCompilationContext {
    pub(super) source_aggregate: Obj,
    pub(super) operation: String,
    pub(super) parameter_set: Obj,
    pub(super) return_carrier: Obj,
    pub(super) parameter_count: usize,
    pub(super) domain_count: usize,
    pub(super) has_body: bool,
    pub(super) has_body_membership: bool,
    pub(super) has_exact_integer_coverage: bool,
}

#[derive(Clone)]
pub(super) struct StmtResultWellDefinednessParameterFactAlias {
    pub(super) symbol_id: SymbolId,
    pub(super) fact_id: FactId,
    pub(super) proposition: Fact,
}

#[derive(Clone)]
pub(super) struct StmtResultFunctionApplicationWellDefinednessToLeanCompilationContext {
    pub(super) source_application: Obj,
    pub(super) function_contracts: Vec<WellDefinedFunctionContract>,
    pub(super) anonymous_function_head: Option<Obj>,
    pub(super) layers:
        Vec<StmtResultFunctionApplicationLayerWellDefinednessToLeanCompilationContext>,
}

#[derive(Clone)]
pub(super) struct StmtResultFunctionApplicationLayerWellDefinednessToLeanCompilationContext {
    pub(super) source_prefix: Obj,
    pub(super) function_contracts: Vec<WellDefinedFunctionContract>,
    pub(super) intrinsic_result_set: Option<Obj>,
    pub(super) requirements: Vec<StmtResultFunctionApplicationRequirementToLeanCompilationContext>,
}

#[derive(Clone)]
pub(super) struct StmtResultFunctionApplicationRequirementToLeanCompilationContext {
    pub(super) role: WellDefinednessRequirementRole,
    pub(super) expected_proposition: Fact,
    pub(super) verification: Rc<SuccessVerifyFactResult>,
    pub(super) proof_expression: Option<String>,
}

#[derive(Clone)]
pub(super) struct StmtResultAnonymousFunctionWellDefinednessToLeanCompilationContext {
    pub(super) source_function: Obj,
    /// The Result-owned body must be replayed only after this anonymous
    /// function's parameter aliases have entered the Lean environment.
    pub(super) body_source_object: Obj,
    pub(super) body_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub(super) parameters: Vec<StmtResultWellDefinednessBinderPremiseToLeanCompilationContext>,
    pub(super) domains: Vec<StmtResultWellDefinednessBinderPremiseToLeanCompilationContext>,
    pub(super) assumption_infers: SuccessInferResult,
    pub(super) compiled_inference_fact_proof_steps: Vec<CompiledInferenceFactProofStep>,
    pub(super) closure: StmtResultAnonymousFunctionClosureToLeanCompilationContext,
}

#[derive(Clone)]
pub(super) struct StmtResultWellDefinednessBinderPremiseToLeanCompilationContext {
    pub(super) role: WellDefinedBinderPremiseRole,
    pub(super) symbol_id: Option<SymbolId>,
    pub(super) fact_id: FactId,
    pub(super) proposition: Fact,
}

#[derive(Clone)]
pub(super) struct StmtResultAnonymousFunctionClosureToLeanCompilationContext {
    pub(super) role: WellDefinednessRequirementRole,
    pub(super) expected_proposition: Fact,
    pub(super) verification: Rc<SuccessVerifyFactResult>,
    pub(super) proof_expression: Option<String>,
}

#[derive(Clone)]
pub(super) struct IndexedTupleBinding {
    pub(super) dimension: usize,
}

#[derive(Clone)]
pub(super) struct ForallConclusionBinding {
    pub(super) theorem_name: String,
    pub(super) forall: ForallFact,
    pub(super) parameter_premises: Vec<LeanLocalFactPremise>,
    pub(super) premises: Vec<LeanLocalFactPremise>,
    pub(super) conclusion_index: usize,
    pub(super) conclusion_count: usize,
}

#[derive(Clone)]
pub(super) struct PredicateBinding {
    pub(super) lean_name: String,
    pub(super) parameter_count: usize,
    pub(super) requirement_count: usize,
    pub(super) clause_count: usize,
    pub(super) definition: Option<DefPropStmt>,
}

/// A theorem introduced by one successful `by *_prop` Result and visible only
/// in the compiler environment corresponding to that Result scope.
#[derive(Clone)]
pub(super) struct RegisteredPredicatePropertyTheoremBinding {
    pub(super) theorem_name: String,
    pub(super) forall_fact: ForallFact,
}

#[derive(Clone)]
pub(super) struct FunctionBinding {
    pub(super) symbol_id: SymbolId,
    pub(super) function: LeanTargetFunctionTypeRepresentation,
    pub(super) membership_proof_name: String,
    pub(super) direct: bool,
}

#[derive(Clone)]
pub(super) struct NamedFunctionDefinitionBinding {
    pub(super) symbol_id: SymbolId,
    pub(super) name: String,
    pub(super) function: LeanTargetFunctionTypeRepresentation,
    pub(super) source_body: Obj,
    pub(super) body: LeanTargetObjectRepresentation,
    pub(super) native_body_carrier: NativeFunctionBodyCarrier,
    pub(super) parameter_premises: Vec<LeanLocalFactPremise>,
    pub(super) domain_premises: Vec<LeanLocalFactPremise>,
    pub(super) well_definedness: StmtResultWellDefinednessToLeanCompilationContext,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NativeFunctionBodyCarrier {
    None,
    Real,
    Integer,
}

#[derive(Clone)]
pub(super) struct TemplateSetAliasBinding {
    pub(super) lean_name: String,
    pub(super) parameter_count: usize,
}
