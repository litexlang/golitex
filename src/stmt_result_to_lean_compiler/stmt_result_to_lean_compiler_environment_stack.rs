use crate::litex_to_lean_ir::{
    LitexToLeanFactIr, LitexToLeanFunctionTypeIr, LitexToLeanLocalPremiseIr, LitexToLeanObjectIr,
    LitexToLeanWellDefinednessCertificateIr,
};
use crate::prelude::*;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

/// Lexical Lean-generation environments owned by `StmtResultToLeanCompiler`.
///
/// A child frame inherits every binding visible in its parent. Bindings added
/// to the child disappear when the child Result scope is left.
#[derive(Clone)]
pub(super) struct StmtResultToLeanCompilerEnvironmentStack {
    pub(super) environments: Vec<StmtResultToLeanCompilerEnvironment>,
}

impl Default for StmtResultToLeanCompilerEnvironmentStack {
    fn default() -> Self {
        Self {
            environments: vec![StmtResultToLeanCompilerEnvironment::default()],
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
    }

    pub(super) fn pop_local_environment(&mut self) {
        assert!(
            self.environments.len() > 1,
            "compiler cannot pop its top-level environment"
        );
        self.environments.pop();
    }
}

/// Names and target-representation choices visible in one Lean lexical scope.
/// This is compiler state, not a second statement/proof IR.
#[derive(Clone, Default)]
pub(super) struct StmtResultToLeanCompilerEnvironment {
    pub(super) symbol_names: HashMap<SymbolId, String>,
    /// Canonical complex observations for numeric symbols whose Lean carrier
    /// is locally heterogeneous (for example a dependent function binder).
    pub(super) numeric_representations: HashMap<SymbolId, String>,
    pub(super) numeric_representation_memberships: HashMap<SymbolId, String>,
    pub(super) numeric_real_values: HashMap<SymbolId, String>,
    pub(super) exact_tuple_indices: HashMap<SymbolId, String>,
    pub(super) indexed_tuple_bindings: HashMap<SymbolId, IndexedTupleBinding>,
    pub(super) existential_names: HashMap<String, String>,
    pub(super) fact_names: HashMap<FactId, String>,
    pub(super) fact_propositions: HashMap<FactId, Fact>,
    pub(super) forall_conclusion_bindings: HashMap<FactId, ForallConclusionBinding>,
    pub(super) function_bindings: HashMap<FactId, FunctionBinding>,
    pub(super) named_function_definitions: HashMap<FactId, NamedFunctionDefinitionBinding>,
    pub(super) predicate_bindings: HashMap<String, PredicateBinding>,
    pub(super) well_definedness: Option<LitexToLeanWellDefinednessCertificateIr>,
}

#[derive(Clone)]
pub(super) struct IndexedTupleBinding {
    pub(super) dimension: usize,
}

#[derive(Clone)]
pub(super) struct ForallConclusionBinding {
    pub(super) theorem_name: String,
    pub(super) forall: ForallFact,
    pub(super) parameter_premises: Vec<LitexToLeanLocalPremiseIr>,
    pub(super) premises: Vec<LitexToLeanLocalPremiseIr>,
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

#[derive(Clone)]
pub(super) struct FunctionBinding {
    pub(super) symbol_id: SymbolId,
    pub(super) function: LitexToLeanFunctionTypeIr,
    pub(super) membership_proof_name: String,
    pub(super) direct: bool,
}

#[derive(Clone)]
pub(super) struct NamedFunctionDefinitionBinding {
    pub(super) symbol_id: SymbolId,
    pub(super) name: String,
    pub(super) function: LitexToLeanFunctionTypeIr,
    pub(super) source_body: Obj,
    pub(super) body: LitexToLeanObjectIr,
    pub(super) uses_native_real_body: bool,
    pub(super) parameter_premises: Vec<LitexToLeanLocalPremiseIr>,
    pub(super) domain_premises: Vec<LitexToLeanLocalPremiseIr>,
    /// Only non-native return carriers need the old representative-selection
    /// recipe. Native real functions are constructed directly from the
    /// recursive return-check Result and deliberately retain no duplicate
    /// mirrored statement/fact compiler representation here.
    pub(super) compatibility_return_selection:
        Option<CompatibilityNamedFunctionReturnSelectionBinding>,
    pub(super) well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone)]
pub(super) struct CompatibilityNamedFunctionReturnSelectionBinding {
    pub(super) inferred_premises: Vec<LitexToLeanFactIr>,
    pub(super) return_check: LitexToLeanFactIr,
}
