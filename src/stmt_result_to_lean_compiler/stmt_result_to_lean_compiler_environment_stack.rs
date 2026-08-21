use crate::litex_to_lean_ir::{
    LitexToLeanFunctionTypeIr, LitexToLeanLocalPremiseIr, LitexToLeanObjectIr,
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

    /// Match Litex `clear` at the target-generation boundary. The current
    /// lexical layer forgets every source identity that execution forgot;
    /// parent layers, when one exists, remain owned by their enclosing Result.
    pub(super) fn clear_current_environment(&mut self) {
        let current = self
            .environments
            .last_mut()
            .expect("compiler environment stack must retain its top-level environment");
        *current = StmtResultToLeanCompilerEnvironment::default();
    }

    pub(super) fn is_top_level(&self) -> bool {
        self.environments.len() == 1
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
    pub(super) exact_tuple_indices: HashMap<SymbolId, String>,
    pub(super) indexed_tuple_bindings: HashMap<SymbolId, IndexedTupleBinding>,
    pub(super) existential_names: HashMap<String, String>,
    pub(super) fact_names: HashMap<FactId, String>,
    pub(super) fact_propositions: HashMap<FactId, Fact>,
    pub(super) forall_conclusion_bindings: HashMap<FactId, ForallConclusionBinding>,
    pub(super) function_bindings: HashMap<FactId, FunctionBinding>,
    pub(super) named_function_definitions: HashMap<FactId, NamedFunctionDefinitionBinding>,
    pub(super) predicate_bindings: HashMap<String, PredicateBinding>,
    pub(super) registered_reflexive_predicate_theorem_bindings:
        HashMap<String, RegisteredPredicatePropertyTheoremBinding>,
    pub(super) registered_symmetric_predicate_theorem_bindings:
        HashMap<String, Vec<RegisteredPredicatePropertyTheoremBinding>>,
    pub(super) registered_transitive_predicate_theorem_bindings:
        HashMap<String, RegisteredPredicatePropertyTheoremBinding>,
    pub(super) registered_antisymmetric_predicate_theorem_bindings:
        HashMap<String, RegisteredPredicatePropertyTheoremBinding>,
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
    pub(super) well_definedness: LitexToLeanWellDefinednessCertificateIr,
}
