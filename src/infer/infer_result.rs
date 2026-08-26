use crate::prelude::*;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct SuccessInferResult {
    pub store_fact_outputs: Vec<SuccessStoreFactOutput>,
    /// Typed rule applications selected by inference. Store outputs retain
    /// the ordered environment effects; these nodes retain why they follow.
    pub rule_applications: Vec<SuccessInferRuleApplicationResult>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InferRule {
    NaturalMembershipImpliesNonnegative,
    PositiveStandardSetMembershipImpliesPositive(
        PositiveStandardSetMembershipImpliesPositiveInferRule,
    ),
    NegativeStandardSetMembershipImpliesNegative(
        NegativeStandardSetMembershipImpliesNegativeInferRule,
    ),
    NonzeroStandardSetMembershipImpliesNonzero(NonzeroStandardSetMembershipImpliesNonzeroInferRule),
    SetBuilderBaseMembershipProjection,
    SetBuilderPredicateProjection {
        clause_index: usize,
    },
    DefinedPredicateParameterRequirementProjection(
        DefinedPredicateParameterRequirementProjectionInferRule,
    ),
    DefinedPredicateDefinitionClauseProjection(DefinedPredicateDefinitionClauseProjectionInferRule),
    EqualityChainClosure(EqualityChainClosureInferRule),
    ClosedPositivePowerEqualityImpliesEqualSideMembership(
        ClosedPositivePowerEqualityImpliesEqualSideMembershipInferRule,
    ),
    PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(
        PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembershipInferRule,
    ),
    RegisteredTransitivePredicateChainClosure(RegisteredTransitivePredicateChainClosureInferRule),
    TupleEqualityWithKnownTupleImpliesTupleShape(
        TupleEqualityWithKnownTupleImpliesTupleShapeInferRule,
    ),
    ListSetMembershipImpliesEqualityAlternatives(
        ListSetMembershipImpliesEqualityAlternativesInferRule,
    ),
    NumericOrderBoundImpliesZeroSign,
    MultiplicationByNegativeOneReversesOrderAgainstZero,
    StrictOrderComparedToZeroImpliesWeakOrder,
    MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(
        MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule,
    ),
    SubsetImpliesElementwiseMembershipForall(SubsetImpliesElementwiseMembershipForallInferRule),
    SupersetImpliesElementwiseMembershipForall(SupersetImpliesElementwiseMembershipForallInferRule),
    ConjunctionImpliesComponent(ConjunctionImpliesComponentInferRule),
}

/// A stored conjunction exposes one exact ordered component. The component
/// Result owns its own FactId; consumers project it from the conjunction
/// premise instead of looking up an equal proposition by text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConjunctionImpliesComponentInferRule {
    pub component_index: usize,
    pub component_count: usize,
}

/// `A $subset B` introduces the reusable local theorem
/// `forall x A: x $in B`. The generated binder identity is retained because
/// it occurs recursively in the conclusion and must not be reconstructed by
/// a compiler from the binder's display name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubsetImpliesElementwiseMembershipForallInferRule {
    pub binder_symbol_id: SymbolId,
}

/// `A $superset B` introduces the reusable local theorem
/// `forall x B: x $in A` with the same exact-binder identity contract as the
/// subset direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupersetImpliesElementwiseMembershipForallInferRule {
    pub binder_symbol_id: SymbolId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownSetEqualityOrientation {
    SourceSetOnLeft,
    SourceSetOnRight,
}

/// The premise list is ordered as source membership followed by the exact
/// previously stored equality between the source and target sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule {
    pub equality_orientation: KnownSetEqualityOrientation,
}

/// `x $in {a_1, ..., a_n}` exposes exactly the ordered alternatives
/// `x = a_1 or ... or x = a_n`. For a singleton the conclusion is the one
/// equality itself. The source list remains in the premise Fact; this field
/// freezes the arity so consumers reject a truncated or extended conclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListSetMembershipImpliesEqualityAlternativesInferRule {
    pub element_count: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownTupleEqualitySide {
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleEqualityWithKnownTupleImpliesTupleShapeInferRule {
    pub known_side: KnownTupleEqualitySide,
    pub tuple_length: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositiveStandardSetMembershipImpliesPositiveInferRule {
    pub source_set: StandardSet,
}

/// A checked equality transports the closed positive-real membership of one
/// literal polynomial power to its opposite endpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClosedPositivePowerEqualityImpliesEqualSideMembershipInferRule {
    pub power_is_left_endpoint: bool,
}

/// A checked equality transports `R+` membership from a positive integer base
/// raised to a closed natural exponent to the opposite equality endpoint. The
/// application additionally cites the exact base-positivity and `Z` premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembershipInferRule {
    pub power_is_left_endpoint: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NegativeStandardSetMembershipImpliesNegativeInferRule {
    pub source_set: StandardSet,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonzeroStandardSetMembershipImpliesNonzeroInferRule {
    pub source_set: StandardSet,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinedPredicateParameterRequirementProjectionInferRule {
    pub predicate_name: String,
    pub parameter_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinedPredicateDefinitionClauseProjectionInferRule {
    pub predicate_name: String,
    pub clause_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisteredTransitivePredicateChainClosureInferRule {
    pub predicate_name: String,
    pub start_object_index: usize,
    pub end_object_index: usize,
}

/// One non-adjacent equality exposed by an exact source relation chain.
///
/// The object interval is half-open over the chain edges and closed over its
/// endpoint objects: `[start_object_index, end_object_index]` consumes exactly
/// the adjacent equalities at edge indexes `start..end`. Consumers must check
/// those premises against the source chain before folding transitivity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityChainClosureInferRule {
    pub start_object_index: usize,
    pub end_object_index: usize,
}

#[derive(Clone, Debug)]
pub struct SuccessInferPremiseResult {
    pub fact: Fact,
    pub fact_id: Option<FactId>,
}

#[derive(Clone, Debug)]
pub struct SuccessInferRuleApplicationResult {
    pub rule: InferRule,
    pub premises: Vec<SuccessInferPremiseResult>,
    pub conclusions: Vec<SuccessStoreFactResult>,
}

#[derive(Clone, Debug)]
pub struct SuccessStoreFactOutput {
    /// Stable identity when this output corresponds to an environment-stored
    /// fact. It remains available after a temporary proof environment is gone.
    pub fact_id: Option<FactId>,
    pub itself_and_why_itself_is_stored: (Fact, String),
    pub inferred_facts: Vec<Fact>,
    /// Stable identities assigned to `inferred_facts` in the same order.
    /// Temporary proof scopes populate these before their environment closes.
    pub inferred_fact_ids: Vec<Option<FactId>>,
}

#[derive(Clone, Debug)]
pub enum InferReason {
    VerifiedStatement,
    ProvedClaim,
    UnsafeAssumption,
    TrustHave,
    InferredFact,
    StoredFact,
    StoredFactWithoutForallCoverageCheck,
    StoredForallFact,
    ObjectDefinition,
    FunctionDefinition,
    ExistElimination,
    TheoremInstantiation,
    ByDefinition,
    BuiltinInference(String),
    InferRule(String),
    Evaluation,
    ParameterDefinition,
    Other(String),
}

impl SuccessInferResult {
    pub fn new() -> Self {
        SuccessInferResult {
            store_fact_outputs: vec![],
            rule_applications: vec![],
        }
    }

    pub fn from_fact(fact: &Fact) -> Self {
        let mut r = Self::new();
        r.add_verified_statement(fact);
        r
    }

    pub fn is_empty(&self) -> bool {
        self.store_fact_outputs.is_empty() && self.rule_applications.is_empty()
    }

    pub fn store_fact_outputs(&self) -> &[SuccessStoreFactOutput] {
        &self.store_fact_outputs
    }

    pub fn infer_lines_unique_in_order(&self) -> Vec<String> {
        let mut seen = HashSet::new();
        self.infer_lines()
            .into_iter()
            .filter(|s| seen.insert(s.clone()))
            .collect()
    }

    pub fn inferred_facts(&self) -> Vec<Fact> {
        let mut facts = Vec::new();
        let mut seen = HashSet::new();
        for output in self.store_fact_outputs.iter() {
            let fact = output.itself_and_why_itself_is_stored.0.clone();
            if seen.insert(fact.to_string()) {
                facts.push(fact);
            }
            for inferred_fact in output.inferred_facts.iter() {
                if seen.insert(inferred_fact.to_string()) {
                    facts.push(inferred_fact.clone());
                }
            }
        }
        facts
    }

    pub fn contains_added_fact(&self, fact: &Fact) -> bool {
        let target = fact.to_string();
        self.store_fact_outputs.iter().any(|output| {
            output.itself_and_why_itself_is_stored.0.to_string() == target
                || output
                    .inferred_facts
                    .iter()
                    .any(|added_fact| added_fact.to_string() == target)
        })
    }

    pub fn remove_first_verified_statement_for_fact(&mut self, fact: &Fact) {
        let target = fact.to_string();
        let mut removed = false;
        self.store_fact_outputs.retain(|output| {
            if removed {
                return true;
            }
            let is_target = output.itself_and_why_itself_is_stored.1 == Fact::store_reason()
                && output.itself_and_why_itself_is_stored.0.to_string() == target;
            if is_target {
                removed = true;
                false
            } else {
                true
            }
        });
    }

    pub fn join_infer_lines(&self, sep: &str) -> String {
        self.infer_lines_unique_in_order().join(sep)
    }

    pub fn new_with_msg(&mut self, _msg: String) {}

    pub fn new_fact(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::InferredFact, fact);
    }

    pub fn push_atomic_fact(&mut self, atomic_fact: &AtomicFact) {
        let fact: Fact = atomic_fact.clone().into();
        self.new_fact(&fact);
    }

    pub fn new_infer_result_inside(&mut self, other_infer_result: SuccessInferResult) {
        self.store_fact_outputs
            .extend(other_infer_result.store_fact_outputs);
        self.rule_applications
            .extend(other_infer_result.rule_applications);
    }

    pub fn add_rule_application(
        &mut self,
        rule: InferRule,
        premise: Fact,
        conclusions: Vec<SuccessStoreFactResult>,
    ) {
        self.add_rule_application_with_premises(rule, vec![premise], conclusions);
    }

    pub fn add_rule_application_with_premises(
        &mut self,
        rule: InferRule,
        premises: Vec<Fact>,
        conclusions: Vec<SuccessStoreFactResult>,
    ) {
        self.rule_applications
            .push(SuccessInferRuleApplicationResult {
                rule,
                premises: premises
                    .into_iter()
                    .map(|fact| SuccessInferPremiseResult {
                        fact,
                        fact_id: None,
                    })
                    .collect(),
                conclusions,
            });
    }

    /// `Combine`: retain each conclusion's recursive infer Result under the
    /// typed application while projecting only its ordered store effects into
    /// this level's compatibility summary. Nested rule applications are not
    /// flattened into the parent; consumers reach them through `conclusions`.
    pub fn add_rule_application_preserving_conclusion_result_structure(
        &mut self,
        rule: InferRule,
        premises: Vec<Fact>,
        conclusions: Vec<SuccessStoreFactResult>,
    ) {
        for conclusion in &conclusions {
            self.store_fact_outputs
                .extend(conclusion.infers.store_fact_outputs.iter().cloned());
        }
        self.add_rule_application_with_premises(rule, premises, conclusions);
    }

    pub fn add_verified_statement(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, Fact::store_reason(), Vec::new());
    }

    pub fn add_proved_claim(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ClaimStmt::store_reason(), Vec::new());
    }

    pub fn add_unsafe_assumption(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, TrustStmt::store_reason(), Vec::new());
    }

    pub fn add_trust_have_binding(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, TrustHaveStmt::store_reason(), Vec::new());
    }

    pub fn add_object_definition(&mut self, fact: &Fact) {
        self.add_store_fact_output(
            fact,
            HaveObjInNonemptySetOrParamTypeStmt::store_reason(),
            Vec::new(),
        );
    }

    pub fn add_function_definition(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, HaveFnEqualStmt::store_reason(), Vec::new());
    }

    pub fn add_function_case_definition(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, HaveFnEqualCaseByCaseStmt::store_reason(), Vec::new());
    }

    pub fn add_exist_elimination(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ObtainObjFromExistFact::store_reason(), Vec::new());
    }

    pub fn add_theorem_instantiation(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ByThmStmt::store_reason(), Vec::new());
    }

    pub fn add_fact_by_definition(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::ByDefinition, fact);
    }

    pub fn add_builtin_inference(&mut self, rule: impl Into<String>, fact: &Fact) {
        self.add_fact_with_reason(InferReason::BuiltinInference(rule.into()), fact);
    }

    pub fn add_infer_rule(&mut self, rule: impl Into<String>, fact: &Fact) {
        self.add_fact_with_reason(InferReason::InferRule(rule.into()), fact);
    }

    pub fn add_evaluation(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, EvalStmt::store_reason(), Vec::new());
    }

    pub fn add_parameter_definition(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, TypedParameterList::store_reason(), Vec::new());
    }

    pub fn add_fact_with_reason(&mut self, reason: InferReason, fact: &Fact) {
        let reason_text = reason.store_reason();
        self.add_store_fact_output(fact, reason_text, Vec::new());
    }

    pub fn relabel_primary_fact(&mut self, fact: &Fact, reason: InferReason) {
        let reason_text = reason.store_reason();
        for output in self.store_fact_outputs.iter_mut() {
            if output.itself_and_why_itself_is_stored.0.to_string() == fact.to_string() {
                output.itself_and_why_itself_is_stored.1 = reason_text;
                return;
            }
        }
    }

    pub fn relabel_all_added_facts(&mut self, reason: InferReason) {
        let reason_text = reason.store_reason();
        self.relabel_all_added_facts_with_store_reason(reason_text);
    }

    pub fn relabel_all_added_facts_with_store_reason(&mut self, reason: impl Into<String>) {
        let reason_text = reason.into();
        for output in self.store_fact_outputs.iter_mut() {
            output.itself_and_why_itself_is_stored.1 = reason_text.clone();
        }
    }

    pub fn add_store_fact_output(
        &mut self,
        fact: &Fact,
        reason: impl Into<String>,
        inferred_facts: Vec<Fact>,
    ) {
        self.store_fact_outputs.push(SuccessStoreFactOutput::new(
            fact.clone(),
            reason.into(),
            inferred_facts,
        ));
    }

    /// Preserve the selected typed rule applications while retaining the
    /// existing flattened environment-effect summary for compatibility.
    pub fn add_store_fact_output_from_nested(
        &mut self,
        fact: &Fact,
        reason: impl Into<String>,
        nested: &mut SuccessInferResult,
    ) {
        let inferred_facts = nested.inferred_facts();
        self.add_store_fact_output(fact, reason, inferred_facts);
        self.rule_applications.append(&mut nested.rule_applications);
    }

    fn infer_lines(&self) -> Vec<String> {
        let mut lines = Vec::new();
        for output in self.store_fact_outputs.iter() {
            lines.push(format!(
                "store {} ({})",
                output.itself_and_why_itself_is_stored.0, output.itself_and_why_itself_is_stored.1
            ));
            for fact in output.inferred_facts.iter() {
                lines.push(format!("infer {}", fact));
            }
        }
        lines
    }
}

impl SuccessStoreFactOutput {
    pub fn new(fact: Fact, reason: String, inferred_facts: Vec<Fact>) -> Self {
        let fact_text = fact.to_string();
        let mut seen = HashSet::new();
        let inferred_facts = inferred_facts
            .into_iter()
            .filter(|inferred_fact| {
                let inferred_text = inferred_fact.to_string();
                inferred_text != fact_text && seen.insert(inferred_text)
            })
            .collect::<Vec<_>>();
        let inferred_fact_ids = vec![None; inferred_facts.len()];
        SuccessStoreFactOutput {
            fact_id: None,
            itself_and_why_itself_is_stored: (fact, reason),
            inferred_facts,
            inferred_fact_ids,
        }
    }
}

impl InferReason {
    pub fn store_reason(&self) -> String {
        match self {
            InferReason::VerifiedStatement => Fact::store_reason().to_string(),
            InferReason::ProvedClaim => ClaimStmt::store_reason().to_string(),
            InferReason::UnsafeAssumption => TrustStmt::store_reason().to_string(),
            InferReason::TrustHave => TrustHaveStmt::store_reason().to_string(),
            InferReason::InferredFact => "inferred fact".to_string(),
            InferReason::StoredFact => "stored fact".to_string(),
            InferReason::StoredFactWithoutForallCoverageCheck => {
                "stored fact without forall coverage check".to_string()
            }
            InferReason::StoredForallFact => "stored forall fact".to_string(),
            InferReason::ObjectDefinition => {
                HaveObjInNonemptySetOrParamTypeStmt::store_reason().to_string()
            }
            InferReason::FunctionDefinition => HaveFnEqualStmt::store_reason().to_string(),
            InferReason::ExistElimination => ObtainObjFromExistFact::store_reason().to_string(),
            InferReason::TheoremInstantiation => ByThmStmt::store_reason().to_string(),
            InferReason::ByDefinition => "inferred by definition".to_string(),
            InferReason::BuiltinInference(rule) => {
                format!("inferred by builtin rule `{}`", rule)
            }
            InferReason::InferRule(rule) => format!("inferred by infer rule `{}`", rule),
            InferReason::Evaluation => EvalStmt::store_reason().to_string(),
            InferReason::ParameterDefinition => TypedParameterList::store_reason().to_string(),
            InferReason::Other(s) => s.clone(),
        }
    }
}
