use crate::prelude::*;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct InferResult {
    pub store_fact_outputs: Vec<StoreFactOutput>,
}

#[derive(Clone, Debug)]
pub struct StoreFactOutput {
    pub itself_and_why_itself_is_stored: (Fact, String),
    pub inferred_facts: Vec<Fact>,
}

#[derive(Clone, Debug)]
pub enum InferReason {
    VerifiedStatement,
    ProvedClaim,
    UnsafeAssumption,
    LetBinding,
    InferredFact,
    StoredFact,
    StoredFactWithoutForallCoverageCheck,
    StoredForallFact,
    ObjectDefinition,
    FunctionDefinition,
    ExistElimination,
    TheoremInstantiation,
    ByDefinition(ByDefinitionReason),
    BuiltinInference(BuiltinInferenceReason),
    InferRule(InferRuleReason),
    Evaluation,
    ParameterDefinition,
    Other(String),
}

#[derive(Clone, Debug)]
pub struct ByDefinitionReason {
    pub source_fact: Option<Box<Fact>>,
    pub definition: Option<String>,
}

#[derive(Clone, Debug)]
pub struct BuiltinInferenceReason {
    pub source_fact: Option<Box<Fact>>,
    pub rule: String,
}

#[derive(Clone, Debug)]
pub struct InferRuleReason {
    pub source_fact: Option<Box<Fact>>,
    pub rule: String,
}

impl InferResult {
    pub fn new() -> Self {
        InferResult {
            store_fact_outputs: vec![],
        }
    }

    pub fn from_fact(fact: &Fact) -> Self {
        let mut r = Self::new();
        r.add_verified_statement(fact);
        r
    }

    pub fn is_empty(&self) -> bool {
        self.store_fact_outputs.is_empty()
    }

    pub fn store_fact_outputs(&self) -> &[StoreFactOutput] {
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

    pub fn new_infer_result_inside(&mut self, other_infer_result: InferResult) {
        self.store_fact_outputs
            .extend(other_infer_result.store_fact_outputs);
    }

    pub fn add_verified_statement(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, Fact::store_reason(), Vec::new());
    }

    pub fn add_proved_claim(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ClaimStmt::store_reason(), Vec::new());
    }

    pub fn add_unsafe_assumption(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ProofDebtStmt::store_reason(), Vec::new());
    }

    pub fn add_let_binding(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, DefLetStmt::store_reason(), Vec::new());
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
        self.add_store_fact_output(fact, HaveByExistStmt::store_reason(), Vec::new());
    }

    pub fn add_theorem_instantiation(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ByThmStmt::store_reason(), Vec::new());
    }

    pub fn add_fact_by_definition(
        &mut self,
        source_fact: Option<Fact>,
        definition: Option<String>,
        fact: &Fact,
    ) {
        self.add_fact_with_reason(
            InferReason::ByDefinition(ByDefinitionReason::new(source_fact, definition)),
            fact,
        );
    }

    pub fn add_builtin_inference(
        &mut self,
        rule: impl Into<String>,
        source_fact: Option<Fact>,
        fact: &Fact,
    ) {
        self.add_fact_with_reason(
            InferReason::BuiltinInference(BuiltinInferenceReason::new(source_fact, rule.into())),
            fact,
        );
    }

    pub fn add_infer_rule(
        &mut self,
        source_fact: Option<Fact>,
        rule: impl Into<String>,
        fact: &Fact,
    ) {
        self.add_fact_with_reason(
            InferReason::InferRule(InferRuleReason::new(source_fact, rule.into())),
            fact,
        );
    }

    pub fn add_evaluation(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, EvalStmt::store_reason(), Vec::new());
    }

    pub fn add_parameter_definition(&mut self, fact: &Fact) {
        self.add_store_fact_output(fact, ParamDefWithType::store_reason(), Vec::new());
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
        self.store_fact_outputs.push(StoreFactOutput::new(
            fact.clone(),
            reason.into(),
            inferred_facts,
        ));
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

impl StoreFactOutput {
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
        StoreFactOutput {
            itself_and_why_itself_is_stored: (fact, reason),
            inferred_facts,
        }
    }
}

impl InferReason {
    pub fn store_reason(&self) -> String {
        match self {
            InferReason::VerifiedStatement => Fact::store_reason().to_string(),
            InferReason::ProvedClaim => ClaimStmt::store_reason().to_string(),
            InferReason::UnsafeAssumption => ProofDebtStmt::store_reason().to_string(),
            InferReason::LetBinding => DefLetStmt::store_reason().to_string(),
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
            InferReason::ExistElimination => HaveByExistStmt::store_reason().to_string(),
            InferReason::TheoremInstantiation => ByThmStmt::store_reason().to_string(),
            InferReason::ByDefinition(_) => "inferred by definition".to_string(),
            InferReason::BuiltinInference(reason) => {
                format!("inferred by builtin rule `{}`", reason.rule)
            }
            InferReason::InferRule(reason) => format!("inferred by infer rule `{}`", reason.rule),
            InferReason::Evaluation => EvalStmt::store_reason().to_string(),
            InferReason::ParameterDefinition => ParamDefWithType::store_reason().to_string(),
            InferReason::Other(s) => s.clone(),
        }
    }
}

impl ByDefinitionReason {
    pub fn new(source_fact: Option<Fact>, definition: Option<String>) -> Self {
        ByDefinitionReason {
            source_fact: source_fact.map(Box::new),
            definition,
        }
    }
}

impl BuiltinInferenceReason {
    pub fn new(source_fact: Option<Fact>, rule: String) -> Self {
        BuiltinInferenceReason {
            source_fact: source_fact.map(Box::new),
            rule,
        }
    }
}

impl InferRuleReason {
    pub fn new(source_fact: Option<Fact>, rule: String) -> Self {
        InferRuleReason {
            source_fact: source_fact.map(Box::new),
            rule,
        }
    }
}
