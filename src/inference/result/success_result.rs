use super::{
    InferReason, InferRule, SuccessInferPremiseResult, SuccessInferRuleApplicationResult,
    SuccessStoreFactOutput,
};
use crate::prelude::*;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct SuccessInferResult {
    pub store_fact_outputs: Vec<SuccessStoreFactOutput>,
    /// Typed rule applications selected by inference. Store outputs retain
    /// the ordered environment effects; these nodes retain why they follow.
    pub rule_applications: Vec<SuccessInferRuleApplicationResult>,
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
        r.add_statement_with_verification(fact);
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

    pub fn remove_first_statement_with_verification_for_fact(&mut self, fact: &Fact) {
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

    pub fn add_statement_with_verification(&mut self, fact: &Fact) {
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
        self.add_store_fact_output(fact, ReleaseThmStmt::store_reason(), Vec::new());
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
