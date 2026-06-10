use crate::prelude::*;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct InferResult {
    pub effects: Vec<InferEffect>,
}

#[derive(Clone, Debug)]
pub enum InferEffect {
    AddsToContext(AddsToContextEffect),
    AbstractPropDefinition(AbstractPropDefinitionEffect),
    Warning(OutputWarning),
}

#[derive(Clone, Debug)]
pub struct AddsToContextEffect {
    pub reason: InferReason,
    pub facts: Vec<Fact>,
}

#[derive(Clone, Debug)]
pub struct AbstractPropDefinitionEffect {
    pub name: String,
    pub params: Vec<String>,
}

#[derive(Clone, Debug)]
pub enum InferReason {
    VerifiedStatement,
    ProvedClaim,
    UnsafeAssumption,
    LetBinding,
    ObjectIntroduction,
    ExistElimination,
    TheoremInstantiation,
    ByDefinition(ByDefinitionReason),
    BuiltinInference(BuiltinInferenceReason),
    InferRule(InferRuleReason),
    Evaluation,
    ParameterDeclaration,
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

#[derive(Clone, Debug)]
pub struct OutputWarning {
    pub message: String,
}

impl InferResult {
    pub fn new() -> Self {
        InferResult { effects: vec![] }
    }

    pub fn from_fact(fact: &Fact) -> Self {
        let mut r = Self::new();
        r.add_verified_statement(fact);
        r
    }

    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }

    pub fn effects(&self) -> &[InferEffect] {
        &self.effects
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
        for effect in self.effects.iter() {
            if let InferEffect::AddsToContext(adds) = effect {
                facts.extend(adds.facts.iter().cloned());
            }
        }
        facts
    }

    pub fn contains_added_fact(&self, fact: &Fact) -> bool {
        let target = fact.to_string();
        self.effects.iter().any(|effect| {
            let InferEffect::AddsToContext(adds) = effect else {
                return false;
            };
            adds.facts
                .iter()
                .any(|added_fact| added_fact.to_string() == target)
        })
    }

    pub fn remove_first_verified_statement_for_fact(&mut self, fact: &Fact) {
        let target = fact.to_string();
        let mut removed = false;
        self.effects.retain(|effect| {
            if removed {
                return true;
            }
            let InferEffect::AddsToContext(adds) = effect else {
                return true;
            };
            let is_target = matches!(adds.reason, InferReason::VerifiedStatement)
                && adds.facts.len() == 1
                && adds.facts[0].to_string() == target;
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

    pub fn new_with_msg(&mut self, msg: String) {
        self.add_warning(msg);
    }

    pub fn new_fact(&mut self, fact: &Fact) {
        self.add_infer_rule(None, "legacy inference", fact);
    }

    pub fn push_atomic_fact(&mut self, atomic_fact: &AtomicFact) {
        let fact: Fact = atomic_fact.clone().into();
        self.new_fact(&fact);
    }

    pub fn new_infer_result_inside(&mut self, other_infer_result: InferResult) {
        self.effects.extend(other_infer_result.effects);
    }

    pub fn add_verified_statement(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::VerifiedStatement, fact);
    }

    pub fn add_proved_claim(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::ProvedClaim, fact);
    }

    pub fn add_unsafe_assumption(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::UnsafeAssumption, fact);
    }

    pub fn add_let_binding(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::LetBinding, fact);
    }

    pub fn add_object_introduction(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::ObjectIntroduction, fact);
    }

    pub fn add_exist_elimination(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::ExistElimination, fact);
    }

    pub fn add_theorem_instantiation(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::TheoremInstantiation, fact);
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
        self.add_fact_with_reason(InferReason::Evaluation, fact);
    }

    pub fn add_parameter_declaration(&mut self, fact: &Fact) {
        self.add_fact_with_reason(InferReason::ParameterDeclaration, fact);
    }

    pub fn add_warning(&mut self, message: String) {
        self.effects
            .push(InferEffect::Warning(OutputWarning::new(message)));
    }

    pub fn add_abstract_prop_definition(&mut self, name: &str, params: &[String]) {
        self.effects.push(InferEffect::AbstractPropDefinition(
            AbstractPropDefinitionEffect::new(name.to_string(), params.to_vec()),
        ));
    }

    pub fn add_fact_with_reason(&mut self, reason: InferReason, fact: &Fact) {
        self.push_fact_with_reason(reason, fact.clone());
    }

    pub fn relabel_primary_fact(&mut self, fact: &Fact, reason: InferReason) {
        for effect in self.effects.iter_mut() {
            let InferEffect::AddsToContext(adds) = effect else {
                continue;
            };
            if adds.facts.len() == 1 && adds.facts[0].to_string() == fact.to_string() {
                adds.reason = reason;
                return;
            }
        }
    }

    pub fn relabel_all_added_facts(&mut self, reason: InferReason) {
        for effect in self.effects.iter_mut() {
            if let InferEffect::AddsToContext(adds) = effect {
                adds.reason = reason.clone();
            }
        }
    }

    fn push_fact_with_reason(&mut self, reason: InferReason, fact: Fact) {
        self.effects
            .push(InferEffect::AddsToContext(AddsToContextEffect::new(
                reason,
                vec![fact],
            )));
    }

    fn infer_lines(&self) -> Vec<String> {
        let mut lines = Vec::new();
        for effect in self.effects.iter() {
            match effect {
                InferEffect::AddsToContext(adds) => {
                    lines.extend(adds.facts.iter().map(|fact| fact.to_string()));
                }
                InferEffect::AbstractPropDefinition(definition) => {
                    lines.push(format!(
                        "defined abstract prop {}({}) with unspecified definition",
                        definition.name,
                        definition.params.join(", ")
                    ));
                }
                InferEffect::Warning(warning) => lines.push(warning.message.clone()),
            }
        }
        lines
    }
}

impl AbstractPropDefinitionEffect {
    pub fn new(name: String, params: Vec<String>) -> Self {
        AbstractPropDefinitionEffect { name, params }
    }
}

impl AddsToContextEffect {
    pub fn new(reason: InferReason, facts: Vec<Fact>) -> Self {
        AddsToContextEffect { reason, facts }
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

impl OutputWarning {
    pub fn new(message: String) -> Self {
        OutputWarning { message }
    }
}
