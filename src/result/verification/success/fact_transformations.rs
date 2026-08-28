//! Equality transport and fact transformation evidence.

use crate::prelude::*;
use std::fmt;

#[derive(Clone, Debug)]
pub struct EqualityTransportEvidence {
    pub steps: Vec<EqualityTransportStep>,
}

impl EqualityTransportEvidence {
    pub fn new(steps: Vec<EqualityTransportStep>) -> Self {
        Self { steps }
    }
}

#[derive(Clone)]
pub struct EqualityTransportStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
    pub equality_fact_id: FactId,
}

impl EqualityTransportStep {
    pub fn new(from: Obj, to: Obj, equality: EqualFact, equality_fact_id: FactId) -> Self {
        Self {
            from,
            to,
            equality,
            equality_fact_id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FactTransformationEvidence {
    /// Proposition proved before the first transformation step.
    pub source: Fact,
    /// Ordered in proof-construction direction: cited source toward the goal.
    pub steps: Vec<FactTransformationStep>,
}

impl FactTransformationEvidence {
    pub fn new(source: Fact, steps: Vec<FactTransformationStep>) -> Self {
        Self { source, steps }
    }
}

#[derive(Clone, Debug)]
pub struct FactTransformationStep {
    /// Proposition available after applying this step.
    pub result: Fact,
    pub rule: FactTransformationRule,
}

impl FactTransformationStep {
    pub fn new(result: Fact, rule: FactTransformationRule) -> Self {
        Self { result, rule }
    }
}

#[derive(Clone, Debug)]
pub enum FactTransformationRule {
    EqualityRewrite(EqualityTransportEvidence),
    RationalNormalization,
    /// Capture-avoiding beta conversion of fully applied anonymous-function
    /// literals, possibly below ordinary object constructors.
    AnonymousFunctionBetaNormalization,
    TransparentDefinitionReduction(TransparentDefinitionReductionEvidence),
}

impl fmt::Debug for EqualityTransportStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("EqualityTransportStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .field("equality_fact_id", &self.equality_fact_id)
            .finish()
    }
}
