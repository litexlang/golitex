//! Checked definition reduction and structural congruence evidence.

use crate::prelude::*;
use std::fmt;

/// One exact named-function unfolding used below a reviewed structural
/// equality context. The defining equality is retained by `FactId`; the
/// application and its substituted body make the reduction independently
/// replayable after the verifier Runtime has been dropped.
#[derive(Clone)]
pub struct NestedCheckedFunctionDefinitionReductionEvidence {
    pub definition_object: Obj,
    pub defining_equality: Fact,
    pub defining_equality_fact_id: FactId,
    pub application: Obj,
    pub reduced: Obj,
}

/// Equality obtained only by applying the retained named-function reductions
/// below matching object constructors. No calculation or ambient equality
/// search is hidden in this certificate.
#[derive(Clone)]
pub struct StructuralDefinitionCongruenceBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub reductions: Vec<NestedCheckedFunctionDefinitionReductionEvidence>,
}

/// Equality obtained by applying reviewed addition congruence to exact child
/// Results. Identical leaves are reflexive; every non-identical leaf is
/// retained as one ordered child Result instead of being rediscovered from a
/// verifier environment after compilation.
#[derive(Clone)]
pub struct StructuralKnownEqualityCongruenceBuiltinRuleEvidence {
    pub expected_target: Fact,
}

impl fmt::Debug for NestedCheckedFunctionDefinitionReductionEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("NestedCheckedFunctionDefinitionReductionEvidence")
            .field("definition_object", &self.definition_object.to_string())
            .field("defining_equality", &self.defining_equality.to_string())
            .field("defining_equality_fact_id", &self.defining_equality_fact_id)
            .field("application", &self.application.to_string())
            .field("reduced", &self.reduced.to_string())
            .finish()
    }
}

impl fmt::Debug for StructuralDefinitionCongruenceBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StructuralDefinitionCongruenceBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("reductions", &self.reductions)
            .finish()
    }
}

impl fmt::Debug for StructuralKnownEqualityCongruenceBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("StructuralKnownEqualityCongruenceBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .finish()
    }
}
