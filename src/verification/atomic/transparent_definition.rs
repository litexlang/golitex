//! Proof-producing one-pass reduction of atomic facts through executed `let`s.

use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    pub(in crate::verification) fn transparent_definition_reduction_for_atomic_fact(
        &self,
        fact: &AtomicFact,
    ) -> Result<Option<(AtomicFact, TransparentDefinitionReductionEvidence)>, RuntimeError> {
        let pass = self.transparent_object_substitutions_once(fact.args_ref())?;
        if !pass.changed() {
            return Ok(None);
        }
        let reduced = self.inst_atomic_fact(
            fact,
            pass.substitutions(),
            SubstitutionMode::TransparentDefinition,
            None,
        )?;
        let definitions = pass
            .definitions()
            .iter()
            .map(|definition_use| TransparentDefinitionReductionUse {
                symbol: definition_use.symbol.clone(),
                definition_object: definition_use.definition.value().clone(),
                defining_equality: definition_use.definition.defining_equality().clone(),
                defining_equality_fact_id: definition_use.definition.defining_equality_fact_id(),
            })
            .collect();
        Ok(Some((
            reduced,
            TransparentDefinitionReductionEvidence::new(definitions),
        )))
    }

    pub(in crate::verification) fn retarget_transparent_definition_reduction_result(
        &self,
        goal: &AtomicFact,
        reduced_result: ProveFactResult,
        evidence: TransparentDefinitionReductionEvidence,
    ) -> ProveFactResult {
        let Some(success) = reduced_result.factual_success() else {
            return reduced_result;
        };
        let transformed = Rc::new(SuccessFactProofNode::new(
            goal.clone().into(),
            SuccessFactProofResult::Transform(Box::new(SuccessTransformFactResult::from_shared(
                FactTransformationRule::TransparentDefinitionReduction(evidence),
                success.verification.clone(),
            ))),
        ));
        SuccessProveFactResult::new_with_verified_by_known_fact(
            goal.clone().into(),
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult {
                source: transformed,
            })),
            Vec::new(),
        )
        .into()
    }
}
