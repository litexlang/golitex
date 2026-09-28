//! Builtin verification for proper subset and superset relations.

use crate::prelude::*;

impl Runtime {
    pub fn verify_builtin_proper_set_relation_from_quantifier_free_premise(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Some(premise) = proper_set_relation_definition_premise(self, atomic_fact) else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        let Some(premise_result) = self.try_verify_builtin_rule_premise(&premise, builtin_state)?
        else {
            return Ok(UnknownGenericStmtResult::new().into());
        };

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                format!(
                    "{} from its complete quantifier-free definition premise",
                    atomic_fact
                ),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyBuiltinProperSetRelationFromQuantifierFreePremise),
                vec![premise_result],
            )
            .into(),
        )
    }

    // Proper containment is ordinary containment plus inequality.
    // Example: `A $subset B` and `A != B` prove `A $proper_subset B`.
    pub fn verify_builtin_proper_set_relation_by_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(definition_facts) = proper_set_relation_definition_facts(self, atomic_fact) else {
            return Ok(None);
        };

        let mut inside_results = Vec::with_capacity(definition_facts.len());
        for definition_fact in definition_facts {
            let result = self.verify_fact_allow_unknown(&definition_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
            inside_results.push(result);
        }

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                format!(
                    "{} by its builtin proper-set-relation definition",
                    atomic_fact.key()
                ),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyBuiltinProperSetRelationByDefinition,
                ),
                inside_results,
            )
            .into(),
        ))
    }
}

// A positive proper-containment fact safely exposes both parts of its definition.
// Example: `A $proper_subset B` infers `A $subset B` and `A != B`.
pub fn positive_proper_set_relation_definition_facts(
    runtime: &Runtime,
    fact: &NormalAtomicFact,
) -> Option<Vec<Fact>> {
    let AtomicName::WithoutMod(name) = &fact.predicate else {
        return None;
    };
    if fact.body.len() != 2 {
        return None;
    }

    let left = fact.body[0].clone();
    let right = fact.body[1].clone();
    let containment: Fact = match name.as_str() {
        PROPER_SUBSET => runtime
            .new_subset_fact(left.clone(), right.clone(), fact.line_file.clone())
            .into(),
        PROPER_SUPERSET => runtime
            .new_subset_fact(right.clone(), left.clone(), fact.line_file.clone())
            .into(),
        _ => return None,
    };
    let not_equal = runtime
        .new_not_equal_fact(left, right, fact.line_file.clone())
        .into();
    Some(vec![containment, not_equal])
}

pub fn is_builtin_proper_set_relation_fact(fact: &AtomicFact) -> bool {
    match fact {
        AtomicFact::NormalAtomicFact(fact) => matches!(
            &fact.predicate,
            AtomicName::WithoutMod(name)
                if matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET)
        ),
        AtomicFact::NotNormalAtomicFact(fact) => matches!(
            &fact.predicate,
            AtomicName::WithoutMod(name)
                if matches!(name.as_str(), PROPER_SUBSET | PROPER_SUPERSET)
        ),
        _ => false,
    }
}

fn proper_set_relation_definition_facts(runtime: &Runtime, fact: &AtomicFact) -> Option<Vec<Fact>> {
    match fact {
        AtomicFact::NormalAtomicFact(fact) => {
            positive_proper_set_relation_definition_facts(runtime, fact)
        }
        AtomicFact::NotNormalAtomicFact(fact) => {
            let AtomicName::WithoutMod(name) = &fact.predicate else {
                return None;
            };
            if fact.body.len() != 2 {
                return None;
            }

            let left = fact.body[0].clone();
            let right = fact.body[1].clone();
            let not_containment: AtomicFact = match name.as_str() {
                PROPER_SUBSET => runtime
                    .new_not_subset_fact(left.clone(), right.clone(), fact.line_file.clone())
                    .into(),
                PROPER_SUPERSET => runtime
                    .new_not_superset_fact(left.clone(), right.clone(), fact.line_file.clone())
                    .into(),
                _ => return None,
            };
            let equal: AtomicFact = runtime
                .new_equal_fact(left, right, fact.line_file.clone())
                .into();
            let definition: Fact = runtime
                .new_or_fact(
                    vec![
                        AndChainAtomicFact::AtomicFact(not_containment),
                        AndChainAtomicFact::AtomicFact(equal),
                    ],
                    fact.line_file.clone(),
                )
                .into();
            Some(vec![definition])
        }
        _ => None,
    }
}

fn proper_set_relation_definition_premise(
    runtime: &Runtime,
    fact: &AtomicFact,
) -> Option<QuantifierFreeFact> {
    match proper_set_relation_definition_facts(runtime, fact)?.as_slice() {
        [Fact::AtomicFact(left), Fact::AtomicFact(right)] => Some(QuantifierFreeFact::AndFact(
            runtime.new_and_fact(vec![left.clone(), right.clone()], fact.line_file()),
        )),
        [Fact::OrFact(or_fact)] => Some(QuantifierFreeFact::OrFact(or_fact.clone())),
        _ => None,
    }
}
