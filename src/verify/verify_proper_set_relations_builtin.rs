use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_builtin_proper_set_relation_from_quantifier_free_premise(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(premise) = proper_set_relation_definition_premise(atomic_fact) else {
            return Ok(StmtUnknown::new().into());
        };
        let premise_result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
        if !premise_result.is_true() {
            return Ok(StmtUnknown::new().into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                format!(
                    "{} from its complete quantifier-free definition premise",
                    atomic_fact
                ),
                vec![premise_result],
            )
            .into(),
        )
    }

    // Proper containment is ordinary containment plus inequality.
    // Example: `A $subset B` and `A != B` prove `A $proper_subset B`.
    pub(crate) fn verify_builtin_proper_set_relation_by_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(definition_facts) = proper_set_relation_definition_facts(atomic_fact) else {
            return Ok(None);
        };

        let mut inside_results = Vec::with_capacity(definition_facts.len());
        for definition_fact in definition_facts {
            let result = self.verify_fact_full(&definition_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
            inside_results.push(result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                format!(
                    "{} by its builtin proper-set-relation definition",
                    atomic_fact.key()
                ),
                inside_results,
            )
            .into(),
        ))
    }
}

// A positive proper-containment fact safely exposes both parts of its definition.
// Example: `A $proper_subset B` infers `A $subset B` and `A != B`.
pub(crate) fn positive_proper_set_relation_definition_facts(
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
        PROPER_SUBSET => {
            SubsetFact::new(left.clone(), right.clone(), fact.line_file.clone()).into()
        }
        PROPER_SUPERSET => {
            SubsetFact::new(right.clone(), left.clone(), fact.line_file.clone()).into()
        }
        _ => return None,
    };
    let not_equal = NotEqualFact::new(left, right, fact.line_file.clone()).into();
    Some(vec![containment, not_equal])
}

pub(crate) fn is_builtin_proper_set_relation_fact(fact: &AtomicFact) -> bool {
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

fn proper_set_relation_definition_facts(fact: &AtomicFact) -> Option<Vec<Fact>> {
    match fact {
        AtomicFact::NormalAtomicFact(fact) => positive_proper_set_relation_definition_facts(fact),
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
                PROPER_SUBSET => {
                    NotSubsetFact::new(left.clone(), right.clone(), fact.line_file.clone()).into()
                }
                PROPER_SUPERSET => {
                    NotSupersetFact::new(left.clone(), right.clone(), fact.line_file.clone()).into()
                }
                _ => return None,
            };
            let equal: AtomicFact = EqualFact::new(left, right, fact.line_file.clone()).into();
            let definition: Fact = OrFact::new(
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

fn proper_set_relation_definition_premise(fact: &AtomicFact) -> Option<QuantifierFreeFact> {
    match proper_set_relation_definition_facts(fact)?.as_slice() {
        [Fact::AtomicFact(left), Fact::AtomicFact(right)] => Some(QuantifierFreeFact::AndFact(
            AndFact::new(vec![left.clone(), right.clone()], fact.line_file()),
        )),
        [Fact::OrFact(or_fact)] => Some(QuantifierFreeFact::OrFact(or_fact.clone())),
        _ => None,
    }
}
