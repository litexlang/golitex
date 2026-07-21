use crate::prelude::*;

impl Runtime {
    // Proper containment is ordinary containment plus inequality.
    // Example: `A $subset B` and `A != B` prove `A $proper_subset B`.
    pub(crate) fn verify_builtin_proper_set_relation_by_definition(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
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
            SupersetFact::new(left.clone(), right.clone(), fact.line_file.clone()).into()
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
