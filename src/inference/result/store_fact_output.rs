use crate::prelude::*;
use std::collections::HashSet;

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
