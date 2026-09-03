//! Canonical fact records and lookup-key registration.

use crate::prelude::*;

impl Environment {
    pub fn store_fact_to_cache_known_fact(
        &mut self,
        fact_key: FactString,
        fact_line_file: LineFile,
        fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        self.facts
            .stored_facts
            .record_lookup_key(fact_key, fact_line_file, fact_id)
    }

    pub fn store_fact_to_cache_known_fact_with_equivalent_proposition_key(
        &mut self,
        fact_key: FactString,
        fact_line_file: LineFile,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        self.facts
            .stored_facts
            .record_lookup_key_with_equivalent_proposition_key(
                fact_key,
                fact_line_file,
                fact_id,
                equivalent_proposition_lookup_key,
            )
    }

    pub fn record_stored_fact(&mut self, fact: Fact, fact_id: FactId) -> Result<(), RuntimeError> {
        self.facts.stored_facts.record_fact(fact, fact_id)
    }

    pub fn record_stored_fact_with_equivalent_proposition_key(
        &mut self,
        fact: Fact,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        self.facts
            .stored_facts
            .record_fact_with_equivalent_proposition_key(
                fact,
                fact_id,
                equivalent_proposition_lookup_key,
            )
    }

    pub fn store_infer_rule_firing(&mut self, firing_key: String) {
        self.inference_cache
            .infer_rule_firings
            .insert(firing_key, ());
    }
}
