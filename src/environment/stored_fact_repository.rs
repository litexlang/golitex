use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

/// The canonical environment-owned record for a fact identity.
///
/// Lookup strings are aliases only. An alias keeps the first representative
/// `FactId` for its proposition-equivalence class, while every independently
/// stored fact identity remains available through `facts_by_id`.
#[derive(Clone)]
pub struct EnvironmentStoredFact {
    pub fact_id: FactId,
    pub fact: Fact,
    pub equivalent_proposition_lookup_key: FactString,
}

#[derive(Clone, Default)]
pub struct EnvironmentStoredFactRepository {
    facts_by_id: HashMap<FactId, Rc<EnvironmentStoredFact>>,
    fact_lookup_by_key: HashMap<FactString, CachedKnownFact>,
}

impl EnvironmentStoredFactRepository {
    pub fn stored_fact_count(&self) -> usize {
        self.facts_by_id.len()
    }

    pub fn lookup_key_count(&self) -> usize {
        self.fact_lookup_by_key.len()
    }

    pub fn stored_fact(&self, fact_id: FactId) -> Option<&Rc<EnvironmentStoredFact>> {
        self.facts_by_id.get(&fact_id)
    }

    pub fn lookup(&self, key: &str) -> Option<&CachedKnownFact> {
        self.fact_lookup_by_key.get(key)
    }

    pub fn lookup_keys(&self) -> impl Iterator<Item = &FactString> {
        self.fact_lookup_by_key.keys()
    }

    pub fn record_fact(&mut self, fact: Fact, fact_id: FactId) -> Result<(), RuntimeError> {
        let equivalent_proposition_lookup_key = nested_obj_binder_normalized_fact_key(&fact);
        self.record_fact_with_equivalent_proposition_key(
            fact,
            fact_id,
            equivalent_proposition_lookup_key,
        )
    }

    pub fn record_fact_with_equivalent_proposition_key(
        &mut self,
        fact: Fact,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        if let Some(existing) = self.facts_by_id.get(&fact_id) {
            if existing.equivalent_proposition_lookup_key != equivalent_proposition_lookup_key {
                return Err(StoreFactRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "FactId `{fact_id}` already identifies `{}`, cannot retarget it to `{fact}`",
                            existing.fact
                        ),
                        fact.line_file(),
                    ),
                )
                .into());
            }
            return Ok(());
        }
        self.facts_by_id.insert(
            fact_id,
            Rc::new(EnvironmentStoredFact {
                fact_id,
                fact,
                equivalent_proposition_lookup_key,
            }),
        );
        Ok(())
    }

    pub fn record_lookup_key(
        &mut self,
        key: FactString,
        line_file: LineFile,
        fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        let equivalent_proposition_lookup_key = self
            .facts_by_id
            .get(&fact_id)
            .map(|stored| nested_obj_binder_normalized_fact_key(&stored.fact))
            .unwrap_or_else(|| key.clone());
        self.record_lookup_key_with_equivalent_proposition_key(
            key,
            line_file,
            fact_id,
            equivalent_proposition_lookup_key,
        )
    }

    pub fn record_lookup_key_with_equivalent_proposition_key(
        &mut self,
        key: FactString,
        line_file: LineFile,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        if let Some(existing) = self.fact_lookup_by_key.get(&key) {
            if existing.fact_id != fact_id {
                let existing_stored_fact = self.facts_by_id.get(&existing.fact_id);
                let attempted_stored_fact = self.facts_by_id.get(&fact_id);
                let existing_fact = existing_stored_fact
                    .map(|stored| stored.fact.to_string())
                    .unwrap_or_else(|| "<missing canonical fact>".to_string());
                let attempted_fact = attempted_stored_fact
                    .map(|stored| stored.fact.to_string())
                    .unwrap_or_else(|| "<missing canonical fact>".to_string());
                // A committed child environment may have independently proved
                // an alpha-equivalent proposition and therefore retained a
                // distinct FactId for its statement result. Keep both records
                // citeable, but leave the convenience alias on the first one.
                // The explicit equivalence key is computed while the fact's
                // binders are still available to Runtime; comparing rendered
                // propositions here would mistake alpha-renaming for a conflict.
                if existing.equivalent_proposition_lookup_key == equivalent_proposition_lookup_key {
                    return Ok(());
                }
                return Err(StoreFactRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "fact lookup key `{key}` already resolves to `{}` (`{existing_fact}`), cannot retarget it to `{fact_id}` (`{attempted_fact}`)",
                            existing.fact_id,
                        ),
                        line_file,
                    ),
                )
                .into());
            }
            return Ok(());
        }
        self.fact_lookup_by_key.insert(
            key,
            CachedKnownFact {
                fact_id,
                line_file,
                equivalent_proposition_lookup_key,
            },
        );
        Ok(())
    }

    pub fn merge_from(
        &mut self,
        child: EnvironmentStoredFactRepository,
    ) -> Result<(), RuntimeError> {
        for (_, stored_fact) in child.facts_by_id {
            self.record_fact_with_equivalent_proposition_key(
                stored_fact.fact.clone(),
                stored_fact.fact_id,
                stored_fact.equivalent_proposition_lookup_key.clone(),
            )?;
        }
        for (key, lookup) in child.fact_lookup_by_key {
            self.record_lookup_key_with_equivalent_proposition_key(
                key,
                lookup.line_file,
                lookup.fact_id,
                lookup.equivalent_proposition_lookup_key,
            )?;
        }
        Ok(())
    }
}
