//! Canonical stored fact identity.

use crate::prelude::*;

/// The canonical environment-owned record for a fact identity.
#[derive(Clone)]
pub struct StoredFactRecord {
    pub fact_id: FactId,
    pub fact: Fact,
    pub equivalent_proposition_lookup_key: FactString,
}
