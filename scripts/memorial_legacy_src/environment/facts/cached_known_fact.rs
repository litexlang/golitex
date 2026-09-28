//! Cached fact lookup payload.

use crate::prelude::*;

/// The deliberately small payload kept by the fact cache.
///
/// Proof trees, origins, scopes, and Lean names belong to statement Results
/// and compiler state. The environment only needs a stable identity and the
/// source location already used by diagnostics.
#[derive(Clone, Debug)]
pub struct CachedKnownFact {
    pub fact_id: FactId,
    pub line_file: LineFile,
    pub equivalent_proposition_lookup_key: FactString,
}
