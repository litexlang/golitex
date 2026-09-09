use crate::prelude::*;

/// One checked edge in a path through the stored equality graph.
///
/// `equality` is the original fact that justified the edge. `from` and `to`
/// record the orientation in which a compiler must use that fact.
#[derive(Clone)]
pub struct KnownEqualityProofStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
    /// The exact environment fact that supplied this proof edge.
    ///
    /// `EqualFact` already owns this identity; keeping it beside the oriented
    /// path step means downstream compiler consumers do not have to rediscover
    /// it from a rendered proposition.
    pub fact_id: FactId,
}

impl std::fmt::Debug for KnownEqualityProofStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KnownEqualityProofStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .field("fact_id", &self.fact_id)
            .finish()
    }
}
