use std::fmt;

// -----------------------------------------------------------------------------
// Public runtime identifiers
// -----------------------------------------------------------------------------

/// Identity of a fact in the new pipeline.
///
/// This is intentionally owned by the new runtime design.  It is not an alias
/// of the legacy `crate::fact::id::FactId`; compatibility with the old
/// pipeline, if needed later, should be an explicit conversion at the
/// boundary rather than an accidental shared dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FactId(u64);

/// Legacy numeric identity used by the draft runtime while typed IDs migrate.
pub type Id = u64;

/// Identity space reserved for predicate algebraic-property records.
pub type PropAlgebraicPropertyId2 = u64;

/// Stable identity for an atom owned by the runtime's parse/execution state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AtomId(u64);

/// Identity of a well-definedness proof stored in an execution environment.
///
/// Allocated by `Runtime::next_well_definedness_id` (when wired). A `ByReuse`
/// result cites this ID; later consumers can use it to recover the WD proof
/// payload retained by the corresponding result/environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WellDefinednessId2(u64);

// -----------------------------------------------------------------------------
// Formatting and accessors
// -----------------------------------------------------------------------------

impl FactId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

impl AtomId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

impl WellDefinednessId2 {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

impl fmt::Display for FactId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "f{}", self.0)
    }
}

impl fmt::Display for WellDefinednessId2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "wd{}", self.0)
    }
}
