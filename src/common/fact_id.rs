use std::fmt;

/// Runtime-unique identity for one fact stored in an environment.
///
/// Display text is deliberately not the identity: alpha-normalized and
/// nested-binder cache aliases for the same stored fact share one `FactId`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FactId(u64);

impl FactId {
    pub(crate) fn new(value: u64) -> Self {
        FactId(value)
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
