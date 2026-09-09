use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

/// Globally unique identity for one fact node created during the process.
///
/// The identity belongs to the node, not to its rendered proposition or to the
/// environment in which it is eventually stored. Cloning a node preserves its
/// identity; every constructor that creates a new node obtains a fresh one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FactId(u64);

static NEXT_FACT_ID: AtomicU64 = AtomicU64::new(1);

impl FactId {
    /// Construct an explicit identity for fixtures and compatibility tests.
    pub fn new(value: u64) -> Self {
        FactId(value)
    }

    /// Allocate a legacy process-wide identity.
    ///
    /// Production code must use `Runtime::allocate_fact_id`; this method stays
    /// temporarily available for the constructor migration and fixed fixtures.
    #[deprecated(note = "production facts must be created through Runtime")]
    pub fn fresh() -> Self {
        let value = NEXT_FACT_ID
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
                value.checked_add(1)
            })
            .expect("fact ID space exhausted");
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
