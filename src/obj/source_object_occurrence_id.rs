use crate::prelude::*;

/// Parser-owned identity of one source object occurrence.
///
/// Cloning, alpha-renaming, and theorem instantiation retain this identity so
/// compiler evidence never has to recover an application by rendered text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourceObjectOccurrenceId(SymbolId);

impl SourceObjectOccurrenceId {
    pub(crate) fn new(id: SymbolId) -> Self {
        Self(id)
    }

    pub fn value(self) -> u64 {
        self.0.value()
    }
}
