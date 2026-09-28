//! Shared state and Runtime forwarding for universal argument matching.

use super::*;

pub(super) struct ArgMatcher<'runtime> {
    pub(super) runtime: &'runtime mut Runtime,
    pub(super) active_bindings: Vec<SymbolId>,
}

impl<'runtime> ArgMatcher<'runtime> {
    pub(super) fn new(runtime: &'runtime mut Runtime, active_bindings: Vec<SymbolId>) -> Self {
        Self {
            runtime,
            active_bindings,
        }
    }
}

impl std::ops::Deref for ArgMatcher<'_> {
    type Target = Runtime;

    fn deref(&self) -> &Self::Target {
        self.runtime
    }
}

impl std::ops::DerefMut for ArgMatcher<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.runtime
    }
}
