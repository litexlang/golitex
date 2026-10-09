use super::{ParseScope, Runtime};
use crate::prelude::*;

impl Runtime {
    /// Install temporary parse scopes and return the originals for rollback.
    /// Keeping the installed scopes commits; assigning the originals restores.
    pub(crate) fn begin_parse_scope_transaction(&mut self) -> Vec<Box<ParseScope>> {
        // Parsing reserves names before verification. exec_stmt's temporary
        // ExecEnv protects definitions/facts, but it cannot undo these separate
        // parse bindings: a failed `have k N = -1` would otherwise block a
        // corrected `have k N = 1` in the same session.
        //
        // Copy the existing layers instead of pushing a lexical scope. Index 0
        // must remain the file root: moving a declaration to an extra layer
        // would change its export qualification and subsequent lookup identity.
        let temporary_scopes = self
            .parse_scope_stack
            .iter()
            .map(|scope| {
                let mut temporary = ParseScope::new();
                temporary.plain = scope.plain.clone();
                Box::new(temporary)
            })
            .collect();

        // Only scope bindings are isolated. Global IDs must keep increasing:
        // failed ASTs/results may still contain IDs that cannot be reused.
        std::mem::replace(&mut self.parse_scope_stack, temporary_scopes)
    }

    /// Run with temporary parse scopes, then restore the originals.
    /// On Ok, return the temporary scopes for explicit commit; Err discards them.
    pub(crate) fn run_in_temporary_parse_scopes_and_take_scopes<T, F>(
        &mut self,
        f: F,
    ) -> RuntimeResult<(T, Vec<Box<ParseScope>>)>
    where
        F: FnOnce(&mut Self) -> RuntimeResult<T>,
    {
        let scopes_before = self.begin_parse_scope_transaction();
        let result = f(self);
        let temporary_scopes = std::mem::replace(&mut self.parse_scope_stack, scopes_before);

        result.map(|value| (value, temporary_scopes))
    }
}
