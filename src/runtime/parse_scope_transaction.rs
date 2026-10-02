use super::{ParseScope, Runtime};

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
}
