//! Definition projection evidence.

use crate::prelude::*;
use std::fmt;

/// Checked definition-elimination certificate for an existential hidden
/// behind one concrete proposition call. The enclosing result is the
/// instantiated existential and has exactly one child: a proof of `source`.
#[derive(Clone)]
pub struct DefinitionProjectionBuiltinRuleEvidence {
    pub fact: NormalAtomicFact,
    pub definition: DefPropStmt,
}

impl DefinitionProjectionBuiltinRuleEvidence {
    pub fn new(fact: NormalAtomicFact, definition: DefPropStmt) -> Self {
        Self { fact, definition }
    }
}

impl fmt::Debug for DefinitionProjectionBuiltinRuleEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("DefinitionProjectionBuiltinRuleEvidence")
            .field("source", &self.fact.to_string())
            .field("definition", &self.definition.name)
            .finish()
    }
}
