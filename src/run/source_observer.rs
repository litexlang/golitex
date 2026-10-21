use crate::prelude::*;
use crate::tokenize::TokenBlock;

/// Read-only access to the source and evidence at their actual execution stage.
pub trait SourceObserver {
    fn requires_source_evidence(&self) -> bool {
        false
    }

    fn source(&mut self, _runtime: &Runtime, _code: &str) {}

    fn statement(
        &mut self,
        _runtime: &Runtime,
        _block: &TokenBlock,
        _statement: &Stmt,
        _result: &ExecStmtResult,
    ) {
    }

    fn completed(&mut self, _runtime: &Runtime, _result: &RunLitexCodeResult) {}

    fn source_error(&mut self, _runtime: &Runtime, _error: &RuntimeError) {}
}

impl SourceObserver for () {}
