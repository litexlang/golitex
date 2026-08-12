use crate::prelude::*;

impl Runtime {
    pub fn exec_by_zorn_lemma_stmt(
        &mut self,
        stmt: &ByZornLemmaStmt,
    ) -> Result<StmtResult, RuntimeError> {
        Err(zorn_lemma_named_property_error(stmt))
    }

    pub(crate) fn exec_by_zorn_lemma_stmt_affect_environment_only(
        &mut self,
        stmt: &ByZornLemmaStmt,
    ) -> Result<StmtResult, RuntimeError> {
        Err(zorn_lemma_named_property_error(stmt))
    }
}

fn zorn_lemma_named_property_error(stmt: &ByZornLemmaStmt) -> RuntimeError {
    short_exec_error(
        stmt.clone().into(),
        "by zorn_lemma is unavailable: its former conclusion used an anonymous `forall` inside \
         an existential body; define a named maximality property and use an explicit theorem \
         interface"
            .to_string(),
        None,
        vec![],
    )
}
