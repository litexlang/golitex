use crate::prelude::*;

impl Runtime {
    pub fn exec_by_axiom_of_choice_stmt(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        Err(axiom_of_choice_named_property_error(stmt))
    }

    pub(crate) fn exec_by_axiom_of_choice_stmt_affect_environment_only(
        &mut self,
        stmt: &ByAxiomOfChoiceStmt,
    ) -> Result<StmtResult, RuntimeError> {
        Err(axiom_of_choice_named_property_error(stmt))
    }
}

fn axiom_of_choice_named_property_error(stmt: &ByAxiomOfChoiceStmt) -> RuntimeError {
    short_exec_error(
        stmt.clone().into(),
        "by axiom_of_choice is unavailable: its former conclusion used an anonymous `forall` \
         inside an existential body; use the explicit `general_cart_nonempty_by_choice_*` theorem \
         interface, or define a named property for the quantified condition"
            .to_string(),
        None,
        vec![],
    )
}
