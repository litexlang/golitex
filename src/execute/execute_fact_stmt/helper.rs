use crate::ast::fact::Fact;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // The stage dispatcher has already restricted this premise's permissions.
    pub(crate) fn verify_builtin_rule_premise(
        &mut self,
        premise: &Fact,
        premise_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        self.verify_fact(premise, premise_state)
    }
}
