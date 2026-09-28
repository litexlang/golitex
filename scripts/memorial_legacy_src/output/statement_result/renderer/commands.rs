//! Command statement results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn command_stmt(
        &mut self,
        result: &SuccessCommandStmtResult,
    ) -> JsonValue {
        match result {
            SuccessCommandStmtResult::EvalStmt(result) => self.non_fact_stmt(
                "EvalStmt",
                result.statement.to_string(),
                &result.common,
                vec![
                    (
                        "execution".to_string(),
                        eval_stmt_execution_result_value(&result.execution),
                    ),
                    (
                        "reported_store_facts".to_string(),
                        array(
                            result
                                .common
                                .infers
                                .store_fact_outputs
                                .iter()
                                .map(store_fact_output_value)
                                .collect(),
                        ),
                    ),
                ],
            ),
        }
    }
}
