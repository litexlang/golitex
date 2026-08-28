//! Successful fact statements.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn success_fact_stmt(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "Fact"),
            string_field("statement", result.fact().to_string()),
            (
                "verification".to_string(),
                self.verify_fact(&result.verification),
            ),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness(&result.well_definedness),
            ),
            ("store".to_string(), self.store_fact(&result.store)),
            (
                "execution_trace".to_string(),
                optional_trace(result.execution_trace.as_ref()),
            ),
        ])
    }
}
