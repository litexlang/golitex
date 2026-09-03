//! Successful fact statements.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn success_fact_stmt(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> JsonValue {
        let evidence = match &result.evidence {
            FactStatementEvidence::Verified(verified) => object(vec![
                string_field("kind", "Verified"),
                (
                    "well_definedness".to_string(),
                    self.fact_well_definedness(&verified.checked),
                ),
                (
                    "proof".to_string(),
                    self.verify_fact(verified.verification.as_ref()),
                ),
            ]),
            FactStatementEvidence::Trusted(_) => object(vec![string_field("kind", "Trusted")]),
        };
        object(vec![
            string_field("kind", "Fact"),
            string_field("statement", result.fact().to_string()),
            ("evidence".to_string(), evidence),
            ("store".to_string(), self.store_fact(&result.store)),
        ])
    }
}
