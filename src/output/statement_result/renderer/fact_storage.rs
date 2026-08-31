//! Stored fact results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn store_fact(&mut self, result: &SuccessStoreFactResult) -> JsonValue {
        success_store_fact_value(result)
    }
}
