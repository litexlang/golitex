//! Stored fact results.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn store_fact(&mut self, result: &SuccessStoreFactResult) -> JsonValue {
        success_store_fact_value(result)
    }
}
