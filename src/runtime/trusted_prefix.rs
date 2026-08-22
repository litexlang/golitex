use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct TrustedPrefixReport {
    pub file: String,
    pub before_line: usize,
    pub trusted_top_level_statements: usize,
    pub first_verified_statement_line: usize,
}

impl TrustedPrefixReport {
    pub fn new(
        file: String,
        before_line: usize,
        trusted_top_level_statements: usize,
        first_verified_statement_line: usize,
    ) -> Self {
        TrustedPrefixReport {
            file,
            before_line,
            trusted_top_level_statements,
            first_verified_statement_line,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TrustedPrefixPolicy {
    pub module_id: ModuleId,
    pub layer: ExecutionLayer,
    pub before_line: usize,
}

impl TrustedPrefixPolicy {
    pub(crate) fn new(module_id: ModuleId, layer: ExecutionLayer, before_line: usize) -> Self {
        TrustedPrefixPolicy {
            module_id,
            layer,
            before_line,
        }
    }

    pub(crate) fn matches(&self, module_id: ModuleId, layer: ExecutionLayer) -> bool {
        self.module_id == module_id && self.layer == layer
    }
}
