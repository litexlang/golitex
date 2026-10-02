//! Concrete `template` definition execution.

mod exec_def_template_stmt;
mod store_template_definition_facts;

#[cfg(test)]
#[path = "../../../tests/unit/execute/template_definition_facts/tests.rs"]
mod tests;

pub use store_template_definition_facts::StoreTemplateDefinitionFactResult;

pub use exec_def_template_stmt::{
    AssumedTemplateDomFactResult, ExecDefTemplateStmtFailed, ExecDefTemplateStmtResult,
    ExecDefTemplateStmtSuccessResult, ExecTemplateDefBodyResult,
};
