//! Concrete `template` definition execution.

mod exec_def_template_stmt;

pub use exec_def_template_stmt::{
    AssumedTemplateDomFactResult, ExecDefTemplateStmtFailed, ExecDefTemplateStmtResult,
    ExecDefTemplateStmtSuccessResult, ExecTemplateDefBodyResult,
};
