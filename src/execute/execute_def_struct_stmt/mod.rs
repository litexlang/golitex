//! Concrete `struct` definition execution.

mod exec_def_struct_stmt;
mod store_struct_definition_facts;

pub use exec_def_struct_stmt::{
    ExecDefStructFieldScopeSuccessResult, ExecDefStructStmtFailed, ExecDefStructStmtResult,
    ExecDefStructStmtSuccessResult,
};

pub(crate) use exec_def_struct_stmt::StructEquivalentFactWellDefinedProof;
pub(crate) use exec_def_struct_stmt::StructFieldWellDefinedAndIntroduced;
pub(crate) use store_struct_definition_facts::StoreStructDefinitionFactResult;
