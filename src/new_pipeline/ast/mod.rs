//! New-pipeline AST framework (legacy taxonomy, adapted identity).

pub mod fact;
pub mod names;
pub mod obj;
pub mod param;
pub mod source_span;
pub mod stmt;

pub use fact::Fact;
pub use names::{AtomicName, PropName};
pub use obj::Obj;
pub use source_span::SourceSpan;
pub use stmt::Stmt;
