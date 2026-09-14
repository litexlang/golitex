//! New-pipeline AST framework (legacy taxonomy, adapted identity).

pub mod conversions;
pub mod fact;
pub mod line_file;
pub mod names;
pub mod obj;
pub mod param;
pub mod stmt;

pub use fact::Fact;
pub use line_file::LineFile;
pub use names::{AtomicName, PropName};
pub use obj::Obj;
pub use stmt::Stmt;
