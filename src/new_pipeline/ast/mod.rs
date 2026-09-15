//! New-pipeline AST framework (legacy taxonomy, adapted identity).

pub mod alpha_normalize;
pub mod conversions;
pub mod fact;
pub mod line_file;
pub mod names;
pub mod obj;
pub mod param;
pub mod stmt;

pub use fact::Fact;
pub use line_file::LineFile;
pub use names::{AtomicName, PlainName};
pub use obj::Obj;
pub use stmt::Stmt;
