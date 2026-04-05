//! Surface syntax for `by …` proof statements (one submodule per form).
mod cases;
mod contra;
mod enumerate;
mod extension;
mod fn_cart_tuple;
mod for_stmt;
mod induc;

pub use cases::ByCasesStmt;
pub use contra::ByContraStmt;
pub use enumerate::ByEnumerateStmt;
pub use extension::ByExtensionStmt;
pub use fn_cart_tuple::{ByFnStmt, ByTupleStmt};
pub use for_stmt::{ByForStmt, ClosedRangeOrRange};
pub use induc::ByInducStmt;
