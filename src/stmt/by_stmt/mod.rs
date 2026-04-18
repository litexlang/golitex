//! Surface syntax for `by …` proof statements (one submodule per form).
mod cases;
mod contra;
mod enumerate;
mod extension;
mod family;
mod fn_cart_tuple;
mod for_stmt;
mod induc;
mod struct_stmt;

pub use cases::ByCasesStmt;
pub use contra::ByContraStmt;
pub use enumerate::ByEnumerateFiniteSetStmt;
pub use extension::ByExtensionStmt;
pub use family::ByFamilyStmt;
pub use fn_cart_tuple::{ByFnSetStmt, ByFnStmt, ByTupleStmt};
pub use for_stmt::{ByForStmt, ClosedRangeOrRange};
pub use induc::ByInducStmt;
pub use struct_stmt::ByStructStmt;
