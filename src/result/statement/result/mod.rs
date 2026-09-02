mod annotations;
mod conversions;
mod inspection;
mod outcome;
mod success_access;

pub use outcome::{ProveFactResult, StmtResult, UnknownStmtResult};

#[cfg(test)]
#[path = "../../../../tests/unit/result/statement/result.rs"]
mod tests;
