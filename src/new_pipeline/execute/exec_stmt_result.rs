//! Statement execution results for new_pipeline.
//!
//! ExecStmtResult records what one statement did after it finished:
//! - global env effect mirrors (option A: ExecEnv remains authoritative)
//! - for facts, the full verify / proof track
//!
//! Local proof environments (e.g. forall binder scope) belong on verify
//! nodes such as VerifyForallFactResult2.local_env, not as a second global env.

use crate::new_pipeline::ast::stmt::LetObjStmt;
use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult2;
use crate::new_pipeline::runtime::FactId;

pub enum ExecStmtResult {
    Fact(ExecFactStmtResult2),
    Definition(ExecDefinitionStmtResult),
}

pub enum ExecDefinitionStmtResult {
    LetObj(ExecLetObjStmtResult),
}

// Parse occupied the name; definition storage into ExecEnv comes later.
// effect lists what this let contributed once storage is wired.
pub struct ExecLetObjStmtResult {
    pub statement: LetObjStmt,
    pub effect: LetObjEffect,
}

pub struct LetObjEffect {
    // Reserved for transparent-definition / equality fact ids after store lands.
    pub stored_fact_ids: Vec<FactId>,
}

impl LetObjEffect {
    pub fn empty() -> Self {
        Self {
            stored_fact_ids: Vec::new(),
        }
    }
}
