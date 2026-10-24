use crate::execute::execute_by_stmt::{
    ByInducBodySuccess, ExecByInducStmtSuccess, ExecByStrongInducStmtSuccess,
};
use crate::prelude::*;

/// Borrowed view of the two executor-owned induction results.
#[derive(Clone, Copy)]
pub(in crate::compile_to_lean) struct InductionEvidence<'a> {
    pub strong: bool,
    pub parameter: &'a BoundName,
    pub induc_from: &'a Obj,
    pub goals: &'a Vec<Fact>,
    pub from_in_z: &'a VerifyFactResult,
    pub introduced_parameter: &'a IntroduceTypedParametersResult,
    pub goal_domain: &'a AssumeDomFactResult,
    pub goals_wd: &'a Vec<VerifyFactWellDefinedResult>,
    pub goal_wd_env: &'a Box<ExecEnv>,
    pub body: &'a ByInducBodySuccess,
    pub stored: &'a StoreFactAndInferResult,
}
impl<'a> From<&'a ExecByInducStmtSuccess> for InductionEvidence<'a> {
    fn from(p: &'a ExecByInducStmtSuccess) -> Self {
        Self {
            strong: false,
            parameter: &p.parameter,
            induc_from: &p.induc_from,
            goals: &p.goals,
            from_in_z: &p.from_in_z,
            introduced_parameter: &p.introduced_parameter,
            goal_domain: &p.goal_domain,
            goals_wd: &p.goals_wd,
            goal_wd_env: &p.goal_wd_env,
            body: &p.body,
            stored: &p.stored,
        }
    }
}
impl<'a> From<&'a ExecByStrongInducStmtSuccess> for InductionEvidence<'a> {
    fn from(p: &'a ExecByStrongInducStmtSuccess) -> Self {
        Self {
            strong: true,
            parameter: &p.parameter,
            induc_from: &p.induc_from,
            goals: &p.goals,
            from_in_z: &p.from_in_z,
            introduced_parameter: &p.introduced_parameter,
            goal_domain: &p.goal_domain,
            goals_wd: &p.goals_wd,
            goal_wd_env: &p.goal_wd_env,
            body: &p.body,
            stored: &p.stored,
        }
    }
}
