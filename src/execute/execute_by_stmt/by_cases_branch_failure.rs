//! An entered case's checked assumption and detached failed-scope evidence.
use super::result::ByCasesEnteredBranchFailed;
use crate::ast::fact::{AndChainAtomicFact, AtomicFact};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::AssumeDomFactResult;
use crate::runtime::FactId;

pub struct ByCasesBranchFailure {
    pub assumption: AndChainAtomicFact,
    pub assumption_fact_id: FactId,
    pub assumption_components: Vec<(FactId, AtomicFact)>,
    pub assumed: AssumeDomFactResult,
    pub failure: ByCasesEnteredBranchFailed,
    pub local_env: Box<ExecEnv>,
}
