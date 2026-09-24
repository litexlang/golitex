//! Attach an executable presentation to an already-defined mathematical function.
//!
//! Surface: `have algo for fn f(x): …`
//! Pipeline: resolve target fn → align params / build reqs → case agreements →
//! default or coverage → store in `algorithm_definitions`.

mod exec_def_algo_stmt;
mod helper;
mod result;

pub use exec_def_algo_stmt::exec_def_algo_stmt;
pub use result::{
    ExecDefAlgoBranchAgreement, ExecDefAlgoCaseAgreement, ExecDefAlgoClosing,
    ExecDefAlgoCoverageAgreement, ExecDefAlgoSetup, ExecDefAlgoStmtFailed, ExecDefAlgoStmtResult,
    ExecDefAlgoStmtSuccess,
};
