//! Witness statements: constructive introduction of exist / `$P` / nonempty set.
//! Optional local proof body (full Stmt); obligations checked after proof in that scope.

mod exec_witness_atomic_fact;
mod exec_witness_exist_fact;
mod exec_witness_nonempty_set;

pub use exec_witness_atomic_fact::{
    ExecWitnessAtomicFactStmtFailed, ExecWitnessAtomicFactStmtResult,
    ExecWitnessAtomicFactStmtSuccessResult,
};
pub use exec_witness_exist_fact::{
    ExecWitnessExistFactStmtFailed, ExecWitnessExistFactStmtResult,
    ExecWitnessExistFactStmtSuccessResult, ExecWitnessStmtResult, WitnessExistAmbientSuccess,
    WitnessExistObligationSuccess,
};
pub use exec_witness_nonempty_set::{
    ExecWitnessNonemptySetStmtFailed, ExecWitnessNonemptySetStmtResult,
    ExecWitnessNonemptySetStmtSuccessResult,
};
