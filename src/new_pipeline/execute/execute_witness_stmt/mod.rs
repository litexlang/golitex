//! Witness statements: constructive introduction of exist / `$P` / nonempty set.
//! No local binder env and no indented proof body in new_pipeline.

mod exec_witness_atomic_fact;
mod exec_witness_exist_fact;
mod exec_witness_nonempty_set;

pub use exec_witness_atomic_fact::{
    ExecWitnessAtomicFactStmtFailed, ExecWitnessAtomicFactStmtResult,
    ExecWitnessAtomicFactStmtSuccessResult,
};
pub use exec_witness_exist_fact::{
    ExecWitnessExistFactStmtFailed, ExecWitnessExistFactStmtResult,
    ExecWitnessExistFactStmtSuccessResult, ExecWitnessStmtResult, WitnessExistCheckSuccess,
};
pub use exec_witness_nonempty_set::{
    ExecWitnessNonemptySetStmtFailed, ExecWitnessNonemptySetStmtResult,
    ExecWitnessNonemptySetStmtSuccessResult,
};
