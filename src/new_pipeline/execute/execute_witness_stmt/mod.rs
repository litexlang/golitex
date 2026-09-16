//! `witness exist … from …` — constructive exist introduction (no local binder env).

mod exec_witness_exist_fact;

pub use exec_witness_exist_fact::{
    ExecWitnessExistFactStmtFailed, ExecWitnessExistFactStmtResult,
    ExecWitnessExistFactStmtSuccessResult, ExecWitnessStmtResult,
};
