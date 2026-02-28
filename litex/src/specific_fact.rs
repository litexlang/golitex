use std::fmt;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;

/// 从 SpecFact 取得 line 与 file_index
pub fn line_file(s: &SpecFact) -> (u32, usize) {
    match s {
        SpecFact::AtomicFact(a) => crate::atomic_fact::line_file(a),
        SpecFact::ExistFact(e) => crate::exist_fact::line_file(e),
    }
}

pub enum SpecFact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
}

impl fmt::Display for SpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpecFact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            SpecFact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
        }
    }
}

