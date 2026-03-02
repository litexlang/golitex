use std::fmt;
use crate::or_fact::OrFact;
use crate::forall_fact::ForallFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::and_fact::AndFact;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
    OrFact(OrFact),
    AndFact(AndFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            Fact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
            Fact::OrFact(or_fact) => write!(f, "{}", or_fact),
            Fact::AndFact(and_fact) => write!(f, "{}", and_fact),
            Fact::ForallFact(forall_fact) => write!(f, "{}", forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => write!(f, "{}", forall_fact_with_iff),
        }
    }
}

/// 从 Fact 取得 line 与 file_index（仅用于 Display 等，不保留方法）
impl Fact {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            Fact::AtomicFact(a) => crate::atomic_fact::line_file(a),
            Fact::ExistFact(e) => crate::exist_fact::line_file(e),
            Fact::OrFact(o) => (o.line, o.file_index),
            Fact::AndFact(a) => (a.line, a.file_index),
            Fact::ForallFact(f) => (f.line, f.file_index),
            Fact::ForallFactWithIff(f) => (f.line, f.file_index),
        }
    }
}