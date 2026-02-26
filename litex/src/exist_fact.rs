use crate::atomic_fact::AtomicFact;
use crate::parameter_set::ParameterSet;

pub enum ExistFact {
    TrueExistFact(TrueExistFact),
    NotExistFact(NotExistFact),
}

pub struct TrueExistFact {
    pub exist_params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub fact: Box<AtomicFact>,
    pub line: u32,
}

pub struct NotExistFact {
    pub exist_params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub fact: Box<AtomicFact>,
    pub line: u32,
}