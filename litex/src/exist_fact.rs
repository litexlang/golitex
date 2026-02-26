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

impl TrueExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        fact: Box<AtomicFact>,
        line: u32,
    ) -> Self {
        TrueExistFact { exist_params, param_sets, fact, line }
    }
}

impl NotExistFact {
    pub fn new(
        exist_params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        fact: Box<AtomicFact>,
        line: u32,
    ) -> Self {
        NotExistFact { exist_params, param_sets, fact, line }
    }
}

// impl ExistFact {
//     pub fn box_true_exist_fact(...) -> Box<ExistFact> {
//         Box::new(ExistFact::TrueExistFact(TrueExistFact::new(...)))
//     }
//     pub fn box_not_exist_fact(...) -> Box<ExistFact> {
//         Box::new(ExistFact::NotExistFact(NotExistFact::new(...)))
//     }
// }