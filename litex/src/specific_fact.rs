use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;

pub enum SpecFact {
    AtomicFact(Box<AtomicFact>),
    ExistFact(Box<ExistFact>),
}

// impl SpecFact {
//     pub fn box_atomic_fact(fact: Box<AtomicFact>) -> Box<SpecFact> {
//         Box::new(SpecFact::AtomicFact(fact))
//     }
//     pub fn box_exist_fact(fact: Box<ExistFact>) -> Box<SpecFact> {
//         Box::new(SpecFact::ExistFact(fact))
//     }
// }