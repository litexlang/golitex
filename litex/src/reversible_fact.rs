use crate::specific_fact::SpecFact;
use crate::or_fact::OrFact;

pub enum ReversibleFact {
    SpecFact(Box<SpecFact>),
    OrFact(Box<OrFact>),
}

// impl ReversibleFact {
//     pub fn box_spec_fact(fact: Box<SpecFact>) -> Box<ReversibleFact> {
//         Box::new(ReversibleFact::SpecFact(fact))
//     }
//     pub fn box_or_fact(fact: Box<OrFact>) -> Box<ReversibleFact> {
//         Box::new(ReversibleFact::OrFact(fact))
//     }
// }