use crate::atomic_fact::AtomicFact;

pub struct OrFact {
    pub facts: Vec<Box<AtomicFact>>,
}