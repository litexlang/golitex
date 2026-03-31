use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct InferResult {
    pub infer_facts: Vec<String>,
}

impl InferResult {
    pub fn new() -> Self {
        InferResult {
            infer_facts: vec![],
        }
    }

    pub fn new_fact(&mut self, fact: &Fact) {
        self.infer_facts.push(fact.to_string());
    }

    pub fn push_atomic_fact(&mut self, atomic_fact: &AtomicFact) {
        self.infer_facts.push(atomic_fact.to_string());
    }

    pub fn new_infer_result_inside(&mut self, other_infer_result: InferResult) {
        for infer_fact in other_infer_result.infer_facts {
            self.infer_facts.push(infer_fact);
        }
    }
}
