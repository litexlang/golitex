use crate::parameter_set::ParameterSet;
use crate::specific_fact::SpecFact;

pub struct ForallFact {
    pub params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub dom_facts: Vec<Box<SpecFact>>,
    pub then_facts: Vec<Box<SpecFact>>,
    pub line: u32,
}

impl ForallFact {
    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ParameterSet>,
        dom_facts: Vec<Box<SpecFact>>,
        then_facts: Vec<Box<SpecFact>>,
        line: u32,
    ) -> Self {
        ForallFact { params, param_sets, dom_facts, then_facts, line }
    }
}