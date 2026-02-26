struct ForallFact {
    pub params: Vec<String>,
    pub param_sets: Vec<ParameterSet>,
    pub fact: Box<AtomicFact>,
    pub line: u32,
}