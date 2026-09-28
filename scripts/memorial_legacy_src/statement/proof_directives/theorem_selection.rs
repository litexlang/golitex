use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByThmStmt {
    pub call: TheoremCall,
    pub selected_fact: AtomicFact,
    pub line_file: LineFile,
}

impl ByThmStmt {
    pub fn new(
        name: AtomicName,
        args: Vec<Obj>,
        selected_fact: AtomicFact,
        line_file: LineFile,
    ) -> Self {
        Self::new_with_call(
            TheoremCall::parenthesized(name, args),
            selected_fact,
            line_file,
        )
    }

    pub fn new_with_call(
        call: TheoremCall,
        selected_fact: AtomicFact,
        line_file: LineFile,
    ) -> Self {
        ByThmStmt {
            call,
            selected_fact,
            line_file,
        }
    }

    pub fn name(&self) -> &AtomicName {
        &self.call.name
    }

    pub fn args(&self) -> &[Obj] {
        self.call.args()
    }

    pub fn selected_fact_store_reason() -> &'static str {
        "selected theorem consequence"
    }
}

impl fmt::Display for ByThmStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {} {} {} {}",
            BY, THM, self.call, RIGHT_ARROW, self.selected_fact
        )
    }
}
