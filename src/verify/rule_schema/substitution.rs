use crate::prelude::*;

#[derive(Clone)]
pub struct RuleSubstitution {
    bindings: Vec<Obj>,
}

impl RuleSubstitution {
    pub(crate) fn new(bindings: Vec<Obj>) -> Self {
        Self { bindings }
    }

    pub fn bindings(&self) -> &[Obj] {
        &self.bindings
    }
}
