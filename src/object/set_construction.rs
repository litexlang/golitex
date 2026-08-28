//! Power sets, finite enumerations, and set builders.

use crate::prelude::*;

#[derive(Clone)]
pub struct PowerSet {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct ListSet {
    pub list: Vec<Box<Obj>>,
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
}

#[derive(Clone)]
pub struct SetBuilder {
    pub param_binding: SymbolBinding,
    pub param_set: Box<Obj>,
    pub facts: Vec<QuantifierFreeFact>,
}

impl ListSet {
    pub fn new(list: Vec<Obj>) -> Self {
        Self::new_with_source_occurrence_id(list, None)
    }

    pub fn new_with_source_occurrence_id(
        list: Vec<Obj>,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
    ) -> Self {
        ListSet {
            list: list.into_iter().map(Box::new).collect(),
            source_occurrence_id,
        }
    }
}

impl SetBuilder {
    pub fn new(
        param_binding: SymbolBinding,
        param_set: Obj,
        facts: Vec<QuantifierFreeFact>,
    ) -> Result<Self, RuntimeError> {
        let set_builder = SetBuilder {
            param_binding,
            param_set: Box::new(param_set),
            facts,
        };
        check_set_builder_has_no_duplicate_set_builder_free_parameter(&set_builder)?;
        Ok(set_builder)
    }

    pub fn param_name(&self) -> &str {
        self.param_binding.name()
    }
}

impl PowerSet {
    pub fn new(set: Obj) -> Self {
        PowerSet { set: Box::new(set) }
    }
}
