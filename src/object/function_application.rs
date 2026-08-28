//! Named function application objects.

use crate::prelude::*;

#[derive(Clone)]
pub struct FnObj {
    pub head: Box<FnObjHead>,
    pub body: Vec<Vec<Box<Obj>>>,
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
}

impl FnObj {
    pub fn new(head: FnObjHead, body: Vec<Vec<Box<Obj>>>) -> Self {
        FnObj {
            head: Box::new(head),
            body,
            source_occurrence_id: None,
        }
    }

    pub fn new_with_source_occurrence_id(
        head: FnObjHead,
        body: Vec<Vec<Box<Obj>>>,
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
    ) -> Self {
        FnObj {
            head: Box::new(head),
            body,
            source_occurrence_id,
        }
    }

    pub fn prefix_obj(&self, number_of_body_groups_to_keep: usize) -> Obj {
        if number_of_body_groups_to_keep == 0 {
            return self.head.as_ref().clone().into();
        }

        FnObj::new_with_source_occurrence_id(
            self.head.as_ref().clone(),
            self.body[..number_of_body_groups_to_keep].to_vec(),
            self.source_occurrence_id,
        )
        .into()
    }
}
