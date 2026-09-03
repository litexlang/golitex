//! Named function application objects.

use crate::prelude::*;

#[derive(Clone)]
pub struct FnObj {
    pub head: Box<FnObjHead>,
    pub body: Vec<Vec<Box<Obj>>>,
}

impl FnObj {
    pub fn new(head: FnObjHead, body: Vec<Vec<Box<Obj>>>) -> Self {
        FnObj {
            head: Box::new(head),
            body,
        }
    }

    pub fn prefix_obj(&self, number_of_body_groups_to_keep: usize) -> Obj {
        if number_of_body_groups_to_keep == 0 {
            return self.head.as_ref().clone().into();
        }

        FnObj::new(
            self.head.as_ref().clone(),
            self.body[..number_of_body_groups_to_keep].to_vec(),
        )
        .into()
    }
}
