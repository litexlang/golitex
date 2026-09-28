//! Object indexing.

use crate::prelude::*;

#[derive(Clone)]
pub struct ObjAtIndex {
    pub obj: Box<Obj>,
    pub index: Box<Obj>,
}

impl ObjAtIndex {
    pub fn new(obj: Obj, index: Obj) -> Self {
        ObjAtIndex {
            obj: Box::new(obj),
            index: Box::new(index),
        }
    }
}
