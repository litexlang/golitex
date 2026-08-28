//! Big and indexed set unions and intersections.

use crate::prelude::*;

#[derive(Clone)]
pub struct BigUnion {
    pub left: Box<Obj>,
}

#[derive(Clone)]
pub struct BigIntersect {
    pub left: Box<Obj>,
}

/// The union of the set-valued family `family_fn` over `index_set`, with
/// `ambient_set` fixing the result carrier and the empty-family semantics.
#[derive(Clone)]
pub struct IndexUnion {
    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

/// The intersection of the set-valued family `family_fn` over `index_set`,
/// equal to `ambient_set` when the index set is empty.
#[derive(Clone)]
pub struct IndexIntersect {
    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

impl BigUnion {
    pub fn new(left: Obj) -> Self {
        BigUnion {
            left: Box::new(left),
        }
    }
}

impl BigIntersect {
    pub fn new(left: Obj) -> Self {
        BigIntersect {
            left: Box::new(left),
        }
    }
}

impl IndexUnion {
    pub fn new(index_set: Obj, ambient_set: Obj, family_fn: Obj) -> Self {
        IndexUnion {
            index_set: Box::new(index_set),
            ambient_set: Box::new(ambient_set),
            family_fn: Box::new(family_fn),
        }
    }
}

impl IndexIntersect {
    pub fn new(index_set: Obj, ambient_set: Obj, family_fn: Obj) -> Self {
        IndexIntersect {
            index_set: Box::new(index_set),
            ambient_set: Box::new(ambient_set),
            family_fn: Box::new(family_fn),
        }
    }
}
