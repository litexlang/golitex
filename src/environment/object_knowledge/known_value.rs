//! Canonical simplified value retained for one object.

use crate::prelude::*;

/// A canonical simplified value retained as reusable object knowledge.
#[derive(Clone)]
pub enum KnownObjValue {
    SimplifiedNumber(Number), // when a = 1.0, store a = 1
    SimplifiedFraction(Div),  // when a = 1/3, store a = 1/3
}
