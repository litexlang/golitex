use crate::prelude::*;
use std::fmt;

/// Parsed `sum(index, start, end, body)` — `index` is bound only in `body` as [`SumFreeParamObj`].
#[derive(Clone)]
pub struct SumObj {
    pub param: String,
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub body: Box<Obj>,
}

impl SumObj {
    pub fn new(param: String, start: Obj, end: Obj, body: Obj) -> Self {
        SumObj {
            param,
            start: Box::new(start),
            end: Box::new(end),
            body: Box::new(body),
        }
    }
}

impl fmt::Display for SumObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}{}{}{}{}{}{}{}",
            SUM,
            LEFT_BRACE,
            self.param,
            COMMA,
            self.start,
            COMMA,
            self.end,
            COMMA,
            self.body,
            RIGHT_BRACE,
        )
    }
}
