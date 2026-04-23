use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ProductObj {
    pub param: String,
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub body: Box<Obj>,
}

impl ProductObj {
    pub fn new(param: String, start: Obj, end: Obj, body: Obj) -> Self {
        ProductObj {
            param,
            start: Box::new(start),
            end: Box::new(end),
            body: Box::new(body),
        }
    }
}

impl fmt::Display for ProductObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}{}{}{}{}{}{}{}{}{}{}",
            PRODUCT,
            LEFT_BRACE,
            self.param,
            COMMA,
            " ",
            self.start,
            COMMA,
            " ",
            self.end,
            COMMA,
            " ",
            self.body,
            RIGHT_BRACE,
        )
    }
}
