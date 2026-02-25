use std::fmt;
use crate::consts::FACT_PREFIX;
use crate::helper::braced_vec_to_string;
use crate::obj::box_Obj;
use crate::predicate::box_Predicate;

pub enum Stmt {
    Fact(PureSpecFact),
}

#[allow(non_camel_case_types)]
pub type box_Stmt = Box<Stmt>;

pub struct PureSpecFact {
    pub predicate: box_Predicate,
    pub body: Vec<box_Obj>,
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(fact) => write!(f, "{}", fact),
        }
    }
}

impl Stmt {
    pub fn box_fact(predicate: box_Predicate, body: Vec<box_Obj>) -> box_Stmt {
        Box::new(Stmt::Fact(PureSpecFact::new(predicate, body)))
    }
}

impl PureSpecFact {
    pub fn new(predicate: box_Predicate, body: Vec<box_Obj>) -> Self {
        PureSpecFact { predicate, body }
    }
}

impl fmt::Display for PureSpecFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, self.predicate, braced_vec_to_string(&self.body))
    }
}