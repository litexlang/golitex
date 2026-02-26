use std::fmt;
use crate::obj::Obj;
use crate::atom::Atom;
use crate::consts::FACT_PREFIX;

pub struct ChainFact {
    pub objs: Vec<Box<Obj>>,
    pub prop_names: Vec<Box<Atom>>,
    pub line: u32,
}

impl ChainFact {
    pub fn new(objs: Vec<Box<Obj>>, prop_names: Vec<Box<Atom>>, line: u32) -> Self {
        ChainFact { objs, prop_names, line }
    }
}

impl fmt::Display for ChainFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, obj) in self.objs.iter().enumerate() {
            write!(f, "{}", obj)?;
            if i < self.objs.len() - 1 {
                write!(f, "{}{}", FACT_PREFIX, self.prop_names[i])?;
            }
        }
        Ok(())
    }
}

impl ChainFact {
    pub fn line(&self) -> u32 {
        self.line
    }
}