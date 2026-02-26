use crate::obj::Obj;
use crate::atom::Atom;

pub struct ChainFact {
    pub objs: Vec<Box<Obj>>,
    pub prop_names: Vec<Box<Atom>>,
}

impl ChainFact {
    pub fn new(objs: Vec<Box<Obj>>, prop_names: Vec<Box<Atom>>) -> Self {
        ChainFact { objs, prop_names }
    }
}