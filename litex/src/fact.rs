use crate::atom::Atom;
use crate::obj::Obj;
use crate::atomic_fact::{AtomicFact};
use crate::exist_fact::{ExistFact, NotExistFact};
use crate::or_fact::OrFact;

enum Fact {
    AtomicFact(Box<AtomicFact>),
    ExistFact(Box<ExistFact>),
    OrFact(OrFact),
    ForallFact(ForallFact),
    ChainFact(ChainFact),
    ForallFactWithIff(ForallFactWithIff),
}

