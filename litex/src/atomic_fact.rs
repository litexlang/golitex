use crate::obj::Obj;
use crate::atom::Atom;

pub enum AtomicFact {
    NormalAtomicFact(NormalAtomicFact),
    EqualFact(EqualFact),
    LessFact(LessFact),
    GreaterFact(GreaterFact),
    LessEqualFact(LessEqualFact),
    GreaterEqualFact(GreaterEqualFact),
    IsSetFact(IsSetFact),
    IsNonemptySetFact(IsNonemptySetFact),
    IsFiniteSetFact(IsFiniteSetFact),

    NotNormalAtomicFact(NotNormalAtomicFact),
    NotEqualFact(NotEqualFact),
    NotLessFact(NotLessFact),
    NotGreaterFact(NotGreaterFact),
    NotLessEqualFact(NotLessEqualFact),
    NotGreaterEqualFact(NotGreaterEqualFact),
    NotIsSetFact(NotIsSetFact),
    NotIsNonemptySetFact(NotIsNonemptySetFact),
    NotIsFiniteSetFact(NotIsFiniteSetFact),
}

pub struct NormalAtomicFact {
    pub predicate: Box<Atom>,
    pub body: Vec<Box<Obj>>,
}

pub struct NotNormalAtomicFact {
    pub predicate: Box<Atom>,
    pub body: Vec<Box<Obj>>,
}

pub struct EqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct NotEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct LessFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct NotLessFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct GreaterFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct NotGreaterFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct LessEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct NotLessEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct GreaterEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct NotGreaterEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

pub struct IsSetFact {
    pub set: Box<Obj>,
}

pub struct NotIsSetFact {
    pub set: Box<Obj>,
}

pub struct IsNonemptySetFact {
    pub set: Box<Obj>,
}

pub struct NotIsNonemptySetFact {
    pub set: Box<Obj>,
}

pub struct IsFiniteSetFact {
    pub set: Box<Obj>,
}

pub struct NotIsFiniteSetFact {
    pub set: Box<Obj>,
}

