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
    pub line: u32,
}

pub struct NotNormalAtomicFact {
    pub predicate: Box<Atom>,
    pub body: Vec<Box<Obj>>,
    pub line: u32,
}

pub struct EqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
}

pub struct NotEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
}

pub struct LessFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
}

pub struct NotLessFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
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
    pub line: u32,
}

pub struct NotLessEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
}

pub struct GreaterEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
}

pub struct NotGreaterEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
}

pub struct IsSetFact {
    pub set: Box<Obj>,
    pub line: u32,
}

pub struct NotIsSetFact {
    pub set: Box<Obj>,
    pub line: u32,
}

pub struct IsNonemptySetFact {
    pub set: Box<Obj>,
    pub line: u32,
}

pub struct NotIsNonemptySetFact {
    pub set: Box<Obj>,
    pub line: u32,
}

pub struct IsFiniteSetFact {
    pub set: Box<Obj>,
    pub line: u32,
}

pub struct NotIsFiniteSetFact {
    pub set: Box<Obj>,
    pub line: u32,
}

impl NormalAtomicFact {
    pub fn new(predicate: Box<Atom>, body: Vec<Box<Obj>>, line: u32) -> Self {
        NormalAtomicFact { predicate, body, line }
    }
}

impl NotNormalAtomicFact {
    pub fn new(predicate: Box<Atom>, body: Vec<Box<Obj>>, line: u32) -> Self {
        NotNormalAtomicFact { predicate, body, line }
    }
}

impl EqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        EqualFact { left, right, line }
    }
}

impl NotEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        NotEqualFact { left, right, line }
    }
}

impl LessFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        LessFact { left, right, line }
    }
}

impl NotLessFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        NotLessFact { left, right, line }
    }
}

impl GreaterFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>) -> Self {
        GreaterFact { left, right }
    }
}

impl NotGreaterFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>) -> Self {
        NotGreaterFact { left, right }
    }
}

impl LessEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        LessEqualFact { left, right, line }
    }
}

impl NotLessEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        NotLessEqualFact { left, right, line }
    }
}

impl GreaterEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        GreaterEqualFact { left, right, line }
    }
}

impl NotGreaterEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        NotGreaterEqualFact { left, right, line }
    }
}

impl IsSetFact {
    pub fn new(set: Box<Obj>, line: u32) -> Self {
        IsSetFact { set, line }
    }
}

impl NotIsSetFact {
    pub fn new(set: Box<Obj>, line: u32) -> Self {
        NotIsSetFact { set, line }
    }
}

impl IsNonemptySetFact {
    pub fn new(set: Box<Obj>, line: u32) -> Self {
        IsNonemptySetFact { set, line }
    }
}

impl NotIsNonemptySetFact {
    pub fn new(set: Box<Obj>, line: u32) -> Self {
        NotIsNonemptySetFact { set, line }
    }
}

impl IsFiniteSetFact {
    pub fn new(set: Box<Obj>, line: u32) -> Self {
        IsFiniteSetFact { set, line }
    }
}

impl NotIsFiniteSetFact {
    pub fn new(set: Box<Obj>, line: u32) -> Self {
        NotIsFiniteSetFact { set, line }
    }
}
