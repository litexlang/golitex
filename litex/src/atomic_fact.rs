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

impl AtomicFact {
    pub fn box_normal_atomic_fact(predicate: Box<Atom>, body: Vec<Box<Obj>>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(predicate, body, line)))
    }
    pub fn box_equal_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::EqualFact(EqualFact::new(left, right, line)))
    }
    pub fn box_less_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::LessFact(LessFact::new(left, right, line)))
    }
    pub fn box_greater_fact(left: Box<Obj>, right: Box<Obj>) -> Box<AtomicFact> {
        Box::new(AtomicFact::GreaterFact(GreaterFact::new(left, right)))
    }
    pub fn box_less_equal_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::LessEqualFact(LessEqualFact::new(left, right, line)))
    }
    pub fn box_greater_equal_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(left, right, line)))
    }
    pub fn box_is_set_fact(set: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::IsSetFact(IsSetFact::new(set, line)))
    }
    pub fn box_is_nonempty_set_fact(set: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(set, line)))
    }
    pub fn box_is_finite_set_fact(set: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(set, line)))
    }
    pub fn box_not_normal_atomic_fact(predicate: Box<Atom>, body: Vec<Box<Obj>>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(predicate, body, line)))
    }
    pub fn box_not_equal_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotEqualFact(NotEqualFact::new(left, right, line)))
    }
    pub fn box_not_less_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotLessFact(NotLessFact::new(left, right, line)))
    }
    pub fn box_not_greater_fact(left: Box<Obj>, right: Box<Obj>) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotGreaterFact(NotGreaterFact::new(left, right)))
    }
    pub fn box_not_less_equal_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotLessEqualFact(NotLessEqualFact::new(left, right, line)))
    }
    pub fn box_not_greater_equal_fact(left: Box<Obj>, right: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(left, right, line)))
    }
    pub fn box_not_is_set_fact(set: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotIsSetFact(NotIsSetFact::new(set, line)))
    }
    pub fn box_not_is_nonempty_set_fact(set: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(set, line)))
    }
    pub fn box_not_is_finite_set_fact(set: Box<Obj>, line: u32) -> Box<AtomicFact> {
        Box::new(AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(set, line)))
    }
}