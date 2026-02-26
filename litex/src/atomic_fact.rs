use std::fmt;
use crate::obj::Obj;
use crate::atom::Atom;
use crate::helper::{braced_vec_to_string, braced_string, braced_two_strings};

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
    pub line: u32,
}

pub struct NotGreaterFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
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
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        GreaterFact { left, right, line }
    }
}

impl NotGreaterFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32) -> Self {
        NotGreaterFact { left, right, line }
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

impl fmt::Display for AtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AtomicFact::NormalAtomicFact(x) => write!(f, "{}", x),
            AtomicFact::EqualFact(x) => write!(f, "{}", x),
            AtomicFact::LessFact(x) => write!(f, "{}", x),
            AtomicFact::GreaterFact(x) => write!(f, "{}", x),
            AtomicFact::LessEqualFact(x) => write!(f, "{}", x),
            AtomicFact::GreaterEqualFact(x) => write!(f, "{}", x),
            AtomicFact::IsSetFact(x) => write!(f, "{}", x),
            AtomicFact::IsNonemptySetFact(x) => write!(f, "{}", x),
            AtomicFact::IsFiniteSetFact(x) => write!(f, "{}", x),
            AtomicFact::NotNormalAtomicFact(x) => write!(f, "{}", x),
            AtomicFact::NotEqualFact(x) => write!(f, "{}", x),
            AtomicFact::NotLessFact(x) => write!(f, "{}", x),
            AtomicFact::NotGreaterFact(x) => write!(f, "{}", x),
            AtomicFact::NotLessEqualFact(x) => write!(f, "{}", x),
            AtomicFact::NotGreaterEqualFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsSetFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsNonemptySetFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsFiniteSetFact(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for NormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.predicate, braced_vec_to_string(&self.body))
    }
}

impl fmt::Display for NotNormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_{}{}", self.predicate, braced_vec_to_string(&self.body))
    }
}

impl fmt::Display for EqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "eq{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for NotEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "neq{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for LessFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "less{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for NotLessFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_less{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for GreaterFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "greater{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for NotGreaterFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_greater{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for LessEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "less_eq{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for NotLessEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_less_eq{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for GreaterEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "greater_eq{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for NotGreaterEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_greater_eq{}", braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for IsSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "is_set{}", braced_string(&self.set))
    }
}

impl fmt::Display for NotIsSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_is_set{}", braced_string(&self.set))
    }
}

impl fmt::Display for IsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "is_nonempty_set{}", braced_string(&self.set))
    }
}

impl fmt::Display for NotIsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_is_nonempty_set{}", braced_string(&self.set))
    }
}

impl fmt::Display for IsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "is_finite_set{}", braced_string(&self.set))
    }
}

impl fmt::Display for NotIsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "not_is_finite_set{}", braced_string(&self.set))
    }
}

impl AtomicFact {
    pub fn line(&self) -> u32 {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.line,
            AtomicFact::EqualFact(x) => x.line,
            AtomicFact::LessFact(x) => x.line,
            AtomicFact::GreaterFact(x) => x.line,
            AtomicFact::LessEqualFact(x) => x.line,
            AtomicFact::GreaterEqualFact(x) => x.line,
            AtomicFact::IsSetFact(x) => x.line,
            AtomicFact::IsNonemptySetFact(x) => x.line,
            AtomicFact::IsFiniteSetFact(x) => x.line,
            AtomicFact::NotNormalAtomicFact(x) => x.line,
            AtomicFact::NotEqualFact(x) => x.line,
            AtomicFact::NotLessFact(x) => x.line,
            AtomicFact::NotGreaterFact(x) => x.line,
            AtomicFact::NotLessEqualFact(x) => x.line,
            AtomicFact::NotGreaterEqualFact(x) => x.line,
            AtomicFact::NotIsSetFact(x) => x.line,
            AtomicFact::NotIsNonemptySetFact(x) => x.line,
            AtomicFact::NotIsFiniteSetFact(x) => x.line,
        }
    }
}