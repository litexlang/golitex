use std::fmt;
use crate::obj::Obj;
use crate::atom::Atom;
use crate::consts::{EQUAL, FACT_PREFIX, GREATER, GREATER_EQUAL, IS_FINITE_SET, IS_NONEMPTY_SET, IS_SET, LESS, LESS_EQUAL, NOT, NOT_EQUAL, IN, IS_CART, IS_TUPLE};
use crate::helper::{braced_string, braced_vec_to_string, str_with_line_file};

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
    InFact(InFact),
    IsCartFact(IsCartFact),
    IsTupleFact(IsTupleFact),

    NotNormalAtomicFact(NotNormalAtomicFact),
    NotEqualFact(NotEqualFact),
    NotLessFact(NotLessFact),
    NotGreaterFact(NotGreaterFact),
    NotLessEqualFact(NotLessEqualFact),
    NotGreaterEqualFact(NotGreaterEqualFact),
    NotIsSetFact(NotIsSetFact),
    NotIsNonemptySetFact(NotIsNonemptySetFact),
    NotIsFiniteSetFact(NotIsFiniteSetFact),
    NotInFact(NotInFact),
    NotIsCartFact(NotIsCartFact),
    NotIsTupleFact(NotIsTupleFact),
}

pub struct IsTupleFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsTupleFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsCartFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsCartFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct InFact {
    pub element: Box<Obj>,
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotInFact {
    pub element: Box<Obj>,
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NormalAtomicFact {
    pub predicate: Box<Atom>,
    pub body: Vec<Box<Obj>>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotNormalAtomicFact {
    pub predicate: Box<Atom>,
    pub body: Vec<Box<Obj>>,
    pub line: u32,
    pub file_index: usize,
}

pub struct EqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct LessFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotLessFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct GreaterFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotGreaterFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct LessEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotLessEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct GreaterEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotGreaterEqualFact {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsSetFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsSetFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsNonemptySetFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsNonemptySetFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsFiniteSetFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsFiniteSetFact {
    pub set: Box<Obj>,
    pub line: u32,
    pub file_index: usize,
}

impl NormalAtomicFact {
    pub fn new(predicate: Box<Atom>, body: Vec<Box<Obj>>, line: u32, file_index: usize) -> Self {
        NormalAtomicFact { predicate, body, line, file_index }
    }
}

impl NotNormalAtomicFact {
    pub fn new(predicate: Box<Atom>, body: Vec<Box<Obj>>, line: u32, file_index: usize) -> Self {
        NotNormalAtomicFact { predicate, body, line, file_index }
    }
}

impl EqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        EqualFact { left, right, line, file_index }
    }
}

impl NotEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotEqualFact { left, right, line, file_index }
    }
}

impl LessFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        LessFact { left, right, line, file_index }
    }
}

impl NotLessFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotLessFact { left, right, line, file_index }
    }
}

impl GreaterFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        GreaterFact { left, right, line, file_index }
    }
}

impl NotGreaterFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotGreaterFact { left, right, line, file_index }
    }
}

impl LessEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        LessEqualFact { left, right, line, file_index }
    }
}

impl NotLessEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotLessEqualFact { left, right, line, file_index }
    }
}

impl GreaterEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        GreaterEqualFact { left, right, line, file_index }
    }
}

impl NotGreaterEqualFact {
    pub fn new(left: Box<Obj>, right: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotGreaterEqualFact { left, right, line, file_index }
    }
}

impl IsSetFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        IsSetFact { set, line, file_index }
    }
}

impl NotIsSetFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotIsSetFact { set, line, file_index }
    }
}

impl IsNonemptySetFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        IsNonemptySetFact { set, line, file_index }
    }
}

impl NotIsNonemptySetFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotIsNonemptySetFact { set, line, file_index }
    }
}

impl IsFiniteSetFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        IsFiniteSetFact { set, line, file_index }
    }
}

impl NotIsFiniteSetFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotIsFiniteSetFact { set, line, file_index }
    }
}

impl InFact {
    pub fn new(element: Box<Obj>, set: Box<Obj>, line: u32, file_index: usize) -> Self {
        InFact { element, set, line, file_index }
    }
}

impl NotInFact {
    pub fn new(element: Box<Obj>, set: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotInFact { element, set, line, file_index }
    }
}


impl IsCartFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        IsCartFact { set, line, file_index }
    }
}

impl NotIsCartFact {
    pub fn new(set: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotIsCartFact { set, line, file_index }
    }
}

impl IsTupleFact {
    pub fn new(tuple: Box<Obj>, line: u32, file_index: usize) -> Self {
        IsTupleFact { set: tuple, line, file_index }
    }
}

impl NotIsTupleFact {
    pub fn new(tuple: Box<Obj>, line: u32, file_index: usize) -> Self {
        NotIsTupleFact { set: tuple, line, file_index }
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
            AtomicFact::InFact(x) => write!(f, "{}", x),
            AtomicFact::NotInFact(x) => write!(f, "{}", x),
            AtomicFact::IsCartFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsCartFact(x) => write!(f, "{}", x),
            AtomicFact::IsTupleFact(x) => write!(f, "{}", x),
            AtomicFact::NotIsTupleFact(x) => write!(f, "{}", x),
        }
    }
}

impl AtomicFact {
    pub fn file_index(&self) -> usize {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.file_index,
            AtomicFact::EqualFact(x) => x.file_index,
            AtomicFact::LessFact(x) => x.file_index,
            AtomicFact::GreaterFact(x) => x.file_index,
            AtomicFact::LessEqualFact(x) => x.file_index,
            AtomicFact::GreaterEqualFact(x) => x.file_index,
            AtomicFact::IsSetFact(x) => x.file_index,
            AtomicFact::IsNonemptySetFact(x) => x.file_index,
            AtomicFact::IsFiniteSetFact(x) => x.file_index,
            AtomicFact::NotNormalAtomicFact(x) => x.file_index,
            AtomicFact::NotEqualFact(x) => x.file_index,
            AtomicFact::NotLessFact(x) => x.file_index,
            AtomicFact::NotGreaterFact(x) => x.file_index,
            AtomicFact::NotLessEqualFact(x) => x.file_index,
            AtomicFact::NotGreaterEqualFact(x) => x.file_index,
            AtomicFact::NotIsSetFact(x) => x.file_index,
            AtomicFact::NotIsNonemptySetFact(x) => x.file_index,
            AtomicFact::NotIsFiniteSetFact(x) => x.file_index,
            AtomicFact::InFact(x) => x.file_index,
            AtomicFact::NotInFact(x) => x.file_index,
            AtomicFact::IsCartFact(x) => x.file_index,
            AtomicFact::NotIsCartFact(x) => x.file_index,
            AtomicFact::IsTupleFact(x) => x.file_index,
            AtomicFact::NotIsTupleFact(x) => x.file_index,
        }
    }
}

impl fmt::Display for InFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", self.element, FACT_PREFIX, IN, self.set)
    }
}

impl fmt::Display for NotInFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}{} {}", NOT, self.element, FACT_PREFIX, IN, self.set)
    }
}

impl fmt::Display for IsCartFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_CART, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsCartFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", NOT, FACT_PREFIX, IS_CART, braced_string(&self.set))
    }
}

impl fmt::Display for IsTupleFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_TUPLE, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsTupleFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", NOT, FACT_PREFIX, IS_TUPLE, braced_string(&self.set))
    }
}

impl fmt::Display for NormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, self.predicate, braced_vec_to_string(&self.body))
    }
}

impl fmt::Display for NotNormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", NOT, FACT_PREFIX, self.predicate, braced_vec_to_string(&self.body))
    }
}

impl fmt::Display for EqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, EQUAL, self.right)
    }
}

impl fmt::Display for NotEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, NOT_EQUAL, self.right)
    }
}

impl fmt::Display for LessFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, LESS, self.right)
    }
}

impl fmt::Display for NotLessFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", NOT, self.left, LESS, self.right)
    }
}

impl fmt::Display for GreaterFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, GREATER, self.right)
    }
}

impl fmt::Display for NotGreaterFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", NOT, self.left, GREATER, self.right)
    }
}

impl fmt::Display for LessEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, LESS_EQUAL, self.right)
    }
}

impl fmt::Display for NotLessEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", NOT, self.left, LESS_EQUAL, self.right)
    }
}

impl fmt::Display for GreaterEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, GREATER_EQUAL, self.right)
    }
}

impl fmt::Display for NotGreaterEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", NOT, self.left, GREATER_EQUAL, self.right)
    }
}

impl fmt::Display for IsSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_SET, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", NOT, FACT_PREFIX, IS_SET, braced_string(&self.set))
    }
}

impl fmt::Display for IsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_NONEMPTY_SET, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", NOT, FACT_PREFIX, IS_NONEMPTY_SET, braced_string(&self.set))
    }
}

impl fmt::Display for IsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_FINITE_SET, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", NOT, FACT_PREFIX, IS_FINITE_SET, braced_string(&self.set))
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
            AtomicFact::InFact(x) => x.line,
            AtomicFact::NotInFact(x) => x.line,
            AtomicFact::IsCartFact(x) => x.line,
            AtomicFact::NotIsCartFact(x) => x.line,
            AtomicFact::IsTupleFact(x) => x.line,
            AtomicFact::NotIsTupleFact(x) => x.line,
        }
    }

    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line(), self.file_index());
    }
}