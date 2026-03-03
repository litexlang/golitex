use std::fmt;
use crate::obj::Obj;
use crate::atom::Atom;
use crate::consts::{EQUAL, FACT_PREFIX, GREATER, GREATER_EQUAL, IS_FINITE_SET, IS_NONEMPTY_SET, IS_SET, LESS, LESS_EQUAL, NOT, IN, IS_CART, IS_TUPLE, SUBSET, SUPERSET, NOT_EQUAL};
use crate::helper::{braced_string, braced_vec_to_string};

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
    SubsetFact(SubsetFact),
    SupersetFact(SupersetFact),

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
    NotSubsetFact(NotSubsetFact),
    NotSupersetFact(NotSupersetFact),
}

pub struct SupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotSupersetFact {    
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct SubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotSubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsTupleFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsTupleFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsCartFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsCartFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct InFact {
    pub element: Obj,
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotInFact {
    pub element: Obj,
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NormalAtomicFact {
    pub predicate: Atom,
    pub body: Vec<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotNormalAtomicFact {
    pub predicate: Atom,
    pub body: Vec<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct EqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct LessFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotLessFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct GreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotGreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct LessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotLessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct GreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotGreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsSetFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsSetFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsNonemptySetFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsNonemptySetFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct IsFiniteSetFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct NotIsFiniteSetFact {
    pub set: Obj,
    pub line: u32,
    pub file_index: usize,
}

impl SubsetFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        SubsetFact { left, right, line, file_index }
    }
}

impl NotSubsetFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotSubsetFact { left, right, line, file_index }
    }
}

impl NormalAtomicFact {
    pub fn new(predicate: Atom, body: Vec<Obj>, line: u32, file_index: usize) -> Self {
        NormalAtomicFact { predicate, body, line, file_index }
    }
}

impl NotNormalAtomicFact {
    pub fn new(predicate: Atom, body: Vec<Obj>, line: u32, file_index: usize) -> Self {
        NotNormalAtomicFact { predicate, body, line, file_index }
    }
}

impl EqualFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        EqualFact { left, right, line, file_index }
    }
}

impl NotEqualFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotEqualFact { left, right, line, file_index }
    }
}

impl LessFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        LessFact { left, right, line, file_index }
    }
}

impl NotLessFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotLessFact { left, right, line, file_index }
    }
}

impl GreaterFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        GreaterFact { left, right, line, file_index }
    }
}

impl NotGreaterFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotGreaterFact { left, right, line, file_index }
    }
}

impl LessEqualFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        LessEqualFact { left, right, line, file_index }
    }
}

impl NotLessEqualFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotLessEqualFact { left, right, line, file_index }
    }
}

impl GreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        GreaterEqualFact { left, right, line, file_index }
    }
}

impl NotGreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotGreaterEqualFact { left, right, line, file_index }
    }
}

impl IsSetFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        IsSetFact { set, line, file_index }
    }
}

impl NotIsSetFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        NotIsSetFact { set, line, file_index }
    }
}

impl IsNonemptySetFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        IsNonemptySetFact { set, line, file_index }
    }
}

impl NotIsNonemptySetFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        NotIsNonemptySetFact { set, line, file_index }
    }
}

impl IsFiniteSetFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        IsFiniteSetFact { set, line, file_index }
    }
}

impl NotIsFiniteSetFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        NotIsFiniteSetFact { set, line, file_index }
    }
}

impl InFact {
    pub fn new(element: Obj, set: Obj, line: u32, file_index: usize) -> Self {
        InFact { element, set, line, file_index }
    }
}

impl NotInFact {
    pub fn new(element: Obj, set: Obj, line: u32, file_index: usize) -> Self {
        NotInFact { element, set, line, file_index }
    }
}


impl IsCartFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        IsCartFact { set, line, file_index }
    }
}

impl NotIsCartFact {
    pub fn new(set: Obj, line: u32, file_index: usize) -> Self {
        NotIsCartFact { set, line, file_index }
    }
}

impl IsTupleFact {
    pub fn new(tuple: Obj, line: u32, file_index: usize) -> Self {
        IsTupleFact { set: tuple, line, file_index }
    }
}

impl NotIsTupleFact {
    pub fn new(tuple: Obj, line: u32, file_index: usize) -> Self {
        NotIsTupleFact { set: tuple, line, file_index }
    }
}

impl SupersetFact {
    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        SupersetFact { left, right, line, file_index }
    }
}

impl NotSupersetFact {

    pub fn new(left: Obj, right: Obj, line: u32, file_index: usize) -> Self {
        NotSupersetFact { left, right, line, file_index }
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
            AtomicFact::SubsetFact(x) => write!(f, "{}", x),
            AtomicFact::NotSubsetFact(x) => write!(f, "{}", x),
            AtomicFact::SupersetFact(x) => write!(f, "{}", x),
            AtomicFact::NotSupersetFact(x) => write!(f, "{}", x),
        }
    }
}

/// 从 AtomicFact 取得 line 与 file_index
pub fn line_file(a: &AtomicFact) -> (u32, usize) {
    let line = match a {
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
        AtomicFact::SubsetFact(x) => x.line,
        AtomicFact::NotSubsetFact(x) => x.line,
        AtomicFact::SupersetFact(x) => x.line,
        AtomicFact::NotSupersetFact(x) => x.line,
    };
    let file_index = match a {
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
        AtomicFact::SubsetFact(x) => x.file_index,
        AtomicFact::NotSubsetFact(x) => x.file_index,
        AtomicFact::SupersetFact(x) => x.file_index,
        AtomicFact::NotSupersetFact(x) => x.file_index,
    };
    (line, file_index)
}

impl fmt::Display for SupersetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", self.left, FACT_PREFIX, SUPERSET, self.right)
    }
}

impl fmt::Display for NotSupersetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}{} {}", NOT, self.left, FACT_PREFIX, SUPERSET, self.right)
    }
}

impl fmt::Display for SubsetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", self.left, FACT_PREFIX, SUBSET, self.right)
    }
}

impl fmt::Display for NotSubsetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}{} {}", NOT, self.left, FACT_PREFIX, SUBSET, self.right)
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
    pub fn predicate_string(&self) -> String {
        match self {
            AtomicFact::NormalAtomicFact(x) => x.predicate.to_string(),
            AtomicFact::EqualFact(_) => EQUAL.to_string(),
            AtomicFact::LessFact(_) => LESS.to_string(),
            AtomicFact::GreaterFact(_) => GREATER.to_string(),
            AtomicFact::LessEqualFact(_) => LESS_EQUAL.to_string(),
            AtomicFact::GreaterEqualFact(_) => GREATER_EQUAL.to_string(),
            AtomicFact::IsSetFact(_) => IS_SET.to_string(),
            AtomicFact::IsNonemptySetFact(_) => IS_NONEMPTY_SET.to_string(),
            AtomicFact::IsFiniteSetFact(_) => IS_FINITE_SET.to_string(),
            AtomicFact::InFact(_) => IN.to_string(),
            AtomicFact::IsCartFact(_) => IS_CART.to_string(),
            AtomicFact::IsTupleFact(_) => IS_TUPLE.to_string(),
            AtomicFact::SubsetFact(_) => SUBSET.to_string(),
            AtomicFact::SupersetFact(_) => SUPERSET.to_string(),
            AtomicFact::NotNormalAtomicFact(x) => x.predicate.to_string(),
            AtomicFact::NotEqualFact(_) => EQUAL.to_string(),
            AtomicFact::NotLessFact(_) => LESS.to_string(),
            AtomicFact::NotGreaterFact(_) => GREATER.to_string(),
            AtomicFact::NotLessEqualFact(_) => LESS_EQUAL.to_string(),
            AtomicFact::NotGreaterEqualFact(_) => GREATER_EQUAL.to_string(),
            AtomicFact::NotIsSetFact(_) => IS_SET.to_string(),
            AtomicFact::NotIsNonemptySetFact(_) => IS_NONEMPTY_SET.to_string(),
            AtomicFact::NotIsFiniteSetFact(_) => IS_FINITE_SET.to_string(),
            AtomicFact::NotInFact(_) => IN.to_string(),
            AtomicFact::NotIsCartFact(_) => IS_CART.to_string(),
            AtomicFact::NotIsTupleFact(_) => IS_TUPLE.to_string(),
            AtomicFact::NotSubsetFact(_) => SUBSET.to_string(),
            AtomicFact::NotSupersetFact(_) => SUPERSET.to_string(),
        }
    }

    pub fn is_true(&self) -> bool {
        match self {
            AtomicFact::NormalAtomicFact(_) => true,
            AtomicFact::EqualFact(_) => true,
            AtomicFact::LessFact(_) => true,
            AtomicFact::GreaterFact(_) => true,
            AtomicFact::LessEqualFact(_) => true,
            AtomicFact::GreaterEqualFact(_) => true,
            AtomicFact::IsSetFact(_) => true,
            AtomicFact::IsNonemptySetFact(_) => true,
            AtomicFact::IsFiniteSetFact(_) => true,
            AtomicFact::InFact(_) => true,
            AtomicFact::IsCartFact(_) => true,
            AtomicFact::IsTupleFact(_) => true,
            AtomicFact::SubsetFact(_) => true,
            AtomicFact::SupersetFact(_) => true,
            AtomicFact::NotNormalAtomicFact(_) => false,
            AtomicFact::NotEqualFact(_) => false,
            AtomicFact::NotLessFact(_) => false,
            AtomicFact::NotGreaterFact(_) => false,
            AtomicFact::NotLessEqualFact(_) => false,
            AtomicFact::NotGreaterEqualFact(_) => false,
            AtomicFact::NotIsSetFact(_) => false,
            AtomicFact::NotIsNonemptySetFact(_) => false,
            AtomicFact::NotIsFiniteSetFact(_) => false,
            AtomicFact::NotInFact(_) => false,
            AtomicFact::NotIsCartFact(_) => false,
            AtomicFact::NotIsTupleFact(_) => false,
            AtomicFact::NotSubsetFact(_) => false,
            AtomicFact::NotSupersetFact(_) => false,
        }
    }

    pub fn key(&self) -> String {
        return self.predicate_string();
    }
}