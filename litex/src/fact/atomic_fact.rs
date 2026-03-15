use std::fmt;
use crate::obj::Obj;
use crate::obj::IdentifierOrIdentifierWithMod;
use crate::common::keywords::{EQUAL, FACT_PREFIX, GREATER, GREATER_EQUAL, IS_FINITE_SET, IS_NONEMPTY_SET, IS_SET, LESS, LESS_EQUAL, NOT, IN, IS_CART, IS_TUPLE, SUBSET, SUPERSET, NOT_EQUAL};
use crate::common::helper::{braced_string, braced_vec_to_string};
use crate::error::NewAtomicFactError;

#[derive(Clone)]
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

#[derive(Clone)]
pub struct SupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotSupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct SubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotSubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct IsTupleFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotIsTupleFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct IsCartFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotIsCartFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct InFact {
    pub element: Obj,
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotInFact {
    pub element: Obj,
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NormalAtomicFact {
    pub predicate: IdentifierOrIdentifierWithMod,
    pub body: Vec<Obj>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotNormalAtomicFact {
    pub predicate: IdentifierOrIdentifierWithMod,
    pub body: Vec<Obj>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct EqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct LessFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotLessFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct GreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotGreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct LessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotLessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct GreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotGreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct IsSetFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotIsSetFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct IsNonemptySetFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotIsNonemptySetFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct IsFiniteSetFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct NotIsFiniteSetFact {
    pub set: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

impl SubsetFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        SubsetFact { left, right, line_file_index }
    }
}

impl NotSubsetFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotSubsetFact { left, right, line_file_index }
    }
}

impl NormalAtomicFact {
    pub fn new(predicate: IdentifierOrIdentifierWithMod, body: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Self {
        NormalAtomicFact { predicate, body, line_file_index }
    }
}

impl NotNormalAtomicFact {
    pub fn new(predicate: IdentifierOrIdentifierWithMod, body: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Self {
        NotNormalAtomicFact { predicate, body, line_file_index }
    }
}

impl EqualFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        EqualFact { left, right, line_file_index }
    }
}

impl NotEqualFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotEqualFact { left, right, line_file_index }
    }
}

impl LessFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        LessFact { left, right, line_file_index }
    }
}

impl NotLessFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotLessFact { left, right, line_file_index }
    }
}

impl GreaterFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        GreaterFact { left, right, line_file_index }
    }
}

impl NotGreaterFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotGreaterFact { left, right, line_file_index }
    }
}

impl LessEqualFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        LessEqualFact { left, right, line_file_index }
    }
}

impl NotLessEqualFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotLessEqualFact { left, right, line_file_index }
    }
}

impl GreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        GreaterEqualFact { left, right, line_file_index }
    }
}

impl NotGreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotGreaterEqualFact { left, right, line_file_index }
    }
}

impl IsSetFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        IsSetFact { set, line_file_index }
    }
}

impl NotIsSetFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotIsSetFact { set, line_file_index }
    }
}

impl IsNonemptySetFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        IsNonemptySetFact { set, line_file_index }
    }
}

impl NotIsNonemptySetFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotIsNonemptySetFact { set, line_file_index }
    }
}

impl IsFiniteSetFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        IsFiniteSetFact { set, line_file_index }
    }
}

impl NotIsFiniteSetFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotIsFiniteSetFact { set, line_file_index }
    }
}

impl InFact {
    pub fn new(element: Obj, set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        InFact { element, set, line_file_index }
    }
}

impl NotInFact {
    pub fn new(element: Obj, set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotInFact { element, set, line_file_index }
    }
}


impl IsCartFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        IsCartFact { set, line_file_index }
    }
}

impl NotIsCartFact {
    pub fn new(set: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotIsCartFact { set, line_file_index }
    }
}

impl IsTupleFact {
    pub fn new(tuple: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        IsTupleFact { set: tuple, line_file_index }
    }
}

impl NotIsTupleFact {
    pub fn new(tuple: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotIsTupleFact { set: tuple, line_file_index }
    }
}

impl SupersetFact {
    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        SupersetFact { left, right, line_file_index }
    }
}

impl NotSupersetFact {

    pub fn new(left: Obj, right: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        NotSupersetFact { left, right, line_file_index }
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

pub fn line_file(a: &AtomicFact) -> Option<(usize, usize)> {
    match a {
        AtomicFact::NormalAtomicFact(x) => x.line_file_index,
        AtomicFact::EqualFact(x) => x.line_file_index,
        AtomicFact::LessFact(x) => x.line_file_index,
        AtomicFact::GreaterFact(x) => x.line_file_index,
        AtomicFact::LessEqualFact(x) => x.line_file_index,
        AtomicFact::GreaterEqualFact(x) => x.line_file_index,
        AtomicFact::IsSetFact(x) => x.line_file_index,
        AtomicFact::IsNonemptySetFact(x) => x.line_file_index,
        AtomicFact::IsFiniteSetFact(x) => x.line_file_index,
        AtomicFact::NotNormalAtomicFact(x) => x.line_file_index,
        AtomicFact::NotEqualFact(x) => x.line_file_index,
        AtomicFact::NotLessFact(x) => x.line_file_index,
        AtomicFact::NotGreaterFact(x) => x.line_file_index,
        AtomicFact::NotLessEqualFact(x) => x.line_file_index,
        AtomicFact::NotGreaterEqualFact(x) => x.line_file_index,
        AtomicFact::NotIsSetFact(x) => x.line_file_index,
        AtomicFact::NotIsNonemptySetFact(x) => x.line_file_index,
        AtomicFact::NotIsFiniteSetFact(x) => x.line_file_index,
        AtomicFact::InFact(x) => x.line_file_index,
        AtomicFact::NotInFact(x) => x.line_file_index,
        AtomicFact::IsCartFact(x) => x.line_file_index,
        AtomicFact::NotIsCartFact(x) => x.line_file_index,
        AtomicFact::IsTupleFact(x) => x.line_file_index,
        AtomicFact::NotIsTupleFact(x) => x.line_file_index,
        AtomicFact::SubsetFact(x) => x.line_file_index,
        AtomicFact::NotSubsetFact(x) => x.line_file_index,
        AtomicFact::SupersetFact(x) => x.line_file_index,
        AtomicFact::NotSupersetFact(x) => x.line_file_index,
    }
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
        if self.body.len() == 2 {
            write!(f, "{} {}{} {}", self.body[0], FACT_PREFIX, self.predicate, self.body[1])
        } else {
            write!(f, "{}{}{}", FACT_PREFIX, self.predicate, braced_vec_to_string(&self.body))
        }
    }
}

impl fmt::Display for NotNormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.body.len() == 2 {
            write!(f, "{} {} {}{} {}", NOT, self.body[0], FACT_PREFIX, self.predicate, self.body[1])
        } else {
            write!(f, "{} {}{}{}", NOT, FACT_PREFIX, self.predicate, braced_vec_to_string(&self.body))
        }
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
    fn predicate_string(&self) -> String {
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


impl AtomicFact {
    pub fn to_atomic_fact(prop_name: IdentifierOrIdentifierWithMod, is_true: bool, args: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Result<AtomicFact, NewAtomicFactError> {
        let prop_name_as_string = prop_name.to_string();
        match prop_name_as_string.as_str() {
            EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", EQUAL, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::EqualFact(EqualFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::NotEqualFact(NotEqualFact::new(a0, a1, line_file_index)))
                }
            }
            NOT_EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", NOT_EQUAL, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::NotEqualFact(NotEqualFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::EqualFact(EqualFact::new(a0, a1, line_file_index)))
                }
            }
            LESS => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", LESS, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::LessFact(LessFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::GreaterFact(GreaterFact::new(a0, a1, line_file_index)))
                }
            }
            GREATER => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", GREATER, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::GreaterFact(GreaterFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::LessFact(LessFact::new(a0, a1, line_file_index)))
                }
            }
            LESS_EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", LESS_EQUAL, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::LessEqualFact(LessEqualFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(a0, a1, line_file_index)))
                }
            }
            GREATER_EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", GREATER_EQUAL, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::LessEqualFact(LessEqualFact::new(a0, a1, line_file_index)))
                }
            }
            IS_SET => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_SET, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsSetFact(IsSetFact::new(a0, line_file_index)))
                } else {
                    Ok(AtomicFact::NotIsSetFact(NotIsSetFact::new(a0, line_file_index)))
                }
            }
            IS_NONEMPTY_SET => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_NONEMPTY_SET, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(a0, line_file_index)))
                } else {
                    Ok(AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(a0, line_file_index)))
                }
            }
            IS_FINITE_SET => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_FINITE_SET, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(a0, line_file_index)))
                } else {
                    Ok(AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(a0, line_file_index)))
                }
            }
            IN => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", IN, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::InFact(InFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::NotInFact(NotInFact::new(a0, a1, line_file_index)))
                }
            }
            IS_CART => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_CART, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsCartFact(IsCartFact::new(a0, line_file_index)))
                } else {
                    Ok(AtomicFact::NotIsCartFact(NotIsCartFact::new(a0, line_file_index)))
                }
            }
            IS_TUPLE => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_TUPLE, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsTupleFact(IsTupleFact::new(a0, line_file_index)))
                } else {
                    Ok(AtomicFact::NotIsTupleFact(NotIsTupleFact::new(a0, line_file_index)))
                }
            }
            SUBSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUBSET, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::SubsetFact(SubsetFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::NotSubsetFact(NotSubsetFact::new(a0, a1, line_file_index)))
                }
            }
            SUPERSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUPERSET, args.len());
                    return Err(NewAtomicFactError::new(msg));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::SupersetFact(SupersetFact::new(a0, a1, line_file_index)))
                } else {
                    Ok(AtomicFact::NotSupersetFact(NotSupersetFact::new(a0, a1, line_file_index)))
                }
            }
            _ => {
                if is_true {
                    Ok(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(prop_name, args, line_file_index)))
                } else {
                    Ok(AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(prop_name, args, line_file_index)))
                }
            }
        }
    }
}

impl AtomicFact {
    pub fn args(&self) -> Vec<Obj> {
        match self {
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => normal_atomic_fact.body.clone(),
            AtomicFact::EqualFact(equal_fact) => vec![equal_fact.left.clone(), equal_fact.right.clone()],
            AtomicFact::LessFact(less_fact) => vec![less_fact.left.clone(), less_fact.right.clone()],
            AtomicFact::GreaterFact(greater_fact) => vec![greater_fact.left.clone(), greater_fact.right.clone()],
            AtomicFact::LessEqualFact(less_equal_fact) => vec![less_equal_fact.left.clone(), less_equal_fact.right.clone()],
            AtomicFact::GreaterEqualFact(greater_equal_fact) => vec![greater_equal_fact.left.clone(), greater_equal_fact.right.clone()],
            AtomicFact::IsSetFact(is_set_fact) => vec![is_set_fact.set.clone()],
            AtomicFact::IsNonemptySetFact(is_nonempty_set_fact) => vec![is_nonempty_set_fact.set.clone()],
            AtomicFact::IsFiniteSetFact(is_finite_set_fact) => vec![is_finite_set_fact.set.clone()],
            AtomicFact::InFact(in_fact) => vec![in_fact.element.clone(), in_fact.set.clone()],
            AtomicFact::IsCartFact(is_cart_fact) => vec![is_cart_fact.set.clone()],
            AtomicFact::IsTupleFact(is_tuple_fact) => vec![is_tuple_fact.set.clone()],
            AtomicFact::SubsetFact(subset_fact) => vec![subset_fact.left.clone(), subset_fact.right.clone()],
            AtomicFact::SupersetFact(superset_fact) => vec![superset_fact.left.clone(), superset_fact.right.clone()],
            AtomicFact::NotNormalAtomicFact(not_normal_atomic_fact) => not_normal_atomic_fact.body.clone(),
            AtomicFact::NotEqualFact(not_equal_fact) => vec![not_equal_fact.left.clone(), not_equal_fact.right.clone()],
            AtomicFact::NotLessFact(not_less_fact) => vec![not_less_fact.left.clone(), not_less_fact.right.clone()],
            AtomicFact::NotGreaterFact(not_greater_fact) => vec![not_greater_fact.left.clone(), not_greater_fact.right.clone()],
            AtomicFact::NotLessEqualFact(not_less_equal_fact) => vec![not_less_equal_fact.left.clone(), not_less_equal_fact.right.clone()],
            AtomicFact::NotGreaterEqualFact(not_greater_equal_fact) => vec![not_greater_equal_fact.left.clone(), not_greater_equal_fact.right.clone()],
            AtomicFact::NotIsSetFact(not_is_set_fact) => vec![not_is_set_fact.set.clone()],
            AtomicFact::NotIsNonemptySetFact(not_is_nonempty_set_fact) => vec![not_is_nonempty_set_fact.set.clone()],
            AtomicFact::NotIsFiniteSetFact(not_is_finite_set_fact) => vec![not_is_finite_set_fact.set.clone()],
            AtomicFact::NotInFact(not_in_fact) => vec![not_in_fact.element.clone(), not_in_fact.set.clone()],
            AtomicFact::NotIsCartFact(not_is_cart_fact) => vec![not_is_cart_fact.set.clone()],
            AtomicFact::NotIsTupleFact(not_is_tuple_fact) => vec![not_is_tuple_fact.set.clone()],
            AtomicFact::NotSubsetFact(not_subset_fact) => vec![not_subset_fact.left.clone(), not_subset_fact.right.clone()],
            AtomicFact::NotSupersetFact(not_superset_fact) => vec![not_superset_fact.left.clone(), not_superset_fact.right.clone()],
        }
    }

}

// 对每个类型的 atomic fact，都有个方法叫 required_args_len，返回该 atomic fact 需要的参数数量
impl AtomicFact {
    pub fn is_builtin_predicate_and_return_expected_args_len(&self) -> usize {
        match self {
            AtomicFact::EqualFact(_) => 2,
            AtomicFact::LessFact(_) => 2,
            AtomicFact::GreaterFact(_) => 2,
            AtomicFact::LessEqualFact(_) => 2,
            AtomicFact::GreaterEqualFact(_) => 2,
            AtomicFact::IsSetFact(_) => 1,
            AtomicFact::IsNonemptySetFact(_) => 1,
            AtomicFact::IsFiniteSetFact(_) => 1,
            AtomicFact::InFact(_) => 2,
            AtomicFact::IsCartFact(_) => 1,
            AtomicFact::IsTupleFact(_) => 1,
            AtomicFact::SubsetFact(_) => 2,
            AtomicFact::SupersetFact(_) => 2,
            AtomicFact::NotEqualFact(_) => 2,
            AtomicFact::NotLessFact(_) => 2,
            AtomicFact::NotGreaterFact(_) => 2,
            AtomicFact::NotLessEqualFact(_) => 2,
            AtomicFact::NotGreaterEqualFact(_) => 2,
            AtomicFact::NotIsSetFact(_) => 1,
            AtomicFact::NotIsNonemptySetFact(_) => 1,
            AtomicFact::NotIsFiniteSetFact(_) => 1,
            AtomicFact::NotInFact(_) => 2,
            AtomicFact::NotIsCartFact(_) => 1,
            AtomicFact::NotIsTupleFact(_) => 1,
            AtomicFact::NotSubsetFact(_) => 2,
            AtomicFact::NotSupersetFact(_) => 2,
            _ => panic!("其他情况的arg不是builtin"),
        }
    }
}

impl AtomicFact {
    pub fn number_of_args(&self) -> usize {
        match self {
            AtomicFact::EqualFact(_) => 2,
            AtomicFact::LessFact(_) => 2,
            AtomicFact::GreaterFact(_) => 2,
            AtomicFact::LessEqualFact(_) => 2,
            AtomicFact::GreaterEqualFact(_) => 2,
            AtomicFact::IsSetFact(_) => 1,
            AtomicFact::IsNonemptySetFact(_) => 1,
            AtomicFact::IsFiniteSetFact(_) => 1,
            AtomicFact::InFact(_) => 2,
            AtomicFact::IsCartFact(_) => 1,
            AtomicFact::IsTupleFact(_) => 1,
            AtomicFact::SubsetFact(_) => 2,
            AtomicFact::SupersetFact(_) => 2,
            AtomicFact::NotEqualFact(_) => 2,
            AtomicFact::NotLessFact(_) => 2,
            AtomicFact::NotGreaterFact(_) => 2,
            AtomicFact::NotLessEqualFact(_) => 2,
            AtomicFact::NotGreaterEqualFact(_) => 2,
            AtomicFact::NotIsSetFact(_) => 1,
            AtomicFact::NotIsNonemptySetFact(_) => 1,
            AtomicFact::NotIsFiniteSetFact(_) => 1,
            AtomicFact::NotInFact(_) => 2,
            AtomicFact::NotIsCartFact(_) => 1,
            AtomicFact::NotIsTupleFact(_) => 1,
            AtomicFact::NotSubsetFact(_) => 2,
            AtomicFact::NotSupersetFact(_) => 2,
            AtomicFact::NormalAtomicFact(a) => a.body.len(),
            AtomicFact::NotNormalAtomicFact(a) => a.body.len(),
        }
    }

    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        match self {
            AtomicFact::EqualFact(a) => a.line_file_index,
            AtomicFact::LessFact(a) => a.line_file_index,
            AtomicFact::GreaterFact(a) => a.line_file_index,
            AtomicFact::LessEqualFact(a) => a.line_file_index,
            AtomicFact::GreaterEqualFact(a) => a.line_file_index,
            AtomicFact::IsSetFact(a) => a.line_file_index,
            AtomicFact::IsNonemptySetFact(a) => a.line_file_index,
            AtomicFact::IsFiniteSetFact(a) => a.line_file_index,
            AtomicFact::InFact(a) => a.line_file_index,
            AtomicFact::IsCartFact(a) => a.line_file_index,
            AtomicFact::IsTupleFact(a) => a.line_file_index,
            AtomicFact::SubsetFact(a) => a.line_file_index,
            AtomicFact::SupersetFact(a) => a.line_file_index,
            AtomicFact::NormalAtomicFact(a) => a.line_file_index,
            AtomicFact::NotNormalAtomicFact(a) => a.line_file_index,
            AtomicFact::NotEqualFact(a) => a.line_file_index,
            AtomicFact::NotLessFact(a) => a.line_file_index,
            AtomicFact::NotGreaterFact(a) => a.line_file_index,
            AtomicFact::NotLessEqualFact(a) => a.line_file_index,
            AtomicFact::NotGreaterEqualFact(a) => a.line_file_index,
            AtomicFact::NotIsSetFact(a) => a.line_file_index,
            AtomicFact::NotIsNonemptySetFact(a) => a.line_file_index,
            AtomicFact::NotIsFiniteSetFact(a) => a.line_file_index,
            AtomicFact::NotInFact(a) => a.line_file_index,
            AtomicFact::NotIsCartFact(a) => a.line_file_index,
            AtomicFact::NotIsTupleFact(a) => a.line_file_index,
            AtomicFact::NotSubsetFact(a) => a.line_file_index,
            AtomicFact::NotSupersetFact(a) => a.line_file_index,
        }
    }
}