use crate::prelude::*;
use std::fmt;

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
    RestrictFact(RestrictFact),
    NotRestrictFact(NotRestrictFact),
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
pub struct RestrictFact {
    pub obj: Obj,
    pub obj_can_restrict_to_fn_set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotRestrictFact {
    pub obj: Obj,
    pub obj_cannot_restrict_to_fn_set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct SupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotSupersetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct SubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotSubsetFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsTupleFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsTupleFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsCartFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsCartFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct InFact {
    pub element: Obj,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotInFact {
    pub element: Obj,
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NormalAtomicFact {
    pub predicate: IdentifierOrIdentifierWithMod,
    pub body: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotNormalAtomicFact {
    pub predicate: IdentifierOrIdentifierWithMod,
    pub body: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct EqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct LessFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotLessFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct GreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotGreaterFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct LessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotLessEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct GreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotGreaterEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsNonemptySetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsNonemptySetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct IsFiniteSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotIsFiniteSetFact {
    pub set: Obj,
    pub line_file: LineFile,
}

impl SubsetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        SubsetFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotSubsetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotSubsetFact {
            left,
            right,
            line_file,
        }
    }
}

impl NormalAtomicFact {
    pub fn new(
        predicate: IdentifierOrIdentifierWithMod,
        body: Vec<Obj>,
        line_file: LineFile,
    ) -> Self {
        NormalAtomicFact {
            predicate,
            body,
            line_file,
        }
    }
}

impl NotNormalAtomicFact {
    pub fn new(
        predicate: IdentifierOrIdentifierWithMod,
        body: Vec<Obj>,
        line_file: LineFile,
    ) -> Self {
        NotNormalAtomicFact {
            predicate,
            body,
            line_file,
        }
    }
}

impl EqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        EqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl LessFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        LessFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotLessFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotLessFact {
            left,
            right,
            line_file,
        }
    }
}

impl GreaterFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        GreaterFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotGreaterFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotGreaterFact {
            left,
            right,
            line_file,
        }
    }
}

impl LessEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        LessEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotLessEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotLessEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl GreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        GreaterEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotGreaterEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotGreaterEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl IsSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsSetFact { set, line_file }
    }
}

impl NotIsSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsSetFact { set, line_file }
    }
}

impl IsNonemptySetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsNonemptySetFact { set, line_file }
    }
}

impl NotIsNonemptySetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsNonemptySetFact { set, line_file }
    }
}

impl IsFiniteSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsFiniteSetFact { set, line_file }
    }
}

impl NotIsFiniteSetFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsFiniteSetFact { set, line_file }
    }
}

impl InFact {
    pub fn new(element: Obj, set: Obj, line_file: LineFile) -> Self {
        InFact {
            element,
            set,
            line_file,
        }
    }
}

impl NotInFact {
    pub fn new(element: Obj, set: Obj, line_file: LineFile) -> Self {
        NotInFact {
            element,
            set,
            line_file,
        }
    }
}

impl IsCartFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        IsCartFact { set, line_file }
    }
}

impl NotIsCartFact {
    pub fn new(set: Obj, line_file: LineFile) -> Self {
        NotIsCartFact { set, line_file }
    }
}

impl IsTupleFact {
    pub fn new(tuple: Obj, line_file: LineFile) -> Self {
        IsTupleFact {
            set: tuple,
            line_file,
        }
    }
}

impl NotIsTupleFact {
    pub fn new(tuple: Obj, line_file: LineFile) -> Self {
        NotIsTupleFact {
            set: tuple,
            line_file,
        }
    }
}

impl SupersetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        SupersetFact {
            left,
            right,
            line_file,
        }
    }
}

impl NotSupersetFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        NotSupersetFact {
            left,
            right,
            line_file,
        }
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
            AtomicFact::RestrictFact(x) => write!(f, "{}", x),
            AtomicFact::NotRestrictFact(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for SupersetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{} {}",
            self.left, FACT_PREFIX, SUPERSET, self.right
        )
    }
}

impl fmt::Display for NotSupersetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.left, FACT_PREFIX, SUPERSET, self.right
        )
    }
}

impl fmt::Display for SubsetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", self.left, FACT_PREFIX, SUBSET, self.right)
    }
}

impl fmt::Display for NotSubsetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.left, FACT_PREFIX, SUBSET, self.right
        )
    }
}

impl fmt::Display for InFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{} {}", self.element, FACT_PREFIX, IN, self.set)
    }
}

impl fmt::Display for NotInFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.element, FACT_PREFIX, IN, self.set
        )
    }
}

impl fmt::Display for IsCartFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_CART, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsCartFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_CART,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for IsTupleFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FACT_PREFIX, IS_TUPLE, braced_string(&self.set))
    }
}

impl fmt::Display for NotIsTupleFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_TUPLE,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for NormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}",
            FACT_PREFIX,
            self.predicate,
            braced_vec_to_string(&self.body)
        )
    }
}

impl fmt::Display for NotNormalAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            self.predicate,
            braced_vec_to_string(&self.body)
        )
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
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for IsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}",
            FACT_PREFIX,
            IS_NONEMPTY_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for NotIsNonemptySetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_NONEMPTY_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for IsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}",
            FACT_PREFIX,
            IS_FINITE_SET,
            braced_string(&self.set)
        )
    }
}

impl fmt::Display for NotIsFiniteSetFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}",
            NOT,
            FACT_PREFIX,
            IS_FINITE_SET,
            braced_string(&self.set)
        )
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
            AtomicFact::RestrictFact(_) => RESTRICT.to_string(),
            AtomicFact::NotRestrictFact(_) => RESTRICT.to_string(),
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
            AtomicFact::RestrictFact(_) => true,
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
            AtomicFact::NotRestrictFact(_) => false,
        }
    }

    pub fn key(&self) -> String {
        return self.predicate_string();
    }

    pub fn transposed_binary_order_equivalent(&self) -> Option<Self> {
        match self {
            AtomicFact::LessFact(f) => Some(AtomicFact::GreaterFact(GreaterFact::new(
                f.right.clone(),
                f.left.clone(),
                f.line_file.clone(),
            ))),
            AtomicFact::GreaterFact(f) => Some(AtomicFact::LessFact(LessFact::new(
                f.right.clone(),
                f.left.clone(),
                f.line_file.clone(),
            ))),
            AtomicFact::LessEqualFact(f) => Some(AtomicFact::GreaterEqualFact(
                GreaterEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
            )),
            AtomicFact::GreaterEqualFact(f) => Some(AtomicFact::LessEqualFact(LessEqualFact::new(
                f.right.clone(),
                f.left.clone(),
                f.line_file.clone(),
            ))),
            AtomicFact::NotLessFact(f) => Some(AtomicFact::NotGreaterFact(NotGreaterFact::new(
                f.right.clone(),
                f.left.clone(),
                f.line_file.clone(),
            ))),
            AtomicFact::NotGreaterFact(f) => Some(AtomicFact::NotLessFact(NotLessFact::new(
                f.right.clone(),
                f.left.clone(),
                f.line_file.clone(),
            ))),
            AtomicFact::NotLessEqualFact(f) => Some(AtomicFact::NotGreaterEqualFact(
                NotGreaterEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
            )),
            AtomicFact::NotGreaterEqualFact(f) => Some(AtomicFact::NotLessEqualFact(
                NotLessEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
            )),
            _ => None,
        }
    }
}

impl AtomicFact {
    pub fn to_atomic_fact(
        prop_name: IdentifierOrIdentifierWithMod,
        is_true: bool,
        args: Vec<Obj>,
        line_file: LineFile,
    ) -> Result<AtomicFact, RuntimeErrorStruct> {
        let prop_name_as_string = prop_name.to_string();
        match prop_name_as_string.as_str() {
            EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", EQUAL, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::EqualFact(EqualFact::new(a0, a1, line_file)))
                } else {
                    Ok(AtomicFact::NotEqualFact(NotEqualFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            NOT_EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", NOT_EQUAL, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::NotEqualFact(NotEqualFact::new(
                        a0, a1, line_file,
                    )))
                } else {
                    Ok(AtomicFact::EqualFact(EqualFact::new(a0, a1, line_file)))
                }
            }
            LESS => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", LESS, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::LessFact(LessFact::new(a0, a1, line_file)))
                } else {
                    Ok(AtomicFact::NotLessFact(NotLessFact::new(a0, a1, line_file)))
                }
            }
            GREATER => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", GREATER, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::GreaterFact(GreaterFact::new(a0, a1, line_file)))
                } else {
                    Ok(AtomicFact::NotGreaterFact(NotGreaterFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            LESS_EQUAL => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        LESS_EQUAL,
                        args.len()
                    );
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::LessEqualFact(LessEqualFact::new(
                        a0, a1, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotLessEqualFact(NotLessEqualFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            GREATER_EQUAL => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        GREATER_EQUAL,
                        args.len()
                    );
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                        a0, a1, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            IS_SET => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_SET, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsSetFact(IsSetFact::new(a0, line_file)))
                } else {
                    Ok(AtomicFact::NotIsSetFact(NotIsSetFact::new(a0, line_file)))
                }
            }
            IS_NONEMPTY_SET => {
                if args.len() != 1 {
                    let msg = format!(
                        "{} requires 1 argument, but got {}",
                        IS_NONEMPTY_SET,
                        args.len()
                    );
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                        a0, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(
                        a0, line_file,
                    )))
                }
            }
            IS_FINITE_SET => {
                if args.len() != 1 {
                    let msg = format!(
                        "{} requires 1 argument, but got {}",
                        IS_FINITE_SET,
                        args.len()
                    );
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                        a0, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(
                        a0, line_file,
                    )))
                }
            }
            IN => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", IN, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::InFact(InFact::new(a0, a1, line_file)))
                } else {
                    Ok(AtomicFact::NotInFact(NotInFact::new(a0, a1, line_file)))
                }
            }
            IS_CART => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_CART, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsCartFact(IsCartFact::new(a0, line_file)))
                } else {
                    Ok(AtomicFact::NotIsCartFact(NotIsCartFact::new(a0, line_file)))
                }
            }
            IS_TUPLE => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_TUPLE, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::IsTupleFact(IsTupleFact::new(a0, line_file)))
                } else {
                    Ok(AtomicFact::NotIsTupleFact(NotIsTupleFact::new(
                        a0, line_file,
                    )))
                }
            }
            SUBSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUBSET, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::SubsetFact(SubsetFact::new(a0, a1, line_file)))
                } else {
                    Ok(AtomicFact::NotSubsetFact(NotSubsetFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            SUPERSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUPERSET, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::SupersetFact(SupersetFact::new(
                        a0, a1, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotSupersetFact(NotSupersetFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            RESTRICT => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", RESTRICT, args.len());
                    return Err(RuntimeErrorStruct::new_with_msg_previous_error(msg, None));
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(AtomicFact::RestrictFact(RestrictFact::new(
                        a0, a1, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotRestrictFact(NotRestrictFact::new(
                        a0, a1, line_file,
                    )))
                }
            }
            _ => {
                if is_true {
                    Ok(AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
                        prop_name, args, line_file,
                    )))
                } else {
                    Ok(AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(
                        prop_name, args, line_file,
                    )))
                }
            }
        }
    }
}

impl AtomicFact {
    pub fn args(&self) -> Vec<Obj> {
        match self {
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => normal_atomic_fact.body.clone(),
            AtomicFact::EqualFact(equal_fact) => {
                vec![equal_fact.left.clone(), equal_fact.right.clone()]
            }
            AtomicFact::LessFact(less_fact) => {
                vec![less_fact.left.clone(), less_fact.right.clone()]
            }
            AtomicFact::GreaterFact(greater_fact) => {
                vec![greater_fact.left.clone(), greater_fact.right.clone()]
            }
            AtomicFact::LessEqualFact(less_equal_fact) => {
                vec![less_equal_fact.left.clone(), less_equal_fact.right.clone()]
            }
            AtomicFact::GreaterEqualFact(greater_equal_fact) => vec![
                greater_equal_fact.left.clone(),
                greater_equal_fact.right.clone(),
            ],
            AtomicFact::IsSetFact(is_set_fact) => vec![is_set_fact.set.clone()],
            AtomicFact::IsNonemptySetFact(is_nonempty_set_fact) => {
                vec![is_nonempty_set_fact.set.clone()]
            }
            AtomicFact::IsFiniteSetFact(is_finite_set_fact) => vec![is_finite_set_fact.set.clone()],
            AtomicFact::InFact(in_fact) => vec![in_fact.element.clone(), in_fact.set.clone()],
            AtomicFact::IsCartFact(is_cart_fact) => vec![is_cart_fact.set.clone()],
            AtomicFact::IsTupleFact(is_tuple_fact) => vec![is_tuple_fact.set.clone()],
            AtomicFact::SubsetFact(subset_fact) => {
                vec![subset_fact.left.clone(), subset_fact.right.clone()]
            }
            AtomicFact::SupersetFact(superset_fact) => {
                vec![superset_fact.left.clone(), superset_fact.right.clone()]
            }
            AtomicFact::NotNormalAtomicFact(not_normal_atomic_fact) => {
                not_normal_atomic_fact.body.clone()
            }
            AtomicFact::NotEqualFact(not_equal_fact) => {
                vec![not_equal_fact.left.clone(), not_equal_fact.right.clone()]
            }
            AtomicFact::NotLessFact(not_less_fact) => {
                vec![not_less_fact.left.clone(), not_less_fact.right.clone()]
            }
            AtomicFact::NotGreaterFact(not_greater_fact) => vec![
                not_greater_fact.left.clone(),
                not_greater_fact.right.clone(),
            ],
            AtomicFact::NotLessEqualFact(not_less_equal_fact) => vec![
                not_less_equal_fact.left.clone(),
                not_less_equal_fact.right.clone(),
            ],
            AtomicFact::NotGreaterEqualFact(not_greater_equal_fact) => vec![
                not_greater_equal_fact.left.clone(),
                not_greater_equal_fact.right.clone(),
            ],
            AtomicFact::NotIsSetFact(not_is_set_fact) => vec![not_is_set_fact.set.clone()],
            AtomicFact::NotIsNonemptySetFact(not_is_nonempty_set_fact) => {
                vec![not_is_nonempty_set_fact.set.clone()]
            }
            AtomicFact::NotIsFiniteSetFact(not_is_finite_set_fact) => {
                vec![not_is_finite_set_fact.set.clone()]
            }
            AtomicFact::NotInFact(not_in_fact) => {
                vec![not_in_fact.element.clone(), not_in_fact.set.clone()]
            }
            AtomicFact::NotIsCartFact(not_is_cart_fact) => vec![not_is_cart_fact.set.clone()],
            AtomicFact::NotIsTupleFact(not_is_tuple_fact) => vec![not_is_tuple_fact.set.clone()],
            AtomicFact::NotSubsetFact(not_subset_fact) => {
                vec![not_subset_fact.left.clone(), not_subset_fact.right.clone()]
            }
            AtomicFact::NotSupersetFact(not_superset_fact) => vec![
                not_superset_fact.left.clone(),
                not_superset_fact.right.clone(),
            ],
            AtomicFact::RestrictFact(restrict_fact) => vec![
                restrict_fact.obj.clone(),
                restrict_fact.obj_can_restrict_to_fn_set.clone().into(),
            ],
            AtomicFact::NotRestrictFact(not_restrict_fact) => vec![
                not_restrict_fact.obj.clone(),
                not_restrict_fact.obj_cannot_restrict_to_fn_set.clone(),
            ],
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
            AtomicFact::RestrictFact(_) => 2,
            AtomicFact::NotRestrictFact(_) => 2,
            _ => unreachable!("其他情况不是builtin predicate"),
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
            AtomicFact::RestrictFact(_) => 2,
            AtomicFact::NotRestrictFact(_) => 2,
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            AtomicFact::EqualFact(a) => a.line_file.clone(),
            AtomicFact::LessFact(a) => a.line_file.clone(),
            AtomicFact::GreaterFact(a) => a.line_file.clone(),
            AtomicFact::LessEqualFact(a) => a.line_file.clone(),
            AtomicFact::GreaterEqualFact(a) => a.line_file.clone(),
            AtomicFact::IsSetFact(a) => a.line_file.clone(),
            AtomicFact::IsNonemptySetFact(a) => a.line_file.clone(),
            AtomicFact::IsFiniteSetFact(a) => a.line_file.clone(),
            AtomicFact::InFact(a) => a.line_file.clone(),
            AtomicFact::IsCartFact(a) => a.line_file.clone(),
            AtomicFact::IsTupleFact(a) => a.line_file.clone(),
            AtomicFact::SubsetFact(a) => a.line_file.clone(),
            AtomicFact::SupersetFact(a) => a.line_file.clone(),
            AtomicFact::NormalAtomicFact(a) => a.line_file.clone(),
            AtomicFact::NotNormalAtomicFact(a) => a.line_file.clone(),
            AtomicFact::NotEqualFact(a) => a.line_file.clone(),
            AtomicFact::NotLessFact(a) => a.line_file.clone(),
            AtomicFact::NotGreaterFact(a) => a.line_file.clone(),
            AtomicFact::NotLessEqualFact(a) => a.line_file.clone(),
            AtomicFact::NotGreaterEqualFact(a) => a.line_file.clone(),
            AtomicFact::NotIsSetFact(a) => a.line_file.clone(),
            AtomicFact::NotIsNonemptySetFact(a) => a.line_file.clone(),
            AtomicFact::NotIsFiniteSetFact(a) => a.line_file.clone(),
            AtomicFact::NotInFact(a) => a.line_file.clone(),
            AtomicFact::NotIsCartFact(a) => a.line_file.clone(),
            AtomicFact::NotIsTupleFact(a) => a.line_file.clone(),
            AtomicFact::NotSubsetFact(a) => a.line_file.clone(),
            AtomicFact::NotSupersetFact(a) => a.line_file.clone(),
            AtomicFact::RestrictFact(a) => a.line_file.clone(),
            AtomicFact::NotRestrictFact(a) => a.line_file.clone(),
        }
    }

    pub fn with_new_line_file(self, line_file: LineFile) -> Self {
        match self {
            AtomicFact::EqualFact(x) => {
                AtomicFact::EqualFact(EqualFact::new(x.left, x.right, line_file))
            }
            AtomicFact::LessFact(x) => {
                AtomicFact::LessFact(LessFact::new(x.left, x.right, line_file))
            }
            AtomicFact::GreaterFact(x) => {
                AtomicFact::GreaterFact(GreaterFact::new(x.left, x.right, line_file))
            }
            AtomicFact::LessEqualFact(x) => {
                AtomicFact::LessEqualFact(LessEqualFact::new(x.left, x.right, line_file))
            }
            AtomicFact::GreaterEqualFact(x) => {
                AtomicFact::GreaterEqualFact(GreaterEqualFact::new(x.left, x.right, line_file))
            }
            AtomicFact::IsSetFact(x) => AtomicFact::IsSetFact(IsSetFact::new(x.set, line_file)),
            AtomicFact::IsNonemptySetFact(x) => {
                AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(x.set, line_file))
            }
            AtomicFact::IsFiniteSetFact(x) => {
                AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(x.set, line_file))
            }
            AtomicFact::InFact(x) => AtomicFact::InFact(InFact::new(x.element, x.set, line_file)),
            AtomicFact::IsCartFact(x) => AtomicFact::IsCartFact(IsCartFact::new(x.set, line_file)),
            AtomicFact::IsTupleFact(x) => {
                AtomicFact::IsTupleFact(IsTupleFact::new(x.set, line_file))
            }
            AtomicFact::SubsetFact(x) => {
                AtomicFact::SubsetFact(SubsetFact::new(x.left, x.right, line_file))
            }
            AtomicFact::SupersetFact(x) => {
                AtomicFact::SupersetFact(SupersetFact::new(x.left, x.right, line_file))
            }
            AtomicFact::NormalAtomicFact(x) => {
                AtomicFact::NormalAtomicFact(NormalAtomicFact::new(x.predicate, x.body, line_file))
            }
            AtomicFact::NotNormalAtomicFact(x) => AtomicFact::NotNormalAtomicFact(
                NotNormalAtomicFact::new(x.predicate, x.body, line_file),
            ),
            AtomicFact::NotEqualFact(x) => {
                AtomicFact::NotEqualFact(NotEqualFact::new(x.left, x.right, line_file))
            }
            AtomicFact::NotLessFact(x) => {
                AtomicFact::NotLessFact(NotLessFact::new(x.left, x.right, line_file))
            }
            AtomicFact::NotGreaterFact(x) => {
                AtomicFact::NotGreaterFact(NotGreaterFact::new(x.left, x.right, line_file))
            }
            AtomicFact::NotLessEqualFact(x) => {
                AtomicFact::NotLessEqualFact(NotLessEqualFact::new(x.left, x.right, line_file))
            }
            AtomicFact::NotGreaterEqualFact(x) => AtomicFact::NotGreaterEqualFact(
                NotGreaterEqualFact::new(x.left, x.right, line_file),
            ),
            AtomicFact::NotIsSetFact(x) => {
                AtomicFact::NotIsSetFact(NotIsSetFact::new(x.set, line_file))
            }
            AtomicFact::NotIsNonemptySetFact(x) => {
                AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(x.set, line_file))
            }
            AtomicFact::NotIsFiniteSetFact(x) => {
                AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(x.set, line_file))
            }
            AtomicFact::NotInFact(x) => {
                AtomicFact::NotInFact(NotInFact::new(x.element, x.set, line_file))
            }
            AtomicFact::NotIsCartFact(x) => {
                AtomicFact::NotIsCartFact(NotIsCartFact::new(x.set, line_file))
            }
            AtomicFact::NotIsTupleFact(x) => {
                AtomicFact::NotIsTupleFact(NotIsTupleFact::new(x.set, line_file))
            }
            AtomicFact::NotSubsetFact(x) => {
                AtomicFact::NotSubsetFact(NotSubsetFact::new(x.left, x.right, line_file))
            }
            AtomicFact::NotSupersetFact(x) => {
                AtomicFact::NotSupersetFact(NotSupersetFact::new(x.left, x.right, line_file))
            }
            AtomicFact::RestrictFact(x) => AtomicFact::RestrictFact(RestrictFact::new(
                x.obj,
                x.obj_can_restrict_to_fn_set,
                line_file,
            )),
            AtomicFact::NotRestrictFact(x) => AtomicFact::NotRestrictFact(NotRestrictFact::new(
                x.obj,
                x.obj_cannot_restrict_to_fn_set,
                line_file,
            )),
        }
    }
}

impl RestrictFact {
    pub fn new(obj: Obj, obj_can_restrict_to_fn_set: Obj, line_file: LineFile) -> Self {
        RestrictFact {
            obj,
            obj_can_restrict_to_fn_set,
            line_file,
        }
    }
}

impl NotRestrictFact {
    pub fn new(obj: Obj, obj_cannot_restrict_to_fn_set: Obj, line_file: LineFile) -> Self {
        NotRestrictFact {
            obj,
            obj_cannot_restrict_to_fn_set,
            line_file,
        }
    }
}

impl fmt::Display for RestrictFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{} {}",
            self.obj, FACT_PREFIX, RESTRICT, self.obj_can_restrict_to_fn_set
        )
    }
}

impl fmt::Display for NotRestrictFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.obj, FACT_PREFIX, RESTRICT, self.obj_cannot_restrict_to_fn_set
        )
    }
}

impl AtomicFact {
    pub fn get_args_from_fact(&self) -> Vec<Obj> {
        self.args()
    }
}

impl AtomicFact {
    pub fn make_reversed(&self) -> AtomicFact {
        match self {
            AtomicFact::NormalAtomicFact(a) => AtomicFact::NotNormalAtomicFact(
                NotNormalAtomicFact::new(a.predicate.clone(), a.body.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotNormalAtomicFact(a) => AtomicFact::NormalAtomicFact(
                NormalAtomicFact::new(a.predicate.clone(), a.body.clone(), a.line_file.clone()),
            ),
            AtomicFact::EqualFact(a) => AtomicFact::NotEqualFact(NotEqualFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::LessFact(a) => AtomicFact::NotLessFact(NotLessFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::GreaterFact(a) => AtomicFact::NotGreaterFact(NotGreaterFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::LessEqualFact(a) => AtomicFact::NotLessEqualFact(NotLessEqualFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::GreaterEqualFact(a) => AtomicFact::NotGreaterEqualFact(
                NotGreaterEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsSetFact(a) => {
                AtomicFact::NotIsSetFact(NotIsSetFact::new(a.set.clone(), a.line_file.clone()))
            }
            AtomicFact::IsNonemptySetFact(a) => AtomicFact::IsNonemptySetFact(
                IsNonemptySetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsFiniteSetFact(a) => AtomicFact::NotIsFiniteSetFact(
                NotIsFiniteSetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::InFact(a) => AtomicFact::NotInFact(NotInFact::new(
                a.element.clone(),
                a.set.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::IsCartFact(a) => {
                AtomicFact::NotIsCartFact(NotIsCartFact::new(a.set.clone(), a.line_file.clone()))
            }
            AtomicFact::IsTupleFact(a) => {
                AtomicFact::NotIsTupleFact(NotIsTupleFact::new(a.set.clone(), a.line_file.clone()))
            }
            AtomicFact::SubsetFact(a) => AtomicFact::NotSubsetFact(NotSubsetFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::SupersetFact(a) => AtomicFact::NotSupersetFact(NotSupersetFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::RestrictFact(a) => AtomicFact::NotRestrictFact(NotRestrictFact::new(
                a.obj.clone(),
                a.obj_can_restrict_to_fn_set.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotEqualFact(a) => AtomicFact::EqualFact(EqualFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotLessFact(a) => AtomicFact::LessFact(LessFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotGreaterFact(a) => AtomicFact::GreaterFact(GreaterFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotLessEqualFact(a) => AtomicFact::LessEqualFact(LessEqualFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotGreaterEqualFact(a) => AtomicFact::GreaterEqualFact(
                GreaterEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsSetFact(a) => {
                AtomicFact::IsSetFact(IsSetFact::new(a.set.clone(), a.line_file.clone()))
            }
            AtomicFact::NotIsNonemptySetFact(a) => AtomicFact::IsNonemptySetFact(
                IsNonemptySetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsFiniteSetFact(a) => AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                a.set.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotInFact(a) => AtomicFact::InFact(InFact::new(
                a.element.clone(),
                a.set.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotIsCartFact(a) => {
                AtomicFact::IsCartFact(IsCartFact::new(a.set.clone(), a.line_file.clone()))
            }
            AtomicFact::NotIsTupleFact(a) => {
                AtomicFact::IsTupleFact(IsTupleFact::new(a.set.clone(), a.line_file.clone()))
            }
            AtomicFact::NotSubsetFact(a) => AtomicFact::SubsetFact(SubsetFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotSupersetFact(a) => AtomicFact::SupersetFact(SupersetFact::new(
                a.left.clone(),
                a.right.clone(),
                a.line_file.clone(),
            )),
            AtomicFact::NotRestrictFact(a) => AtomicFact::RestrictFact(RestrictFact::new(
                a.obj.clone(),
                a.obj_cannot_restrict_to_fn_set.clone(),
                a.line_file.clone(),
            )),
        }
    }
}

impl AtomicFact {
    fn body_vec_after_calculate_each_calculable_arg(original_body: &Vec<Obj>) -> Vec<Obj> {
        let mut next_body = Vec::new();
        for obj in original_body {
            next_body.push(obj.replace_with_numeric_result_if_can_be_calculated().0);
        }
        next_body
    }

    pub fn calculate_args(&self) -> (AtomicFact, bool) {
        let calculated_atomic_fact = match self {
            AtomicFact::NormalAtomicFact(inner) => {
                AtomicFact::NormalAtomicFact(NormalAtomicFact::new(
                    inner.predicate.clone(),
                    Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::NotNormalAtomicFact(inner) => {
                AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(
                    inner.predicate.clone(),
                    Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::EqualFact(inner) => AtomicFact::EqualFact(EqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotEqualFact(inner) => AtomicFact::NotEqualFact(NotEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::LessFact(inner) => AtomicFact::LessFact(LessFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotLessFact(inner) => AtomicFact::NotLessFact(NotLessFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::GreaterFact(inner) => AtomicFact::GreaterFact(GreaterFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotGreaterFact(inner) => AtomicFact::NotGreaterFact(NotGreaterFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::LessEqualFact(inner) => AtomicFact::LessEqualFact(LessEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotLessEqualFact(inner) => {
                AtomicFact::NotLessEqualFact(NotLessEqualFact::new(
                    inner
                        .left
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner
                        .right
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::GreaterEqualFact(inner) => {
                AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                    inner
                        .left
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner
                        .right
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::NotGreaterEqualFact(inner) => {
                AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(
                    inner
                        .left
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner
                        .right
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::IsSetFact(inner) => AtomicFact::IsSetFact(IsSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotIsSetFact(inner) => AtomicFact::NotIsSetFact(NotIsSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::IsNonemptySetFact(inner) => {
                AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::NotIsNonemptySetFact(inner) => {
                AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact::new(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::IsFiniteSetFact(inner) => {
                AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::NotIsFiniteSetFact(inner) => {
                AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact::new(
                    inner
                        .set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::InFact(inner) => AtomicFact::InFact(InFact::new(
                inner
                    .element
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotInFact(inner) => AtomicFact::NotInFact(NotInFact::new(
                inner
                    .element
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::IsCartFact(inner) => AtomicFact::IsCartFact(IsCartFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotIsCartFact(inner) => AtomicFact::NotIsCartFact(NotIsCartFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::IsTupleFact(inner) => AtomicFact::IsTupleFact(IsTupleFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotIsTupleFact(inner) => AtomicFact::NotIsTupleFact(NotIsTupleFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::SubsetFact(inner) => AtomicFact::SubsetFact(SubsetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotSubsetFact(inner) => AtomicFact::NotSubsetFact(NotSubsetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::SupersetFact(inner) => AtomicFact::SupersetFact(SupersetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotSupersetFact(inner) => {
                AtomicFact::NotSupersetFact(NotSupersetFact::new(
                    inner
                        .left
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner
                        .right
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
            AtomicFact::RestrictFact(inner) => AtomicFact::RestrictFact(RestrictFact::new(
                inner
                    .obj
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .obj_can_restrict_to_fn_set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )),
            AtomicFact::NotRestrictFact(inner) => {
                AtomicFact::NotRestrictFact(NotRestrictFact::new(
                    inner
                        .obj
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner
                        .obj_cannot_restrict_to_fn_set
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0,
                    inner.line_file.clone(),
                ))
            }
        };
        let any_argument_replaced = calculated_atomic_fact.to_string() != self.to_string();
        (calculated_atomic_fact, any_argument_replaced)
    }
}
