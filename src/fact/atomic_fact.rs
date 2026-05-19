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
    FnEqualInFact(FnEqualInFact),
    FnEqualFact(FnEqualFact),
}

#[derive(Clone)]
pub struct FnEqualInFact {
    pub left: Obj,
    pub right: Obj,
    pub set: Obj,
    pub line_file: LineFile,
}

impl FnEqualInFact {
    pub fn new(left: Obj, right: Obj, set: Obj, line_file: LineFile) -> Self {
        FnEqualInFact {
            left,
            right,
            set,
            line_file,
        }
    }
}

impl fmt::Display for FnEqualInFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}({}, {}, {})",
            FACT_PREFIX, FN_EQ_IN, self.left, self.right, self.set
        )
    }
}

#[derive(Clone)]
pub struct FnEqualFact {
    pub left: Obj,
    pub right: Obj,
    pub line_file: LineFile,
}

impl FnEqualFact {
    pub fn new(left: Obj, right: Obj, line_file: LineFile) -> Self {
        FnEqualFact {
            left,
            right,
            line_file,
        }
    }
}

impl fmt::Display for FnEqualFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}({}, {})", FACT_PREFIX, FN_EQ, self.left, self.right)
    }
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
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct NotNormalAtomicFact {
    pub predicate: AtomicName,
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
    pub fn new(predicate: AtomicName, body: Vec<Obj>, line_file: LineFile) -> Self {
        NormalAtomicFact {
            predicate,
            body,
            line_file,
        }
    }
}

impl NotNormalAtomicFact {
    pub fn new(predicate: AtomicName, body: Vec<Obj>, line_file: LineFile) -> Self {
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
            AtomicFact::FnEqualInFact(x) => write!(f, "{}", x),
            AtomicFact::FnEqualFact(x) => write!(f, "{}", x),
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
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        fn r(o: Obj, from: &str, to: &str) -> Obj {
            Obj::replace_bound_identifier(o, from, to)
        }
        match self {
            AtomicFact::NormalAtomicFact(x) => NormalAtomicFact::new(
                x.predicate,
                x.body.into_iter().map(|o| r(o, from, to)).collect(),
                x.line_file,
            )
            .into(),
            AtomicFact::EqualFact(x) => {
                EqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::LessFact(x) => {
                LessFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::GreaterFact(x) => {
                GreaterFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::LessEqualFact(x) => {
                LessEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::GreaterEqualFact(x) => {
                GreaterEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::IsSetFact(x) => IsSetFact::new(r(x.set, from, to), x.line_file).into(),
            AtomicFact::IsNonemptySetFact(x) => {
                IsNonemptySetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::IsFiniteSetFact(x) => {
                IsFiniteSetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::InFact(x) => {
                InFact::new(r(x.element, from, to), r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::IsCartFact(x) => IsCartFact::new(r(x.set, from, to), x.line_file).into(),
            AtomicFact::IsTupleFact(x) => IsTupleFact::new(r(x.set, from, to), x.line_file).into(),
            AtomicFact::SubsetFact(x) => {
                SubsetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::SupersetFact(x) => {
                SupersetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::RestrictFact(x) => RestrictFact::new(
                r(x.obj, from, to),
                r(x.obj_can_restrict_to_fn_set, from, to),
                x.line_file,
            )
            .into(),
            AtomicFact::NotRestrictFact(x) => NotRestrictFact::new(
                r(x.obj, from, to),
                r(x.obj_cannot_restrict_to_fn_set, from, to),
                x.line_file,
            )
            .into(),
            AtomicFact::NotNormalAtomicFact(x) => NotNormalAtomicFact::new(
                x.predicate,
                x.body.into_iter().map(|o| r(o, from, to)).collect(),
                x.line_file,
            )
            .into(),
            AtomicFact::NotEqualFact(x) => {
                NotEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotLessFact(x) => {
                NotLessFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotGreaterFact(x) => {
                NotGreaterFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotLessEqualFact(x) => {
                NotLessEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotGreaterEqualFact(x) => {
                NotGreaterEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file)
                    .into()
            }
            AtomicFact::NotIsSetFact(x) => {
                NotIsSetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsNonemptySetFact(x) => {
                NotIsNonemptySetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsFiniteSetFact(x) => {
                NotIsFiniteSetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotInFact(x) => {
                NotInFact::new(r(x.element, from, to), r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsCartFact(x) => {
                NotIsCartFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsTupleFact(x) => {
                NotIsTupleFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotSubsetFact(x) => {
                NotSubsetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotSupersetFact(x) => {
                NotSupersetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::FnEqualInFact(x) => FnEqualInFact::new(
                r(x.left, from, to),
                r(x.right, from, to),
                r(x.set, from, to),
                x.line_file,
            )
            .into(),
            AtomicFact::FnEqualFact(x) => {
                FnEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
        }
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
            AtomicFact::RestrictFact(_) => RESTRICT_FN_IN.to_string(),
            AtomicFact::NotRestrictFact(_) => RESTRICT_FN_IN.to_string(),
            AtomicFact::FnEqualInFact(_) => FN_EQ_IN.to_string(),
            AtomicFact::FnEqualFact(_) => FN_EQ.to_string(),
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
            AtomicFact::FnEqualInFact(_) => true,
            AtomicFact::FnEqualFact(_) => true,
        }
    }

    pub fn key(&self) -> String {
        return self.predicate_string();
    }

    pub fn transposed_binary_order_equivalent(&self) -> Option<Self> {
        match self {
            AtomicFact::LessFact(f) => {
                Some(GreaterFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
            }
            AtomicFact::GreaterFact(f) => {
                Some(LessFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
            }
            AtomicFact::LessEqualFact(f) => Some(AtomicFact::GreaterEqualFact(
                GreaterEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
            )),
            AtomicFact::GreaterEqualFact(f) => Some(
                LessEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into(),
            ),
            AtomicFact::NotLessFact(f) => Some(
                NotGreaterFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into(),
            ),
            AtomicFact::NotGreaterFact(f) => {
                Some(NotLessFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
            }
            AtomicFact::NotLessEqualFact(f) => Some(AtomicFact::NotGreaterEqualFact(
                NotGreaterEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
            )),
            AtomicFact::NotGreaterEqualFact(f) => Some(AtomicFact::NotLessEqualFact(
                NotLessEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
            )),
            AtomicFact::FnEqualFact(f) => {
                Some(FnEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
            }
            AtomicFact::FnEqualInFact(f) => Some(
                FnEqualInFact::new(
                    f.right.clone(),
                    f.left.clone(),
                    f.set.clone(),
                    f.line_file.clone(),
                )
                .into(),
            ),
            _ => None,
        }
    }

    pub fn symmetric_reordered_args(&self, gather: &[usize]) -> Option<Self> {
        match self {
            AtomicFact::NormalAtomicFact(f) => {
                let n = f.body.len();
                if gather.len() != n || n < 2 {
                    return None;
                }
                let mut seen = vec![false; n];
                for &i in gather {
                    if i >= n || seen[i] {
                        return None;
                    }
                    seen[i] = true;
                }
                let new_body: Vec<Obj> = gather.iter().map(|&i| f.body[i].clone()).collect();
                Some(
                    NormalAtomicFact::new(f.predicate.clone(), new_body, f.line_file.clone())
                        .into(),
                )
            }
            _ => None,
        }
    }
}

impl AtomicFact {
    pub fn to_atomic_fact(
        prop_name: AtomicName,
        is_true: bool,
        args: Vec<Obj>,
        line_file: LineFile,
    ) -> Result<AtomicFact, RuntimeError> {
        let prop_name_as_string = prop_name.to_string();
        match prop_name_as_string.as_str() {
            EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", EQUAL, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(EqualFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotEqualFact::new(a0, a1, line_file).into())
                }
            }
            NOT_EQUAL => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", NOT_EQUAL, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(NotEqualFact::new(a0, a1, line_file).into())
                } else {
                    Ok(EqualFact::new(a0, a1, line_file).into())
                }
            }
            LESS => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", LESS, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(LessFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotLessFact::new(a0, a1, line_file).into())
                }
            }
            GREATER => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", GREATER, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(GreaterFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotGreaterFact::new(a0, a1, line_file).into())
                }
            }
            LESS_EQUAL => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        LESS_EQUAL,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(LessEqualFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotLessEqualFact::new(a0, a1, line_file).into())
                }
            }
            GREATER_EQUAL => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        GREATER_EQUAL,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(GreaterEqualFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotGreaterEqualFact::new(a0, a1, line_file).into())
                }
            }
            IS_SET => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_SET, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(IsSetFact::new(a0, line_file).into())
                } else {
                    Ok(NotIsSetFact::new(a0, line_file).into())
                }
            }
            IS_NONEMPTY_SET => {
                if args.len() != 1 {
                    let msg = format!(
                        "{} requires 1 argument, but got {}",
                        IS_NONEMPTY_SET,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(IsNonemptySetFact::new(a0, line_file).into())
                } else {
                    Ok(NotIsNonemptySetFact::new(a0, line_file).into())
                }
            }
            IS_FINITE_SET => {
                if args.len() != 1 {
                    let msg = format!(
                        "{} requires 1 argument, but got {}",
                        IS_FINITE_SET,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(IsFiniteSetFact::new(a0, line_file).into())
                } else {
                    Ok(NotIsFiniteSetFact::new(a0, line_file).into())
                }
            }
            IN => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", IN, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(InFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotInFact::new(a0, a1, line_file).into())
                }
            }
            IS_CART => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_CART, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(IsCartFact::new(a0, line_file).into())
                } else {
                    Ok(NotIsCartFact::new(a0, line_file).into())
                }
            }
            IS_TUPLE => {
                if args.len() != 1 {
                    let msg = format!("{} requires 1 argument, but got {}", IS_TUPLE, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                if is_true {
                    Ok(IsTupleFact::new(a0, line_file).into())
                } else {
                    Ok(NotIsTupleFact::new(a0, line_file).into())
                }
            }
            SUBSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUBSET, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(SubsetFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotSubsetFact::new(a0, a1, line_file).into())
                }
            }
            SUPERSET => {
                if args.len() != 2 {
                    let msg = format!("{} requires 2 arguments, but got {}", SUPERSET, args.len());
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(SupersetFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotSupersetFact::new(a0, a1, line_file).into())
                }
            }
            RESTRICT_FN_IN => {
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments, but got {}",
                        RESTRICT_FN_IN,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                if is_true {
                    Ok(RestrictFact::new(a0, a1, line_file).into())
                } else {
                    Ok(NotRestrictFact::new(a0, a1, line_file).into())
                }
            }
            FN_EQ_IN => {
                if !is_true {
                    let msg = format!("{} does not support `not`", FN_EQ_IN);
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                if args.len() != 3 {
                    let msg = format!(
                        "{} requires 3 arguments (f, g, set), but got {}",
                        FN_EQ_IN,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                let a2 = args.remove(0);
                Ok(FnEqualInFact::new(a0, a1, a2, line_file).into())
            }
            FN_EQ => {
                if !is_true {
                    let msg = format!("{} does not support `not`", FN_EQ);
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                if args.len() != 2 {
                    let msg = format!(
                        "{} requires 2 arguments (f, g), but got {}",
                        FN_EQ,
                        args.len()
                    );
                    return Err(NewFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, line_file.clone()),
                    )
                    .into());
                }
                let mut args = args;
                let a0 = args.remove(0);
                let a1 = args.remove(0);
                Ok(FnEqualFact::new(a0, a1, line_file).into())
            }
            _ => {
                if is_true {
                    Ok(NormalAtomicFact::new(prop_name, args, line_file).into())
                } else {
                    Ok(NotNormalAtomicFact::new(prop_name, args, line_file).into())
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
            AtomicFact::FnEqualInFact(f) => {
                vec![f.left.clone(), f.right.clone(), f.set.clone()]
            }
            AtomicFact::FnEqualFact(f) => vec![f.left.clone(), f.right.clone()],
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
            AtomicFact::FnEqualInFact(_) => 3,
            AtomicFact::FnEqualFact(_) => 2,
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
            AtomicFact::FnEqualInFact(_) => 3,
            AtomicFact::FnEqualFact(_) => 2,
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
            AtomicFact::FnEqualInFact(a) => a.line_file.clone(),
            AtomicFact::FnEqualFact(a) => a.line_file.clone(),
        }
    }

    pub fn with_line_file(mut self, line_file: LineFile) -> Self {
        match &mut self {
            AtomicFact::EqualFact(a) => a.line_file = line_file,
            AtomicFact::LessFact(a) => a.line_file = line_file,
            AtomicFact::GreaterFact(a) => a.line_file = line_file,
            AtomicFact::LessEqualFact(a) => a.line_file = line_file,
            AtomicFact::GreaterEqualFact(a) => a.line_file = line_file,
            AtomicFact::IsSetFact(a) => a.line_file = line_file,
            AtomicFact::IsNonemptySetFact(a) => a.line_file = line_file,
            AtomicFact::IsFiniteSetFact(a) => a.line_file = line_file,
            AtomicFact::InFact(a) => a.line_file = line_file,
            AtomicFact::IsCartFact(a) => a.line_file = line_file,
            AtomicFact::IsTupleFact(a) => a.line_file = line_file,
            AtomicFact::SubsetFact(a) => a.line_file = line_file,
            AtomicFact::SupersetFact(a) => a.line_file = line_file,
            AtomicFact::NormalAtomicFact(a) => a.line_file = line_file,
            AtomicFact::NotNormalAtomicFact(a) => a.line_file = line_file,
            AtomicFact::NotEqualFact(a) => a.line_file = line_file,
            AtomicFact::NotLessFact(a) => a.line_file = line_file,
            AtomicFact::NotGreaterFact(a) => a.line_file = line_file,
            AtomicFact::NotLessEqualFact(a) => a.line_file = line_file,
            AtomicFact::NotGreaterEqualFact(a) => a.line_file = line_file,
            AtomicFact::NotIsSetFact(a) => a.line_file = line_file,
            AtomicFact::NotIsNonemptySetFact(a) => a.line_file = line_file,
            AtomicFact::NotIsFiniteSetFact(a) => a.line_file = line_file,
            AtomicFact::NotInFact(a) => a.line_file = line_file,
            AtomicFact::NotIsCartFact(a) => a.line_file = line_file,
            AtomicFact::NotIsTupleFact(a) => a.line_file = line_file,
            AtomicFact::NotSubsetFact(a) => a.line_file = line_file,
            AtomicFact::NotSupersetFact(a) => a.line_file = line_file,
            AtomicFact::RestrictFact(a) => a.line_file = line_file,
            AtomicFact::NotRestrictFact(a) => a.line_file = line_file,
            AtomicFact::FnEqualInFact(a) => a.line_file = line_file,
            AtomicFact::FnEqualFact(a) => a.line_file = line_file,
        }
        self
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
            self.obj, FACT_PREFIX, RESTRICT_FN_IN, self.obj_can_restrict_to_fn_set
        )
    }
}

impl fmt::Display for NotRestrictFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {}",
            NOT, self.obj, FACT_PREFIX, RESTRICT_FN_IN, self.obj_cannot_restrict_to_fn_set
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
            AtomicFact::EqualFact(a) => {
                NotEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::LessFact(a) => {
                NotLessFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::GreaterFact(a) => {
                NotGreaterFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::LessEqualFact(a) => {
                NotLessEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::GreaterEqualFact(a) => AtomicFact::NotGreaterEqualFact(
                NotGreaterEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsSetFact(a) => {
                NotIsSetFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::IsNonemptySetFact(a) => AtomicFact::NotIsNonemptySetFact(
                NotIsNonemptySetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsFiniteSetFact(a) => AtomicFact::NotIsFiniteSetFact(
                NotIsFiniteSetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::InFact(a) => {
                NotInFact::new(a.element.clone(), a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::IsCartFact(a) => {
                NotIsCartFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::IsTupleFact(a) => {
                NotIsTupleFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::SubsetFact(a) => {
                NotSubsetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::SupersetFact(a) => {
                NotSupersetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::RestrictFact(a) => NotRestrictFact::new(
                a.obj.clone(),
                a.obj_can_restrict_to_fn_set.clone(),
                a.line_file.clone(),
            )
            .into(),
            AtomicFact::NotEqualFact(a) => {
                EqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotLessFact(a) => {
                LessFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotGreaterFact(a) => {
                GreaterFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotLessEqualFact(a) => {
                LessEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotGreaterEqualFact(a) => AtomicFact::GreaterEqualFact(
                GreaterEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsSetFact(a) => {
                IsSetFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotIsNonemptySetFact(a) => AtomicFact::IsNonemptySetFact(
                IsNonemptySetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsFiniteSetFact(a) => {
                IsFiniteSetFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotInFact(a) => {
                InFact::new(a.element.clone(), a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotIsCartFact(a) => {
                IsCartFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotIsTupleFact(a) => {
                IsTupleFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotSubsetFact(a) => {
                SubsetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotSupersetFact(a) => {
                SupersetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotRestrictFact(a) => RestrictFact::new(
                a.obj.clone(),
                a.obj_cannot_restrict_to_fn_set.clone(),
                a.line_file.clone(),
            )
            .into(),
            AtomicFact::FnEqualInFact(a) => FnEqualInFact::new(
                a.right.clone(),
                a.left.clone(),
                a.set.clone(),
                a.line_file.clone(),
            )
            .into(),
            AtomicFact::FnEqualFact(a) => {
                FnEqualFact::new(a.right.clone(), a.left.clone(), a.line_file.clone()).into()
            }
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
        let calculated_atomic_fact: AtomicFact = match self {
            AtomicFact::NormalAtomicFact(inner) => NormalAtomicFact::new(
                inner.predicate.clone(),
                Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotNormalAtomicFact(inner) => NotNormalAtomicFact::new(
                inner.predicate.clone(),
                Self::body_vec_after_calculate_each_calculable_arg(&inner.body),
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::EqualFact(inner) => EqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotEqualFact(inner) => NotEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::LessFact(inner) => LessFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotLessFact(inner) => NotLessFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::GreaterFact(inner) => GreaterFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotGreaterFact(inner) => NotGreaterFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::LessEqualFact(inner) => LessEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotLessEqualFact(inner) => NotLessEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::GreaterEqualFact(inner) => GreaterEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotGreaterEqualFact(inner) => NotGreaterEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsSetFact(inner) => IsSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsSetFact(inner) => NotIsSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsNonemptySetFact(inner) => IsNonemptySetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsNonemptySetFact(inner) => NotIsNonemptySetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsFiniteSetFact(inner) => IsFiniteSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsFiniteSetFact(inner) => NotIsFiniteSetFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::InFact(inner) => InFact::new(
                inner
                    .element
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotInFact(inner) => NotInFact::new(
                inner
                    .element
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsCartFact(inner) => IsCartFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsCartFact(inner) => NotIsCartFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::IsTupleFact(inner) => IsTupleFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotIsTupleFact(inner) => NotIsTupleFact::new(
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::SubsetFact(inner) => SubsetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotSubsetFact(inner) => NotSubsetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::SupersetFact(inner) => SupersetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotSupersetFact(inner) => NotSupersetFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::RestrictFact(inner) => RestrictFact::new(
                inner
                    .obj
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .obj_can_restrict_to_fn_set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::NotRestrictFact(inner) => NotRestrictFact::new(
                inner
                    .obj
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .obj_cannot_restrict_to_fn_set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::FnEqualInFact(inner) => FnEqualInFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .set
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
            AtomicFact::FnEqualFact(inner) => FnEqualFact::new(
                inner
                    .left
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner
                    .right
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0,
                inner.line_file.clone(),
            )
            .into(),
        };
        let any_argument_replaced = calculated_atomic_fact.to_string() != self.to_string();
        (calculated_atomic_fact, any_argument_replaced)
    }
}

impl From<NormalAtomicFact> for AtomicFact {
    fn from(f: NormalAtomicFact) -> Self {
        AtomicFact::NormalAtomicFact(f)
    }
}

impl From<EqualFact> for AtomicFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::EqualFact(f)
    }
}

impl From<LessFact> for AtomicFact {
    fn from(f: LessFact) -> Self {
        AtomicFact::LessFact(f)
    }
}

impl From<GreaterFact> for AtomicFact {
    fn from(f: GreaterFact) -> Self {
        AtomicFact::GreaterFact(f)
    }
}

impl From<LessEqualFact> for AtomicFact {
    fn from(f: LessEqualFact) -> Self {
        AtomicFact::LessEqualFact(f)
    }
}

impl From<GreaterEqualFact> for AtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::GreaterEqualFact(f)
    }
}

impl From<IsSetFact> for AtomicFact {
    fn from(f: IsSetFact) -> Self {
        AtomicFact::IsSetFact(f)
    }
}

impl From<IsNonemptySetFact> for AtomicFact {
    fn from(f: IsNonemptySetFact) -> Self {
        AtomicFact::IsNonemptySetFact(f)
    }
}

impl From<IsFiniteSetFact> for AtomicFact {
    fn from(f: IsFiniteSetFact) -> Self {
        AtomicFact::IsFiniteSetFact(f)
    }
}

impl From<InFact> for AtomicFact {
    fn from(f: InFact) -> Self {
        AtomicFact::InFact(f)
    }
}

impl From<IsCartFact> for AtomicFact {
    fn from(f: IsCartFact) -> Self {
        AtomicFact::IsCartFact(f)
    }
}

impl From<IsTupleFact> for AtomicFact {
    fn from(f: IsTupleFact) -> Self {
        AtomicFact::IsTupleFact(f)
    }
}

impl From<SubsetFact> for AtomicFact {
    fn from(f: SubsetFact) -> Self {
        AtomicFact::SubsetFact(f)
    }
}

impl From<SupersetFact> for AtomicFact {
    fn from(f: SupersetFact) -> Self {
        AtomicFact::SupersetFact(f)
    }
}

impl From<RestrictFact> for AtomicFact {
    fn from(f: RestrictFact) -> Self {
        AtomicFact::RestrictFact(f)
    }
}

impl From<NotRestrictFact> for AtomicFact {
    fn from(f: NotRestrictFact) -> Self {
        AtomicFact::NotRestrictFact(f)
    }
}

impl From<NotNormalAtomicFact> for AtomicFact {
    fn from(f: NotNormalAtomicFact) -> Self {
        AtomicFact::NotNormalAtomicFact(f)
    }
}

impl From<NotEqualFact> for AtomicFact {
    fn from(f: NotEqualFact) -> Self {
        AtomicFact::NotEqualFact(f)
    }
}

impl From<NotLessFact> for AtomicFact {
    fn from(f: NotLessFact) -> Self {
        AtomicFact::NotLessFact(f)
    }
}

impl From<NotGreaterFact> for AtomicFact {
    fn from(f: NotGreaterFact) -> Self {
        AtomicFact::NotGreaterFact(f)
    }
}

impl From<NotLessEqualFact> for AtomicFact {
    fn from(f: NotLessEqualFact) -> Self {
        AtomicFact::NotLessEqualFact(f)
    }
}

impl From<NotGreaterEqualFact> for AtomicFact {
    fn from(f: NotGreaterEqualFact) -> Self {
        AtomicFact::NotGreaterEqualFact(f)
    }
}

impl From<NotIsSetFact> for AtomicFact {
    fn from(f: NotIsSetFact) -> Self {
        AtomicFact::NotIsSetFact(f)
    }
}

impl From<NotIsNonemptySetFact> for AtomicFact {
    fn from(f: NotIsNonemptySetFact) -> Self {
        AtomicFact::NotIsNonemptySetFact(f)
    }
}

impl From<NotIsFiniteSetFact> for AtomicFact {
    fn from(f: NotIsFiniteSetFact) -> Self {
        AtomicFact::NotIsFiniteSetFact(f)
    }
}

impl From<NotInFact> for AtomicFact {
    fn from(f: NotInFact) -> Self {
        AtomicFact::NotInFact(f)
    }
}

impl From<NotIsCartFact> for AtomicFact {
    fn from(f: NotIsCartFact) -> Self {
        AtomicFact::NotIsCartFact(f)
    }
}

impl From<NotIsTupleFact> for AtomicFact {
    fn from(f: NotIsTupleFact) -> Self {
        AtomicFact::NotIsTupleFact(f)
    }
}

impl From<NotSubsetFact> for AtomicFact {
    fn from(f: NotSubsetFact) -> Self {
        AtomicFact::NotSubsetFact(f)
    }
}

impl From<NotSupersetFact> for AtomicFact {
    fn from(f: NotSupersetFact) -> Self {
        AtomicFact::NotSupersetFact(f)
    }
}

impl From<FnEqualInFact> for AtomicFact {
    fn from(f: FnEqualInFact) -> Self {
        AtomicFact::FnEqualInFact(f)
    }
}

impl From<FnEqualFact> for AtomicFact {
    fn from(f: FnEqualFact) -> Self {
        AtomicFact::FnEqualFact(f)
    }
}

impl From<NormalAtomicFact> for Fact {
    fn from(f: NormalAtomicFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<EqualFact> for Fact {
    fn from(f: EqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<LessFact> for Fact {
    fn from(f: LessFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<GreaterFact> for Fact {
    fn from(f: GreaterFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<LessEqualFact> for Fact {
    fn from(f: LessEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<GreaterEqualFact> for Fact {
    fn from(f: GreaterEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsSetFact> for Fact {
    fn from(f: IsSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsNonemptySetFact> for Fact {
    fn from(f: IsNonemptySetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsFiniteSetFact> for Fact {
    fn from(f: IsFiniteSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<InFact> for Fact {
    fn from(f: InFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsCartFact> for Fact {
    fn from(f: IsCartFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsTupleFact> for Fact {
    fn from(f: IsTupleFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<SubsetFact> for Fact {
    fn from(f: SubsetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<SupersetFact> for Fact {
    fn from(f: SupersetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<RestrictFact> for Fact {
    fn from(f: RestrictFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotRestrictFact> for Fact {
    fn from(f: NotRestrictFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<FnEqualInFact> for Fact {
    fn from(f: FnEqualInFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<FnEqualFact> for Fact {
    fn from(f: FnEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotNormalAtomicFact> for Fact {
    fn from(f: NotNormalAtomicFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotEqualFact> for Fact {
    fn from(f: NotEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotLessFact> for Fact {
    fn from(f: NotLessFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotGreaterFact> for Fact {
    fn from(f: NotGreaterFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotLessEqualFact> for Fact {
    fn from(f: NotLessEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotGreaterEqualFact> for Fact {
    fn from(f: NotGreaterEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsSetFact> for Fact {
    fn from(f: NotIsSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsNonemptySetFact> for Fact {
    fn from(f: NotIsNonemptySetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsFiniteSetFact> for Fact {
    fn from(f: NotIsFiniteSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotInFact> for Fact {
    fn from(f: NotInFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsCartFact> for Fact {
    fn from(f: NotIsCartFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsTupleFact> for Fact {
    fn from(f: NotIsTupleFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotSubsetFact> for Fact {
    fn from(f: NotSubsetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotSupersetFact> for Fact {
    fn from(f: NotSupersetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
