use super::atom_obj::AtomObj;
use super::fn_set::{AnonymousFn, FnSet, FnSetBody};
use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Obj {
    Atom(AtomObj),
    FnObj(FnObj),
    Number(Number),
    ImaginaryUnit(ImaginaryUnit),
    EulerNumber(EulerNumber),
    Pi(Pi),
    Add(Add),
    Sub(Sub),
    Mul(Mul),
    Div(Div),
    Mod(Mod),
    Gcd(Gcd),
    Lcm(Lcm),
    Floor(Floor),
    Ceil(Ceil),
    Min(Min),
    Max(Max),
    Exp(Exp),
    Ln(Ln),
    Sign(Sign),
    Factorial(Factorial),
    Pow(Pow),
    Abs(Abs),
    Sin(Sin),
    Cos(Cos),
    Tan(Tan),
    Cot(Cot),
    RealPart(RealPart),
    ImaginaryPart(ImaginaryPart),
    ComplexAbs(ComplexAbs),
    Sqrt(Sqrt),
    Log(Log),
    Union(Union),
    Intersect(Intersect),
    SetMinus(SetMinus),
    SetDiff(SetDiff),
    BigUnion(BigUnion),
    BigIntersect(BigIntersect),
    PowerSet(PowerSet),
    GeneralCart(GeneralCart),
    ListSet(ListSet),
    SetBuilder(SetBuilder),
    FnSet(FnSet),
    AnonymousFn(AnonymousFn),
    Cart(Cart),
    CartDim(CartDim),
    Proj(Proj),
    TupleDim(TupleDim),
    Tuple(Tuple),
    FiniteSetSize(FiniteSetSize),
    FiniteSetMax(FiniteSetMax),
    FiniteSetMin(FiniteSetMin),
    FnRange(FnRange),
    Replacement(Replacement),
    Sum(Sum),
    SumOfFiniteSet(SumOfFiniteSet),
    Product(Product),
    ProductOfFiniteSet(ProductOfFiniteSet),
    Reduce(Reduce),
    FiniteSetReduce(FiniteSetReduce),
    Range(Range),
    ClosedRange(ClosedRange),
    FiniteSeqSet(FiniteSeqSet),
    SeqSet(SeqSet),
    FiniteSeqListObj(FiniteSeqListObj),
    ObjAtIndex(ObjAtIndex),
    StandardSet(StandardSet),
    MatrixSet(MatrixSet),
    MatrixListObj(MatrixListObj),
    MatrixAdd(MatrixAdd),
    MatrixSub(MatrixSub),
    MatrixMul(MatrixMul),
    MatrixScalarMul(MatrixScalarMul),
    MatrixPow(MatrixPow),
    StructObj(StructObj),
    ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
    OneSideInfinityIntervalObj(OneSideInfinityIntervalObj),
    IntervalObj(IntervalObj),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ObjKind {
    Atom = 0,
    FnObj = 1,
    Number = 2,
    Add = 3,
    Sub = 4,
    Mul = 5,
    Div = 6,
    Mod = 7,
    Pow = 8,
    Abs = 9,
    Sqrt = 10,
    Log = 11,
    FiniteSetMax = 12,
    FiniteSetMin = 13,
    Union = 14,
    Intersect = 15,
    SetMinus = 16,
    SetDiff = 17,
    BigUnion = 18,
    BigIntersect = 19,
    PowerSet = 20,
    ListSet = 21,
    SetBuilder = 22,
    FnSet = 23,
    AnonymousFn = 24,
    Cart = 25,
    CartDim = 26,
    Proj = 27,
    TupleDim = 28,
    Tuple = 29,
    FiniteSetSize = 30,
    Sum = 31,
    SumOfFiniteSet = 32,
    Product = 33,
    ProductOfFiniteSet = 34,
    Range = 35,
    ClosedRange = 36,
    FiniteSeqSet = 37,
    SeqSet = 38,
    FiniteSeqListObj = 39,
    ObjAtIndex = 40,
    StandardSet = 41,
    MatrixSet = 42,
    MatrixListObj = 43,
    MatrixAdd = 44,
    MatrixSub = 45,
    MatrixMul = 46,
    MatrixScalarMul = 47,
    MatrixPow = 48,
    StructObj = 49,
    ObjAsStructInstanceWithFieldAccess = 50,
    InstantiatedTemplateObj = 51,
    OneSideInfinityIntervalObj = 52,
    IntervalObj = 53,
    Identifier = 54,
    IdentifierWithMod = 55,
    ForallFreeParam = 56,
    DefHeaderFreeParam = 57,
    ExistFreeParam = 58,
    SetBuilderFreeParam = 59,
    FnSetFreeParam = 60,
    ByInducFreeParam = 61,
    DefAlgoFreeParam = 62,
    DefStructFieldFreeParam = 63,
    FnRange = 64,
    Replacement = 66,
    TupleIndexFreeParam = 67,
    CartIndexFreeParam = 68,
    GeneralCart = 69,
    ImaginaryUnit = 70,
    RealPart = 71,
    ImaginaryPart = 72,
    ComplexAbs = 73,
    EulerNumber = 74,
    Pi = 75,
    Sin = 76,
    Cos = 77,
    Tan = 78,
    Cot = 79,
    Gcd = 80,
    Lcm = 81,
    Floor = 82,
    Ceil = 83,
    Min = 84,
    Max = 85,
    Exp = 86,
    Ln = 87,
    Sign = 88,
    Factorial = 89,
    Reduce = 90,
    FiniteSetReduce = 91,
}

impl ObjKind {
    pub fn as_u8(self) -> u8 {
        self as u8
    }
}

#[derive(Clone)]
pub enum OneSideInfinityIntervalObj {
    LeftOpen(OneSideInfinityIntervalObjStruct),
    LeftClosed(OneSideInfinityIntervalObjStruct),
    RightOpen(OneSideInfinityIntervalObjStruct),
    RightClosed(OneSideInfinityIntervalObjStruct),
}

#[derive(Clone)]
pub struct OneSideInfinityIntervalObjStruct {
    pub start: Box<Obj>,
}

impl OneSideInfinityIntervalObjStruct {
    pub fn new(start: Obj) -> Self {
        OneSideInfinityIntervalObjStruct {
            start: Box::new(start),
        }
    }
}

impl OneSideInfinityIntervalObj {
    pub fn new_left_open(start: Obj) -> Self {
        OneSideInfinityIntervalObj::LeftOpen(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn new_left_closed(start: Obj) -> Self {
        OneSideInfinityIntervalObj::LeftClosed(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn new_right_open(start: Obj) -> Self {
        OneSideInfinityIntervalObj::RightOpen(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn new_right_closed(start: Obj) -> Self {
        OneSideInfinityIntervalObj::RightClosed(OneSideInfinityIntervalObjStruct::new(start))
    }

    pub fn interval_struct(&self) -> &OneSideInfinityIntervalObjStruct {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(x)
            | OneSideInfinityIntervalObj::LeftClosed(x)
            | OneSideInfinityIntervalObj::RightOpen(x)
            | OneSideInfinityIntervalObj::RightClosed(x) => x,
        }
    }

    pub fn start(&self) -> &Obj {
        self.interval_struct().start.as_ref()
    }

    pub fn left_closed(&self) -> bool {
        matches!(self, OneSideInfinityIntervalObj::LeftClosed(_))
    }

    pub fn right_closed(&self) -> bool {
        matches!(self, OneSideInfinityIntervalObj::RightClosed(_))
    }

    pub fn left_bounded(&self) -> bool {
        matches!(
            self,
            OneSideInfinityIntervalObj::LeftOpen(_) | OneSideInfinityIntervalObj::LeftClosed(_)
        )
    }

    pub fn same_kind_as(&self, other: &OneSideInfinityIntervalObj) -> bool {
        matches!(
            (self, other),
            (
                OneSideInfinityIntervalObj::LeftOpen(_),
                OneSideInfinityIntervalObj::LeftOpen(_)
            ) | (
                OneSideInfinityIntervalObj::LeftClosed(_),
                OneSideInfinityIntervalObj::LeftClosed(_)
            ) | (
                OneSideInfinityIntervalObj::RightOpen(_),
                OneSideInfinityIntervalObj::RightOpen(_)
            ) | (
                OneSideInfinityIntervalObj::RightClosed(_),
                OneSideInfinityIntervalObj::RightClosed(_)
            )
        )
    }
}

#[derive(Clone)]
pub enum IntervalObj {
    LeftOpenRightOpen(IntervalObjStruct),
    LeftOpenRightClosed(IntervalObjStruct),
    LeftClosedRightOpen(IntervalObjStruct),
    LeftClosedRightClosed(IntervalObjStruct),
}

#[derive(Clone)]
pub struct IntervalObjStruct {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

impl IntervalObjStruct {
    pub fn new(start: Obj, end: Obj) -> Self {
        IntervalObjStruct {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl IntervalObj {
    pub fn new_left_open_right_open(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftOpenRightOpen(IntervalObjStruct::new(start, end))
    }

    pub fn new_left_open_right_closed(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftOpenRightClosed(IntervalObjStruct::new(start, end))
    }

    pub fn new_left_closed_right_open(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftClosedRightOpen(IntervalObjStruct::new(start, end))
    }

    pub fn new_left_closed_right_closed(start: Obj, end: Obj) -> Self {
        IntervalObj::LeftClosedRightClosed(IntervalObjStruct::new(start, end))
    }

    pub fn interval_struct(&self) -> &IntervalObjStruct {
        match self {
            IntervalObj::LeftOpenRightOpen(x)
            | IntervalObj::LeftOpenRightClosed(x)
            | IntervalObj::LeftClosedRightOpen(x)
            | IntervalObj::LeftClosedRightClosed(x) => x,
        }
    }

    pub fn start(&self) -> &Obj {
        self.interval_struct().start.as_ref()
    }

    pub fn end(&self) -> &Obj {
        self.interval_struct().end.as_ref()
    }

    pub fn left_closed(&self) -> bool {
        matches!(
            self,
            IntervalObj::LeftClosedRightOpen(_) | IntervalObj::LeftClosedRightClosed(_)
        )
    }

    pub fn right_closed(&self) -> bool {
        matches!(
            self,
            IntervalObj::LeftOpenRightClosed(_) | IntervalObj::LeftClosedRightClosed(_)
        )
    }
}

#[derive(Clone)]
pub struct Sqrt {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct StructObj {
    pub name: AtomicName,
    pub params: Vec<Obj>,
}

#[derive(Clone)]
pub struct ObjAsStructInstanceWithFieldAccess {
    pub struct_obj: Box<StructObj>,
    pub obj: Box<Obj>,
    pub field_name: String,
}

#[derive(Clone)]
pub struct InstantiatedTemplateObj {
    pub template_name: AtomicName,
    pub args: Vec<Obj>,
    pub symbol: SymbolRef,
}

impl StructObj {
    pub fn new(name: AtomicName, params: Vec<Obj>) -> Self {
        StructObj { name, params }
    }
}

impl ObjAsStructInstanceWithFieldAccess {
    pub fn new(struct_obj: StructObj, obj: Obj, field_name: String) -> Self {
        ObjAsStructInstanceWithFieldAccess {
            struct_obj: Box::new(struct_obj),
            obj: Box::new(obj),
            field_name,
        }
    }
}

impl InstantiatedTemplateObj {
    pub fn new(template_name: AtomicName, args: Vec<Obj>, symbol: SymbolRef) -> Self {
        InstantiatedTemplateObj {
            template_name,
            args,
            symbol,
        }
    }

    pub fn surface_name(&self) -> String {
        format!(
            "{}{}{}{}{}",
            TEMPLATE_INSTANCE_PREFIX,
            self.template_name,
            LESS,
            vec_to_string_join_by_comma(&self.args),
            GREATER
        )
    }

    pub(crate) fn declaration_binding(&self) -> SymbolBinding {
        SymbolBinding::new(
            self.symbol.id(),
            self.surface_name(),
            self.symbol.display_name().to_string(),
        )
    }
}

#[derive(Clone)]
pub struct Sum {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct SumOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct Product {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct ProductOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

/// An ascending left fold over the closed integer interval `[start, end]`.
/// The empty interval evaluates to `seed`.
#[derive(Clone)]
pub struct Reduce {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

/// An order-independent fold over a finite set. Well-definedness requires
/// `op` to be associative and commutative on its carrier.
#[derive(Clone)]
pub struct FiniteSetReduce {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixAdd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixSub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixMul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixScalarMul {
    pub scalar: Box<Obj>,
    pub matrix: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixPow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixSet {
    pub set: Box<Obj>,
    pub row_len: Box<Obj>,
    pub col_len: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixListObj {
    pub rows: Vec<Vec<Box<Obj>>>,
}

#[derive(Clone)]
pub struct ObjAtIndex {
    pub obj: Box<Obj>,
    pub index: Box<Obj>,
}

#[derive(Clone)]
pub struct PowerSet {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct Range {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

#[derive(Clone)]
pub struct ClosedRange {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

/// Set of functions `fn(x N+: x <= n) s` (Lit surface syntax: keyword `finite_seq(s, n)`).
#[derive(Clone)]
pub struct FiniteSeqSet {
    pub set: Box<Obj>,
    pub n: Box<Obj>,
}

/// `seq(s)` — functions `fn(x N+) s` (no length bound; surface: keyword `seq(s)`).
#[derive(Clone)]
pub struct SeqSet {
    pub set: Box<Obj>,
}

/// Literal `[a, b, ...]` as a finite sequence value (for membership in `finite_seq(s, n)`).
#[derive(Clone)]
pub struct FiniteSeqListObj {
    pub objs: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct FiniteSetSize {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct FiniteSetMax {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct FiniteSetMin {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct FnRange {
    pub function: Box<Obj>,
}

#[derive(Clone)]
pub struct Replacement {
    pub prop_name: AtomicName,
    pub source_set: Box<Obj>,
}

#[derive(Clone)]
pub struct Tuple {
    pub args: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct TupleDim {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct CartDim {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct Proj {
    pub set: Box<Obj>,
    pub dim: Box<Obj>,
}

#[derive(Clone)]
pub struct FnObj {
    pub head: Box<FnObjHead>,
    pub body: Vec<Vec<Box<Obj>>>,
}

#[derive(Clone)]
pub struct Number {
    pub normalized_value: String,
}

#[derive(Clone)]
pub struct ImaginaryUnit;

#[derive(Clone)]
pub struct EulerNumber;

#[derive(Clone)]
pub struct Pi;

#[derive(Clone)]
pub struct Add {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Div {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Mod {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Gcd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Lcm {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Floor {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Ceil {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Min {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Max {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

/// Real exponential `e^x`.
#[derive(Clone)]
pub struct Exp {
    pub arg: Box<Obj>,
}

/// Natural logarithm on the positive reals.
#[derive(Clone)]
pub struct Ln {
    pub arg: Box<Obj>,
}

/// Real sign function with values `-1`, `0`, and `1`.
#[derive(Clone)]
pub struct Sign {
    pub arg: Box<Obj>,
}

/// Natural-number factorial.
#[derive(Clone)]
pub struct Factorial {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

#[derive(Clone)]
pub struct Abs {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Sin {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Cos {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Tan {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Cot {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct RealPart {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct ImaginaryPart {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct ComplexAbs {
    pub arg: Box<Obj>,
}

/// Real logarithm `log(base, x)` with `base > 0`, `base != 1`, `x > 0`.
#[derive(Clone)]
pub struct Log {
    pub base: Box<Obj>,
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Union {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Intersect {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct SetMinus {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct SetDiff {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct BigUnion {
    pub left: Box<Obj>,
}

#[derive(Clone)]
pub struct BigIntersect {
    pub left: Box<Obj>,
}

#[derive(Clone)]
pub struct ListSet {
    pub list: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct SetBuilder {
    pub param: String,
    pub param_binding: SymbolBinding,
    pub param_set: Box<Obj>,
    pub facts: Vec<ExistBodyFact>,
}

#[derive(Clone)]
pub struct GeneralCart {
    pub index_set: Box<Obj>,
    pub family_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

#[derive(Clone)]
pub struct Cart {
    pub args: Vec<Box<Obj>>,
}

impl ObjAtIndex {
    pub fn new(obj: Obj, index: Obj) -> Self {
        ObjAtIndex {
            obj: Box::new(obj),
            index: Box::new(index),
        }
    }
}

impl FnObj {
    pub fn new(head: FnObjHead, body: Vec<Vec<Box<Obj>>>) -> Self {
        FnObj {
            head: Box::new(head),
            body,
        }
    }

    pub(crate) fn prefix_obj(&self, number_of_body_groups_to_keep: usize) -> Obj {
        if number_of_body_groups_to_keep == 0 {
            return self.head.as_ref().clone().into();
        }

        FnObj::new(
            self.head.as_ref().clone(),
            self.body[..number_of_body_groups_to_keep].to_vec(),
        )
        .into()
    }
}

impl Number {
    pub fn new(value: String) -> Self {
        Number {
            normalized_value: normalize_decimal_number_string(&value),
        }
    }
}

impl ImaginaryUnit {
    pub fn new() -> Self {
        ImaginaryUnit
    }
}

impl EulerNumber {
    pub fn new() -> Self {
        EulerNumber
    }
}

impl Pi {
    pub fn new() -> Self {
        Pi
    }
}

impl Add {
    pub fn new(left: Obj, right: Obj) -> Self {
        Add {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Sub {
    pub fn new(left: Obj, right: Obj) -> Self {
        Sub {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Mul {
    pub fn new(left: Obj, right: Obj) -> Self {
        Mul {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Div {
    pub fn new(left: Obj, right: Obj) -> Self {
        Div {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Mod {
    pub fn new(left: Obj, right: Obj) -> Self {
        Mod {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Gcd {
    pub fn new(left: Obj, right: Obj) -> Self {
        Gcd {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Lcm {
    pub fn new(left: Obj, right: Obj) -> Self {
        Lcm {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Floor {
    pub fn new(arg: Obj) -> Self {
        Floor { arg: Box::new(arg) }
    }
}

impl Ceil {
    pub fn new(arg: Obj) -> Self {
        Ceil { arg: Box::new(arg) }
    }
}

impl Min {
    pub fn new(left: Obj, right: Obj) -> Self {
        Min {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Max {
    pub fn new(left: Obj, right: Obj) -> Self {
        Max {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Exp {
    pub fn new(arg: Obj) -> Self {
        Exp { arg: Box::new(arg) }
    }
}

impl Ln {
    pub fn new(arg: Obj) -> Self {
        Ln { arg: Box::new(arg) }
    }
}

impl Sign {
    pub fn new(arg: Obj) -> Self {
        Sign { arg: Box::new(arg) }
    }
}

impl Factorial {
    pub fn new(arg: Obj) -> Self {
        Factorial { arg: Box::new(arg) }
    }
}

impl Pow {
    pub fn new(base: Obj, exponent: Obj) -> Self {
        Pow {
            base: Box::new(base),
            exponent: Box::new(exponent),
        }
    }
}

impl Abs {
    pub fn new(arg: Obj) -> Self {
        Abs { arg: Box::new(arg) }
    }
}

impl Sin {
    pub fn new(arg: Obj) -> Self {
        Sin { arg: Box::new(arg) }
    }
}

impl Cos {
    pub fn new(arg: Obj) -> Self {
        Cos { arg: Box::new(arg) }
    }
}

impl Tan {
    pub fn new(arg: Obj) -> Self {
        Tan { arg: Box::new(arg) }
    }
}

impl Cot {
    pub fn new(arg: Obj) -> Self {
        Cot { arg: Box::new(arg) }
    }
}

impl RealPart {
    pub fn new(arg: Obj) -> Self {
        RealPart { arg: Box::new(arg) }
    }
}

impl ImaginaryPart {
    pub fn new(arg: Obj) -> Self {
        ImaginaryPart { arg: Box::new(arg) }
    }
}

impl ComplexAbs {
    pub fn new(arg: Obj) -> Self {
        ComplexAbs { arg: Box::new(arg) }
    }
}

impl Sqrt {
    pub fn new(arg: Obj) -> Self {
        Sqrt { arg: Box::new(arg) }
    }
}

impl Log {
    pub fn new(base: Obj, arg: Obj) -> Self {
        Log {
            base: Box::new(base),
            arg: Box::new(arg),
        }
    }
}

impl Union {
    pub fn new(left: Obj, right: Obj) -> Self {
        Union {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Intersect {
    pub fn new(left: Obj, right: Obj) -> Self {
        Intersect {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl SetMinus {
    pub fn new(left: Obj, right: Obj) -> Self {
        SetMinus {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl SetDiff {
    pub fn new(left: Obj, right: Obj) -> Self {
        SetDiff {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl BigUnion {
    pub fn new(left: Obj) -> Self {
        BigUnion {
            left: Box::new(left),
        }
    }
}

impl BigIntersect {
    pub fn new(left: Obj) -> Self {
        BigIntersect {
            left: Box::new(left),
        }
    }
}

impl ListSet {
    pub fn new(list: Vec<Obj>) -> Self {
        ListSet {
            list: list.into_iter().map(Box::new).collect(),
        }
    }
}

impl SetBuilder {
    pub fn new(
        param_binding: SymbolBinding,
        param_set: Obj,
        facts: Vec<ExistBodyFact>,
    ) -> Result<Self, RuntimeError> {
        let set_builder = SetBuilder {
            param: param_binding.name().to_string(),
            param_binding,
            param_set: Box::new(param_set),
            facts,
        };
        check_set_builder_has_no_duplicate_set_builder_free_parameter(&set_builder)?;
        Ok(set_builder)
    }
}

impl GeneralCart {
    pub fn new(index_set: Obj, family_set: Obj, family_fn: Obj) -> Self {
        GeneralCart {
            index_set: Box::new(index_set),
            family_set: Box::new(family_set),
            family_fn: Box::new(family_fn),
        }
    }
}

impl PowerSet {
    pub fn new(set: Obj) -> Self {
        PowerSet { set: Box::new(set) }
    }
}

impl CartDim {
    pub fn new(set: Obj) -> Self {
        CartDim { set: Box::new(set) }
    }
}

impl Proj {
    pub fn new(set: Obj, dim: Obj) -> Self {
        Proj {
            set: Box::new(set),
            dim: Box::new(dim),
        }
    }
}

impl TupleDim {
    pub fn new(dim: Obj) -> Self {
        TupleDim { arg: Box::new(dim) }
    }
}

impl Cart {
    pub fn new(args: Vec<Obj>) -> Self {
        let n = args.len();
        if n < 2 {
            panic!("Cart::new: expected at least 2 factors, got {n}");
        }
        Cart {
            args: args.into_iter().map(Box::new).collect(),
        }
    }
}

impl Tuple {
    pub fn new(elements: Vec<Obj>) -> Self {
        let n = elements.len();
        if n < 2 {
            panic!("Tuple::new: expected at least 2 elements, got {n}");
        }
        Tuple {
            args: elements.into_iter().map(Box::new).collect(),
        }
    }
}

impl FiniteSetSize {
    pub fn new(set: Obj) -> Self {
        FiniteSetSize { set: Box::new(set) }
    }
}

impl FiniteSetMax {
    pub fn new(set: Obj) -> Self {
        FiniteSetMax { set: Box::new(set) }
    }
}

impl FiniteSetMin {
    pub fn new(set: Obj) -> Self {
        FiniteSetMin { set: Box::new(set) }
    }
}

impl FnRange {
    pub fn new(function: Obj) -> Self {
        FnRange {
            function: Box::new(function),
        }
    }
}

impl Replacement {
    pub fn new(prop_name: AtomicName, source_set: Obj) -> Self {
        Replacement {
            prop_name,
            source_set: Box::new(source_set),
        }
    }
}

impl Range {
    pub fn new(start: Obj, end: Obj) -> Self {
        Range {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl ClosedRange {
    pub fn new(start: Obj, end: Obj) -> Self {
        ClosedRange {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl FiniteSeqSet {
    pub fn new(set: Obj, n: Obj) -> Self {
        FiniteSeqSet {
            set: Box::new(set),
            n: Box::new(n),
        }
    }
}

impl SeqSet {
    pub fn new(set: Obj) -> Self {
        SeqSet { set: Box::new(set) }
    }
}

impl FiniteSeqListObj {
    pub fn new(objs: Vec<Obj>) -> Self {
        FiniteSeqListObj {
            objs: objs.into_iter().map(Box::new).collect(),
        }
    }
}

impl MatrixSet {
    pub fn new(set: Obj, row_len: Obj, col_len: Obj) -> Self {
        MatrixSet {
            set: Box::new(set),
            row_len: Box::new(row_len),
            col_len: Box::new(col_len),
        }
    }
}

impl MatrixListObj {
    pub fn new(rows: Vec<Vec<Obj>>) -> Self {
        MatrixListObj {
            rows: rows
                .into_iter()
                .map(|row| row.into_iter().map(Box::new).collect())
                .collect(),
        }
    }
}

impl MatrixAdd {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixAdd {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixSub {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixSub {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixMul {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixMul {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixScalarMul {
    pub fn new(scalar: Obj, matrix: Obj) -> Self {
        MatrixScalarMul {
            scalar: Box::new(scalar),
            matrix: Box::new(matrix),
        }
    }
}

impl MatrixPow {
    pub fn new(base: Obj, exponent: Obj) -> Self {
        MatrixPow {
            base: Box::new(base),
            exponent: Box::new(exponent),
        }
    }
}

impl Sum {
    pub fn new(start: Obj, end: Obj, func: Obj) -> Self {
        Sum {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
        }
    }
}

impl SumOfFiniteSet {
    pub fn new(set: Obj, func: Obj) -> Self {
        SumOfFiniteSet {
            set: Box::new(set),
            func: Box::new(func),
        }
    }
}

impl Product {
    pub fn new(start: Obj, end: Obj, func: Obj) -> Self {
        Product {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
        }
    }
}

impl ProductOfFiniteSet {
    pub fn new(set: Obj, func: Obj) -> Self {
        ProductOfFiniteSet {
            set: Box::new(set),
            func: Box::new(func),
        }
    }
}

impl Reduce {
    pub fn new(start: Obj, end: Obj, func: Obj, op: Obj, seed: Obj) -> Self {
        Reduce {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
            op: Box::new(op),
            seed: Box::new(seed),
        }
    }
}

impl FiniteSetReduce {
    pub fn new(set: Obj, func: Obj, op: Obj, seed: Obj) -> Self {
        FiniteSetReduce {
            set: Box::new(set),
            func: Box::new(func),
            op: Box::new(op),
            seed: Box::new(seed),
        }
    }
}

/// Arithmetic precedence for display; smaller numbers bind tighter.
fn precedence(o: &Obj) -> u8 {
    match o {
        Obj::Add(_) | Obj::Sub(_) => 3,
        Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::MatrixScalarMul(_) => 2,
        Obj::Pow(_)
        | Obj::Abs(_)
        | Obj::Sin(_)
        | Obj::Cos(_)
        | Obj::Tan(_)
        | Obj::Cot(_)
        | Obj::RealPart(_)
        | Obj::ImaginaryPart(_)
        | Obj::ComplexAbs(_)
        | Obj::Sqrt(_)
        | Obj::Log(_)
        | Obj::Lcm(_)
        | Obj::Floor(_)
        | Obj::Ceil(_)
        | Obj::Min(_)
        | Obj::Max(_)
        | Obj::Exp(_)
        | Obj::Ln(_)
        | Obj::Sign(_)
        | Obj::Factorial(_)
        | Obj::MatrixAdd(_)
        | Obj::MatrixSub(_)
        | Obj::MatrixMul(_)
        | Obj::MatrixPow(_) => 1,
        _ => 0,
    }
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.fmt_with_precedence(f, 0)
    }
}

impl Obj {
    pub fn kind(&self) -> ObjKind {
        match self {
            Obj::Atom(atom) => match atom {
                AtomObj::Identifier(_) => ObjKind::Identifier,
                AtomObj::IdentifierWithMod(_) => ObjKind::IdentifierWithMod,
                AtomObj::Forall(_) => ObjKind::ForallFreeParam,
                AtomObj::Def(_) => ObjKind::DefHeaderFreeParam,
                AtomObj::Exist(_) => ObjKind::ExistFreeParam,
                AtomObj::SetBuilder(_) => ObjKind::SetBuilderFreeParam,
                AtomObj::FnSet(_) => ObjKind::FnSetFreeParam,
                AtomObj::Induc(_) => ObjKind::ByInducFreeParam,
                AtomObj::DefAlgo(_) => ObjKind::DefAlgoFreeParam,
                AtomObj::DefStructField(_) => ObjKind::DefStructFieldFreeParam,
                AtomObj::TupleIndex(_) => ObjKind::TupleIndexFreeParam,
                AtomObj::CartIndex(_) => ObjKind::CartIndexFreeParam,
            },
            Obj::FnObj(_) => ObjKind::FnObj,
            Obj::Number(_) => ObjKind::Number,
            Obj::ImaginaryUnit(_) => ObjKind::ImaginaryUnit,
            Obj::EulerNumber(_) => ObjKind::EulerNumber,
            Obj::Pi(_) => ObjKind::Pi,
            Obj::Add(_) => ObjKind::Add,
            Obj::Sub(_) => ObjKind::Sub,
            Obj::Mul(_) => ObjKind::Mul,
            Obj::Div(_) => ObjKind::Div,
            Obj::Mod(_) => ObjKind::Mod,
            Obj::Gcd(_) => ObjKind::Gcd,
            Obj::Lcm(_) => ObjKind::Lcm,
            Obj::Floor(_) => ObjKind::Floor,
            Obj::Ceil(_) => ObjKind::Ceil,
            Obj::Min(_) => ObjKind::Min,
            Obj::Max(_) => ObjKind::Max,
            Obj::Exp(_) => ObjKind::Exp,
            Obj::Ln(_) => ObjKind::Ln,
            Obj::Sign(_) => ObjKind::Sign,
            Obj::Factorial(_) => ObjKind::Factorial,
            Obj::Pow(_) => ObjKind::Pow,
            Obj::Abs(_) => ObjKind::Abs,
            Obj::Sin(_) => ObjKind::Sin,
            Obj::Cos(_) => ObjKind::Cos,
            Obj::Tan(_) => ObjKind::Tan,
            Obj::Cot(_) => ObjKind::Cot,
            Obj::RealPart(_) => ObjKind::RealPart,
            Obj::ImaginaryPart(_) => ObjKind::ImaginaryPart,
            Obj::ComplexAbs(_) => ObjKind::ComplexAbs,
            Obj::Sqrt(_) => ObjKind::Sqrt,
            Obj::Log(_) => ObjKind::Log,
            Obj::Union(_) => ObjKind::Union,
            Obj::Intersect(_) => ObjKind::Intersect,
            Obj::SetMinus(_) => ObjKind::SetMinus,
            Obj::SetDiff(_) => ObjKind::SetDiff,
            Obj::BigUnion(_) => ObjKind::BigUnion,
            Obj::BigIntersect(_) => ObjKind::BigIntersect,
            Obj::PowerSet(_) => ObjKind::PowerSet,
            Obj::GeneralCart(_) => ObjKind::GeneralCart,
            Obj::ListSet(_) => ObjKind::ListSet,
            Obj::SetBuilder(_) => ObjKind::SetBuilder,
            Obj::FnSet(_) => ObjKind::FnSet,
            Obj::AnonymousFn(_) => ObjKind::AnonymousFn,
            Obj::Cart(_) => ObjKind::Cart,
            Obj::CartDim(_) => ObjKind::CartDim,
            Obj::Proj(_) => ObjKind::Proj,
            Obj::TupleDim(_) => ObjKind::TupleDim,
            Obj::Tuple(_) => ObjKind::Tuple,
            Obj::FiniteSetSize(_) => ObjKind::FiniteSetSize,
            Obj::FiniteSetMax(_) => ObjKind::FiniteSetMax,
            Obj::FiniteSetMin(_) => ObjKind::FiniteSetMin,
            Obj::FnRange(_) => ObjKind::FnRange,
            Obj::Replacement(_) => ObjKind::Replacement,
            Obj::Sum(_) => ObjKind::Sum,
            Obj::SumOfFiniteSet(_) => ObjKind::SumOfFiniteSet,
            Obj::Product(_) => ObjKind::Product,
            Obj::ProductOfFiniteSet(_) => ObjKind::ProductOfFiniteSet,
            Obj::Reduce(_) => ObjKind::Reduce,
            Obj::FiniteSetReduce(_) => ObjKind::FiniteSetReduce,
            Obj::Range(_) => ObjKind::Range,
            Obj::ClosedRange(_) => ObjKind::ClosedRange,
            Obj::FiniteSeqSet(_) => ObjKind::FiniteSeqSet,
            Obj::SeqSet(_) => ObjKind::SeqSet,
            Obj::FiniteSeqListObj(_) => ObjKind::FiniteSeqListObj,
            Obj::ObjAtIndex(_) => ObjKind::ObjAtIndex,
            Obj::StandardSet(_) => ObjKind::StandardSet,
            Obj::MatrixSet(_) => ObjKind::MatrixSet,
            Obj::MatrixListObj(_) => ObjKind::MatrixListObj,
            Obj::MatrixAdd(_) => ObjKind::MatrixAdd,
            Obj::MatrixSub(_) => ObjKind::MatrixSub,
            Obj::MatrixMul(_) => ObjKind::MatrixMul,
            Obj::MatrixScalarMul(_) => ObjKind::MatrixScalarMul,
            Obj::MatrixPow(_) => ObjKind::MatrixPow,
            Obj::StructObj(_) => ObjKind::StructObj,
            Obj::ObjAsStructInstanceWithFieldAccess(_) => {
                ObjKind::ObjAsStructInstanceWithFieldAccess
            }
            Obj::InstantiatedTemplateObj(_) => ObjKind::InstantiatedTemplateObj,
            Obj::OneSideInfinityIntervalObj(_) => ObjKind::OneSideInfinityIntervalObj,
            Obj::IntervalObj(_) => ObjKind::IntervalObj,
        }
    }

    pub fn kind_id(&self) -> u8 {
        self.kind().as_u8()
    }

    pub fn equality_in_forall_key_part(&self) -> (ObjKind, ObjOperatorString) {
        (self.kind(), self.obj_operator_string())
    }

    fn obj_operator_string(&self) -> ObjOperatorString {
        match self {
            Obj::FnObj(fn_obj) => fn_obj.head.to_string(),
            Obj::Add(_) => ADD.to_string(),
            Obj::Sub(_) => SUB.to_string(),
            Obj::Mul(_) => MUL.to_string(),
            Obj::Div(_) => DIV.to_string(),
            Obj::Mod(_) => MOD.to_string(),
            Obj::Gcd(_) => GCD.to_string(),
            Obj::Lcm(_) => LCM.to_string(),
            Obj::Floor(_) => FLOOR.to_string(),
            Obj::Ceil(_) => CEIL.to_string(),
            Obj::Min(_) => MIN.to_string(),
            Obj::Max(_) => MAX.to_string(),
            Obj::Exp(_) => EXP.to_string(),
            Obj::Ln(_) => LN.to_string(),
            Obj::Sign(_) => SIGN.to_string(),
            Obj::Factorial(_) => FACTORIAL.to_string(),
            Obj::Pow(_) => POW.to_string(),
            Obj::Abs(_) => ABS.to_string(),
            Obj::Sin(_) => SIN.to_string(),
            Obj::Cos(_) => COS.to_string(),
            Obj::Tan(_) => TAN.to_string(),
            Obj::Cot(_) => COT.to_string(),
            Obj::RealPart(_) => RE.to_string(),
            Obj::ImaginaryPart(_) => IMG.to_string(),
            Obj::ComplexAbs(_) => C_ABS.to_string(),
            Obj::Sqrt(_) => SQRT.to_string(),
            Obj::Log(_) => LOG.to_string(),
            Obj::Union(_) => UNION.to_string(),
            Obj::Intersect(_) => INTERSECT.to_string(),
            Obj::SetMinus(_) => SET_MINUS.to_string(),
            Obj::SetDiff(_) => SET_DIFF.to_string(),
            Obj::BigUnion(_) => BIG_UNION.to_string(),
            Obj::BigIntersect(_) => BIG_INTERSECT.to_string(),
            Obj::PowerSet(_) => POWER_SET.to_string(),
            Obj::GeneralCart(_) => GENERAL_CART.to_string(),
            Obj::Cart(_) => CART.to_string(),
            Obj::CartDim(_) => CART_DIM.to_string(),
            Obj::Proj(_) => PROJ.to_string(),
            Obj::TupleDim(_) => TUPLE_DIM.to_string(),
            Obj::FiniteSetSize(_) => FINITE_SET_SIZE.to_string(),
            Obj::FiniteSetMax(_) => FINITE_SET_MAX.to_string(),
            Obj::FiniteSetMin(_) => FINITE_SET_MIN.to_string(),
            Obj::FnRange(_) => FN_RANGE.to_string(),
            Obj::Replacement(_) => REPLACEMENT.to_string(),
            Obj::Sum(_) => SUM.to_string(),
            Obj::SumOfFiniteSet(_) => FINITE_SET_SUM.to_string(),
            Obj::Product(_) => PRODUCT.to_string(),
            Obj::ProductOfFiniteSet(_) => FINITE_SET_PRODUCT.to_string(),
            Obj::Reduce(_) => REDUCE.to_string(),
            Obj::FiniteSetReduce(_) => FINITE_SET_REDUCE.to_string(),
            Obj::Range(_) => RANGE.to_string(),
            Obj::ClosedRange(_) => CLOSED_RANGE.to_string(),
            Obj::MatrixAdd(_) => MATRIX_ADD.to_string(),
            Obj::MatrixSub(_) => MATRIX_SUB.to_string(),
            Obj::MatrixMul(_) => MATRIX_MUL.to_string(),
            Obj::MatrixScalarMul(_) => MATRIX_SCALAR_MUL.to_string(),
            Obj::MatrixPow(_) => MATRIX_POW.to_string(),
            Obj::StructObj(struct_obj) => struct_obj.name.to_string(),
            Obj::InstantiatedTemplateObj(template_obj) => template_obj.template_name.to_string(),
            Obj::ObjAsStructInstanceWithFieldAccess(field_access) => {
                field_access.field_name.clone()
            }
            _ => String::new(),
        }
    }

    /// Precedence-aware display: add parens when a child binds looser than the parent (e.g. + under *).
    /// For same-precedence `+`/`-`, pass a stricter bound (2) on Sub's sides and Add's right so
    /// `a - (b + c)` and `a + (b - c)` do not print as the ambiguous `a - b + c` / `a + b - c`.
    pub fn fmt_with_precedence(
        &self,
        f: &mut fmt::Formatter<'_>,
        parent_precedent: u8,
    ) -> Result<(), fmt::Error> {
        let precedent = precedence(self);
        let need_parens = parent_precedent != 0 && precedent != 0 && precedent > parent_precedent;
        if need_parens {
            write!(f, "{}", LEFT_BRACE)?;
        }
        match self {
            Obj::Add(a) => {
                a.left.fmt_with_precedence(f, 3)?;
                write!(f, " {} ", ADD)?;
                a.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Sub(s) => {
                s.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", SUB)?;
                s.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Mul(m) => {
                m.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MUL)?;
                m.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Div(d) => {
                d.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", DIV)?;
                d.right.fmt_with_precedence(f, 1)?;
            }
            Obj::Mod(m) => {
                m.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MOD)?;
                m.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Gcd(g) => {
                write!(f, "{}{}", GCD, LEFT_BRACE)?;
                g.left.fmt_with_precedence(f, 0)?;
                write!(f, "{COMMA} ")?;
                g.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Lcm(x) => {
                write!(f, "{}{}", LCM, LEFT_BRACE)?;
                x.left.fmt_with_precedence(f, 0)?;
                write!(f, "{COMMA} ")?;
                x.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Floor(x) => write!(f, "{}{}{}{}", FLOOR, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Ceil(x) => write!(f, "{}{}{}{}", CEIL, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Min(x) => write!(
                f,
                "{}{}{}, {}{}",
                MIN, LEFT_BRACE, x.left, x.right, RIGHT_BRACE
            )?,
            Obj::Max(x) => write!(
                f,
                "{}{}{}, {}{}",
                MAX, LEFT_BRACE, x.left, x.right, RIGHT_BRACE
            )?,
            Obj::Exp(x) => write!(f, "{}{}{}{}", EXP, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Ln(x) => write!(f, "{}{}{}{}", LN, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Sign(x) => write!(f, "{}{}{}{}", SIGN, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Factorial(x) => write!(f, "{}{}{}{}", FACTORIAL, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Pow(p) => {
                p.base.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", POW)?;
                p.exponent.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixAdd(m) => {
                m.left.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_ADD)?;
                m.right.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixSub(m) => {
                m.left.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_SUB)?;
                m.right.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixMul(m) => {
                m.left.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_MUL)?;
                m.right.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixPow(m) => {
                m.base.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_POW)?;
                m.exponent.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixScalarMul(m) => {
                m.scalar.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MATRIX_SCALAR_MUL)?;
                m.matrix.fmt_with_precedence(f, 2)?;
            }
            Obj::Abs(a) => {
                write!(f, "{} {}", ABS, LEFT_BRACE)?;
                a.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Sin(x) => {
                write!(f, "{}{}", SIN, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Cos(x) => {
                write!(f, "{}{}", COS, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Tan(x) => {
                write!(f, "{}{}", TAN, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Cot(x) => {
                write!(f, "{}{}", COT, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::RealPart(real_part) => {
                write!(f, "{}{}", RE, LEFT_BRACE)?;
                real_part.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::ImaginaryPart(imaginary_part) => {
                write!(f, "{}{}", IMG, LEFT_BRACE)?;
                imaginary_part.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::ComplexAbs(complex_abs) => {
                write!(f, "{}{}", C_ABS, LEFT_BRACE)?;
                complex_abs.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Sqrt(s) => {
                write!(f, "{} {}", SQRT, LEFT_BRACE)?;
                s.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Log(l) => {
                write!(f, "{} {}", LOG, LEFT_BRACE)?;
                l.base.fmt_with_precedence(f, 0)?;
                write!(f, "{} ", COMMA)?;
                l.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Union(x) => write!(f, "{}", x)?,
            Obj::Intersect(x) => write!(f, "{}", x)?,
            Obj::SetMinus(x) => write!(f, "{}", x)?,
            Obj::SetDiff(x) => write!(f, "{}", x)?,
            Obj::BigUnion(x) => write!(f, "{}", x)?,
            Obj::BigIntersect(x) => write!(f, "{}", x)?,
            Obj::Atom(x) => write!(f, "{}", x)?,
            Obj::FnObj(x) => write!(f, "{}", x)?,
            Obj::Number(x) => write!(f, "{}", x)?,
            Obj::ImaginaryUnit(_) => write!(f, "{}", I)?,
            Obj::EulerNumber(_) => write!(f, "{}", E)?,
            Obj::Pi(_) => write!(f, "{}", PI)?,
            Obj::ListSet(x) => write!(f, "{}", x)?,
            Obj::SetBuilder(x) => write!(f, "{}", x)?,
            Obj::FnSet(x) => write!(f, "{}", x)?,
            Obj::AnonymousFn(x) => write!(f, "{}", x)?,
            Obj::StandardSet(standard_set) => write!(f, "{}", standard_set)?,
            Obj::Cart(x) => write!(f, "{}", x)?,
            Obj::CartDim(x) => write!(f, "{}", x)?,
            Obj::Proj(x) => write!(f, "{}", x)?,
            Obj::TupleDim(x) => write!(f, "{}", x)?,
            Obj::Tuple(x) => write!(f, "{}", x)?,
            Obj::FiniteSetSize(x) => write!(f, "{}", x)?,
            Obj::FiniteSetMax(x) => write!(f, "{}", x)?,
            Obj::FiniteSetMin(x) => write!(f, "{}", x)?,
            Obj::FnRange(x) => write!(f, "{}", x)?,
            Obj::Replacement(x) => write!(f, "{}", x)?,
            Obj::Sum(x) => write!(f, "{}", x)?,
            Obj::SumOfFiniteSet(x) => write!(f, "{}", x)?,
            Obj::Product(x) => write!(f, "{}", x)?,
            Obj::ProductOfFiniteSet(x) => write!(f, "{}", x)?,
            Obj::Reduce(x) => write!(f, "{}", x)?,
            Obj::FiniteSetReduce(x) => write!(f, "{}", x)?,
            Obj::Range(x) => write!(f, "{}", x)?,
            Obj::ClosedRange(x) => write!(f, "{}", x)?,
            Obj::FiniteSeqSet(x) => write!(f, "{}", x)?,
            Obj::SeqSet(x) => write!(f, "{}", x)?,
            Obj::FiniteSeqListObj(x) => write!(f, "{}", x)?,
            Obj::MatrixSet(x) => write!(f, "{}", x)?,
            Obj::MatrixListObj(x) => write!(f, "{}", x)?,
            Obj::PowerSet(x) => write!(f, "{}", x)?,
            Obj::GeneralCart(x) => write!(f, "{}", x)?,
            Obj::ObjAtIndex(x) => write!(f, "{}", x)?,
            Obj::StructObj(x) => write!(f, "{}", x)?,
            Obj::ObjAsStructInstanceWithFieldAccess(x) => write!(f, "{}", x)?,
            Obj::InstantiatedTemplateObj(x) => write!(f, "{}", x)?,
            Obj::OneSideInfinityIntervalObj(x) => write!(f, "{}", x)?,
            Obj::IntervalObj(x) => write!(f, "{}", x)?,
        }
        if need_parens {
            write!(f, "{}", RIGHT_BRACE)?;
        }
        Ok(())
    }

    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Obj {
        if from == to {
            return self;
        }
        match self {
            Obj::Atom(a) => Obj::Atom(a.replace_bound_identifier(from, to)),
            Obj::FnObj(inner) => {
                let head = replace_bound_identifier_in_fn_obj_head(*inner.head, from, to);
                let body = inner
                    .body
                    .into_iter()
                    .map(|group| {
                        group
                            .into_iter()
                            .map(|b| Box::new(Obj::replace_bound_identifier(*b, from, to)))
                            .collect()
                    })
                    .collect();
                FnObj::new(head, body).into()
            }
            Obj::Number(n) => n.into(),
            Obj::ImaginaryUnit(i) => i.into(),
            Obj::EulerNumber(e) => e.into(),
            Obj::Pi(pi) => pi.into(),
            Obj::Add(x) => Add::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Sub(x) => Sub::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Mul(x) => Mul::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Div(x) => Div::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Mod(x) => Mod::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Gcd(x) => Gcd::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Lcm(x) => Lcm::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Floor(x) => Floor::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Ceil(x) => Ceil::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Min(x) => Min::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Max(x) => Max::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Exp(x) => Exp::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Ln(x) => Ln::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Sign(x) => Sign::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Factorial(x) => {
                Factorial::new(Obj::replace_bound_identifier(*x.arg, from, to)).into()
            }
            Obj::Pow(x) => Pow::new(
                Obj::replace_bound_identifier(*x.base, from, to),
                Obj::replace_bound_identifier(*x.exponent, from, to),
            )
            .into(),
            Obj::Abs(x) => Abs::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Sin(x) => Sin::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Cos(x) => Cos::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Tan(x) => Tan::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Cot(x) => Cot::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::RealPart(x) => {
                RealPart::new(Obj::replace_bound_identifier(*x.arg, from, to)).into()
            }
            Obj::ImaginaryPart(x) => {
                ImaginaryPart::new(Obj::replace_bound_identifier(*x.arg, from, to)).into()
            }
            Obj::ComplexAbs(x) => {
                ComplexAbs::new(Obj::replace_bound_identifier(*x.arg, from, to)).into()
            }
            Obj::Sqrt(x) => Sqrt::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Log(x) => Log::new(
                Obj::replace_bound_identifier(*x.base, from, to),
                Obj::replace_bound_identifier(*x.arg, from, to),
            )
            .into(),
            Obj::Union(x) => Union::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Intersect(x) => Intersect::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::SetMinus(x) => SetMinus::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::SetDiff(x) => SetDiff::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::BigUnion(x) => {
                BigUnion::new(Obj::replace_bound_identifier(*x.left, from, to)).into()
            }
            Obj::BigIntersect(x) => {
                BigIntersect::new(Obj::replace_bound_identifier(*x.left, from, to)).into()
            }
            Obj::PowerSet(x) => {
                PowerSet::new(Obj::replace_bound_identifier(*x.set, from, to)).into()
            }
            Obj::GeneralCart(x) => GeneralCart::new(
                Obj::replace_bound_identifier(*x.index_set, from, to),
                Obj::replace_bound_identifier(*x.family_set, from, to),
                Obj::replace_bound_identifier(*x.family_fn, from, to),
            )
            .into(),
            Obj::ListSet(x) => ListSet::new(
                x.list
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::SetBuilder(sb) => {
                let param_binding = if sb.param == from {
                    sb.param_binding.with_local_name(to.to_string())
                } else {
                    sb.param_binding
                };
                let param_set = Obj::replace_bound_identifier(*sb.param_set, from, to);
                let facts = sb
                    .facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier(from, to))
                    .collect();
                Obj::SetBuilder(
                    SetBuilder::new(param_binding, param_set, facts)
                        .expect("renaming a valid set builder preserves object scope validity"),
                )
            }
            Obj::FnSet(fs) => {
                let FnSet { body } = fs;
                let FnSetBody {
                    params_def_with_set,
                    dom_facts,
                    ret_set,
                } = body;
                let params_def_with_set: Vec<ParamGroupWithSet> = params_def_with_set
                    .into_iter()
                    .map(|pg| {
                        let params = pg
                            .params
                            .into_iter()
                            .map(|p| {
                                if p.name() == from {
                                    p.with_local_name(to.to_string())
                                } else {
                                    p
                                }
                            })
                            .collect();
                        ParamGroupWithSet::new(
                            params,
                            Obj::replace_bound_identifier(*pg.param_type, from, to),
                        )
                    })
                    .collect();
                let dom_facts = dom_facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier(from, to))
                    .collect();
                let ret_set = Obj::replace_bound_identifier(*ret_set, from, to);
                FnSet::new(params_def_with_set, dom_facts, ret_set)
                    .expect("renaming a valid fn set preserves object scope validity")
                    .into()
            }
            Obj::AnonymousFn(af) => {
                let AnonymousFn { body, equal_to } = af;
                let FnSetBody {
                    params_def_with_set,
                    dom_facts,
                    ret_set,
                } = body;
                let params_def_with_set: Vec<ParamGroupWithSet> = params_def_with_set
                    .into_iter()
                    .map(|pg| {
                        let params = pg
                            .params
                            .into_iter()
                            .map(|p| {
                                if p.name() == from {
                                    p.with_local_name(to.to_string())
                                } else {
                                    p
                                }
                            })
                            .collect();
                        ParamGroupWithSet::new(
                            params,
                            Obj::replace_bound_identifier(*pg.param_type, from, to),
                        )
                    })
                    .collect();
                let dom_facts = dom_facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier(from, to))
                    .collect();
                let ret_set = Obj::replace_bound_identifier(*ret_set, from, to);
                let equal_to = Obj::replace_bound_identifier(*equal_to, from, to);
                AnonymousFn::new(params_def_with_set, dom_facts, ret_set, equal_to)
                    .expect("renaming a valid anonymous fn preserves object scope validity")
                    .into()
            }
            Obj::Cart(c) => Cart::new(
                c.args
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::CartDim(x) => CartDim::new(Obj::replace_bound_identifier(*x.set, from, to)).into(),
            Obj::Proj(x) => Proj::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.dim, from, to),
            )
            .into(),
            Obj::TupleDim(x) => {
                TupleDim::new(Obj::replace_bound_identifier(*x.arg, from, to)).into()
            }
            Obj::Tuple(t) => Tuple::new(
                t.args
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::FiniteSetSize(x) => {
                FiniteSetSize::new(Obj::replace_bound_identifier(*x.set, from, to)).into()
            }
            Obj::FiniteSetMax(x) => {
                FiniteSetMax::new(Obj::replace_bound_identifier(*x.set, from, to)).into()
            }
            Obj::FiniteSetMin(x) => {
                FiniteSetMin::new(Obj::replace_bound_identifier(*x.set, from, to)).into()
            }
            Obj::FnRange(x) => {
                FnRange::new(Obj::replace_bound_identifier(*x.function, from, to)).into()
            }
            Obj::Replacement(x) => Replacement::new(
                x.prop_name,
                Obj::replace_bound_identifier(*x.source_set, from, to),
            )
            .into(),
            Obj::Sum(x) => Sum::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
            )
            .into(),
            Obj::SumOfFiniteSet(x) => SumOfFiniteSet::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
            )
            .into(),
            Obj::Product(x) => Product::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
            )
            .into(),
            Obj::ProductOfFiniteSet(x) => ProductOfFiniteSet::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
            )
            .into(),
            Obj::Reduce(x) => Reduce::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
                Obj::replace_bound_identifier(*x.op, from, to),
                Obj::replace_bound_identifier(*x.seed, from, to),
            )
            .into(),
            Obj::FiniteSetReduce(x) => FiniteSetReduce::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
                Obj::replace_bound_identifier(*x.op, from, to),
                Obj::replace_bound_identifier(*x.seed, from, to),
            )
            .into(),
            Obj::Range(x) => Range::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
            )
            .into(),
            Obj::ClosedRange(x) => ClosedRange::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
            )
            .into(),
            Obj::FiniteSeqSet(x) => FiniteSeqSet::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.n, from, to),
            )
            .into(),
            Obj::SeqSet(x) => SeqSet::new(Obj::replace_bound_identifier(*x.set, from, to)).into(),
            Obj::FiniteSeqListObj(x) => FiniteSeqListObj::new(
                x.objs
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::MatrixSet(x) => MatrixSet::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.row_len, from, to),
                Obj::replace_bound_identifier(*x.col_len, from, to),
            )
            .into(),
            Obj::MatrixListObj(x) => MatrixListObj::new(
                x.rows
                    .into_iter()
                    .map(|row| {
                        row.into_iter()
                            .map(|b| Obj::replace_bound_identifier(*b, from, to))
                            .collect()
                    })
                    .collect(),
            )
            .into(),
            Obj::MatrixAdd(x) => MatrixAdd::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::MatrixSub(x) => MatrixSub::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::MatrixMul(x) => MatrixMul::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::MatrixScalarMul(x) => MatrixScalarMul::new(
                Obj::replace_bound_identifier(*x.scalar, from, to),
                Obj::replace_bound_identifier(*x.matrix, from, to),
            )
            .into(),
            Obj::MatrixPow(x) => MatrixPow::new(
                Obj::replace_bound_identifier(*x.base, from, to),
                Obj::replace_bound_identifier(*x.exponent, from, to),
            )
            .into(),
            Obj::ObjAtIndex(x) => ObjAtIndex::new(
                Obj::replace_bound_identifier(*x.obj, from, to),
                Obj::replace_bound_identifier(*x.index, from, to),
            )
            .into(),
            Obj::StandardSet(s) => s.into(),
            Obj::StructObj(s) => StructObj::new(
                s.name,
                s.params
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
            )
            .into(),
            Obj::ObjAsStructInstanceWithFieldAccess(s) => {
                let struct_obj = StructObj::new(
                    s.struct_obj.name.clone(),
                    s.struct_obj
                        .params
                        .into_iter()
                        .map(|o| Obj::replace_bound_identifier(o, from, to))
                        .collect(),
                );
                ObjAsStructInstanceWithFieldAccess::new(
                    struct_obj,
                    Obj::replace_bound_identifier(*s.obj, from, to),
                    s.field_name,
                )
                .into()
            }
            Obj::InstantiatedTemplateObj(t) => InstantiatedTemplateObj::new(
                t.template_name,
                t.args
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
                t.symbol,
            )
            .into(),
            Obj::IntervalObj(x) => match x {
                IntervalObj::LeftOpenRightOpen(i) => IntervalObj::new_left_open_right_open(
                    Obj::replace_bound_identifier(*i.start, from, to),
                    Obj::replace_bound_identifier(*i.end, from, to),
                )
                .into(),
                IntervalObj::LeftOpenRightClosed(i) => IntervalObj::new_left_open_right_closed(
                    Obj::replace_bound_identifier(*i.start, from, to),
                    Obj::replace_bound_identifier(*i.end, from, to),
                )
                .into(),
                IntervalObj::LeftClosedRightOpen(i) => IntervalObj::new_left_closed_right_open(
                    Obj::replace_bound_identifier(*i.start, from, to),
                    Obj::replace_bound_identifier(*i.end, from, to),
                )
                .into(),
                IntervalObj::LeftClosedRightClosed(i) => IntervalObj::new_left_closed_right_closed(
                    Obj::replace_bound_identifier(*i.start, from, to),
                    Obj::replace_bound_identifier(*i.end, from, to),
                )
                .into(),
            },
            Obj::OneSideInfinityIntervalObj(x) => match x {
                OneSideInfinityIntervalObj::LeftOpen(i) => {
                    OneSideInfinityIntervalObj::new_left_open(Obj::replace_bound_identifier(
                        *i.start, from, to,
                    ))
                    .into()
                }
                OneSideInfinityIntervalObj::LeftClosed(i) => {
                    OneSideInfinityIntervalObj::new_left_closed(Obj::replace_bound_identifier(
                        *i.start, from, to,
                    ))
                    .into()
                }
                OneSideInfinityIntervalObj::RightOpen(i) => {
                    OneSideInfinityIntervalObj::new_right_open(Obj::replace_bound_identifier(
                        *i.start, from, to,
                    ))
                    .into()
                }
                OneSideInfinityIntervalObj::RightClosed(i) => {
                    OneSideInfinityIntervalObj::new_right_closed(Obj::replace_bound_identifier(
                        *i.start, from, to,
                    ))
                    .into()
                }
            },
        }
    }
}

/// Replace in identifier / `mod::name` name-shaped [`Obj`] values only.
fn replace_bound_identifier_in_name_obj(obj: Obj, from: &str, to: &str) -> Obj {
    if from == to {
        return obj;
    }
    match obj {
        Obj::Atom(AtomObj::Identifier(i)) => {
            if i.name == from {
                Identifier::new(to.to_string()).into()
            } else {
                Obj::Atom(AtomObj::Identifier(i))
            }
        }
        Obj::Atom(AtomObj::IdentifierWithMod(m)) => {
            let name = if m.name == from {
                to.to_string()
            } else {
                m.name
            };
            Obj::from(IdentifierWithMod::new(m.mod_name, name))
        }
        _ => obj,
    }
}

fn replace_bound_identifier_in_fn_obj_head(head: FnObjHead, from: &str, to: &str) -> FnObjHead {
    if from == to {
        return head;
    }
    match head {
        FnObjHead::Identifier(i) => {
            FnObjHead::given_an_atom_return_a_fn_obj_head(replace_bound_identifier_in_name_obj(
                Obj::Atom(AtomObj::Identifier(i.clone())),
                from,
                to,
            ))
            .expect("name replace preserves fn head shape")
        }
        FnObjHead::IdentifierWithMod(m) => {
            FnObjHead::given_an_atom_return_a_fn_obj_head(replace_bound_identifier_in_name_obj(
                Obj::Atom(AtomObj::IdentifierWithMod(m.clone())),
                from,
                to,
            ))
            .expect("name replace preserves fn head shape")
        }
        FnObjHead::Forall(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            ForallFreeParamObj::new(symbol).into()
        }
        FnObjHead::DefHeader(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            DefHeaderFreeParamObj::new(symbol).into()
        }
        FnObjHead::Exist(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            ExistFreeParamObj::new(symbol).into()
        }
        FnObjHead::SetBuilder(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            SetBuilderFreeParamObj::new(symbol).into()
        }
        FnObjHead::FnSet(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            FnSetFreeParamObj::new(symbol).into()
        }
        FnObjHead::DefStructField(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            DefStructFieldFreeParamObj::new(symbol).into()
        }
        FnObjHead::AnonymousFnLiteral(a) => {
            let inner = (*a).clone();
            let replaced = Obj::replace_bound_identifier(Obj::AnonymousFn(inner), from, to);
            let Obj::AnonymousFn(new_af) = replaced else {
                unreachable!()
            };
            FnObjHead::AnonymousFnLiteral(Box::new(new_af))
        }
        FnObjHead::FiniteSeqListObj(v) => {
            let replaced = Obj::replace_bound_identifier(Obj::FiniteSeqListObj(v), from, to);
            let Obj::FiniteSeqListObj(new_v) = replaced else {
                unreachable!()
            };
            FnObjHead::FiniteSeqListObj(new_v)
        }
        FnObjHead::ObjAtIndex(v) => {
            let replaced = Obj::replace_bound_identifier(Obj::ObjAtIndex(v), from, to);
            let Obj::ObjAtIndex(new_v) = replaced else {
                unreachable!()
            };
            FnObjHead::ObjAtIndex(new_v)
        }
        FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => {
            let replaced =
                Obj::replace_bound_identifier(Obj::ObjAsStructInstanceWithFieldAccess(v), from, to);
            let Obj::ObjAsStructInstanceWithFieldAccess(new_v) = replaced else {
                unreachable!()
            };
            FnObjHead::ObjAsStructInstanceWithFieldAccess(new_v)
        }
        FnObjHead::Induc(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            ByInducFreeParamObj::new(symbol).into()
        }
        FnObjHead::DefAlgo(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            DefAlgoFreeParamObj::new(symbol).into()
        }
        FnObjHead::TupleIndex(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            TupleIndexFreeParamObj::new(symbol).into()
        }
        FnObjHead::CartIndex(p) => {
            let symbol = if p.name == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            CartIndexFreeParamObj::new(symbol).into()
        }
        FnObjHead::InstantiatedTemplateObj(t) => {
            let replaced = Obj::replace_bound_identifier(t.into(), from, to);
            let Obj::InstantiatedTemplateObj(new_t) = replaced else {
                unreachable!()
            };
            FnObjHead::InstantiatedTemplateObj(new_t)
        }
        FnObjHead::MatrixOperator(matrix) => {
            let replaced = Obj::replace_bound_identifier((*matrix).clone(), from, to);
            FnObjHead::MatrixOperator(Box::new(replaced))
        }
    }
}

impl fmt::Display for ObjAtIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}{}",
            self.obj, LEFT_BRACKET, self.index, RIGHT_BRACKET
        )
    }
}

impl fmt::Display for StructObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}", STRUCT_VIEW_PREFIX, self.name)?;
        if !self.params.is_empty() {
            write!(
                f,
                "{}{}{}",
                LESS,
                vec_to_string_join_by_comma(&self.params),
                GREATER
            )?;
        }
        Ok(())
    }
}

impl fmt::Display for InstantiatedTemplateObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.symbol.identity_spine(&self.surface_name()))
    }
}

impl fmt::Display for ObjAsStructInstanceWithFieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}", STRUCT_VIEW_PREFIX, self.struct_obj.name)?;
        if !self.struct_obj.params.is_empty() {
            write!(
                f,
                "{}{}{}",
                LESS,
                vec_to_string_join_by_comma(&self.struct_obj.params),
                GREATER
            )?;
        }
        write!(
            f,
            "{}{}{}{}{}",
            LEFT_CURLY_BRACE,
            self.obj,
            RIGHT_CURLY_BRACE,
            DOT_AKA_FIELD_ACCESS_SIGN,
            self.field_name
        )
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            RANGE,
            braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()])
        )
    }
}

impl fmt::Display for ClosedRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            CLOSED_RANGE,
            braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()])
        )
    }
}

impl fmt::Display for IntervalObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let (left_delimiter, right_delimiter) = match self {
            IntervalObj::LeftOpenRightOpen(_) => (LEFT_BRACE, RIGHT_BRACE),
            IntervalObj::LeftOpenRightClosed(_) => (LEFT_BRACE, RIGHT_BRACKET),
            IntervalObj::LeftClosedRightOpen(_) => (LEFT_BRACKET, RIGHT_BRACE),
            IntervalObj::LeftClosedRightClosed(_) => (LEFT_BRACKET, RIGHT_BRACKET),
        };
        let interval_struct = self.interval_struct();
        write!(
            f,
            "{}{}{}, {}{}",
            INTERVAL_LITERAL_PREFIX,
            left_delimiter,
            interval_struct.start.as_ref(),
            interval_struct.end.as_ref(),
            right_delimiter
        )
    }
}

impl fmt::Display for OneSideInfinityIntervalObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(interval) => write!(f, "'({},)", interval.start),
            OneSideInfinityIntervalObj::LeftClosed(interval) => write!(f, "'[{},)", interval.start),
            OneSideInfinityIntervalObj::RightOpen(interval) => write!(f, "'(,{})", interval.start),
            OneSideInfinityIntervalObj::RightClosed(interval) => {
                write!(f, "'(,{}]", interval.start)
            }
        }
    }
}

impl fmt::Display for FiniteSeqSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SEQ,
            braced_vec_to_string(&vec![self.set.as_ref(), self.n.as_ref()])
        )
    }
}

impl fmt::Display for SeqSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            SEQ,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSeqListObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", LEFT_BRACKET)?;
        for (i, o) in self.objs.iter().enumerate() {
            if i > 0 {
                write!(f, "{} ", COMMA)?;
            }
            write!(f, "{}", o)?;
        }
        write!(f, "{}", RIGHT_BRACKET)
    }
}

impl fmt::Display for MatrixSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            MATRIX,
            braced_vec_to_string(&vec![
                self.set.as_ref(),
                self.row_len.as_ref(),
                self.col_len.as_ref(),
            ])
        )
    }
}

impl fmt::Display for MatrixListObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", LEFT_BRACKET)?;
        for (ri, row) in self.rows.iter().enumerate() {
            if ri > 0 {
                write!(f, "{} ", COMMA)?;
            }
            write!(f, "{}", LEFT_BRACKET)?;
            for (ci, o) in row.iter().enumerate() {
                if ci > 0 {
                    write!(f, "{} ", COMMA)?;
                }
                write!(f, "{}", o)?;
            }
            write!(f, "{}", RIGHT_BRACKET)?;
        }
        write!(f, "{}", RIGHT_BRACKET)
    }
}

impl fmt::Display for FiniteSetSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_SIZE,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSetMax {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_MAX,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSetMin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_MIN,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FnRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FN_RANGE,
            braced_vec_to_string(&vec![self.function.as_ref()])
        )
    }
}

impl fmt::Display for Replacement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}, {}{}",
            REPLACEMENT, LEFT_BRACE, self.prop_name, self.source_set, RIGHT_BRACE
        )
    }
}

impl fmt::Display for Sum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            SUM,
            braced_vec_to_string(&vec![
                self.start.as_ref(),
                self.end.as_ref(),
                self.func.as_ref(),
            ])
        )
    }
}

impl fmt::Display for SumOfFiniteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_SUM,
            braced_vec_to_string(&vec![self.set.as_ref(), self.func.as_ref()])
        )
    }
}

impl fmt::Display for Product {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            PRODUCT,
            braced_vec_to_string(&vec![
                self.start.as_ref(),
                self.end.as_ref(),
                self.func.as_ref(),
            ])
        )
    }
}

impl fmt::Display for ProductOfFiniteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_PRODUCT,
            braced_vec_to_string(&vec![self.set.as_ref(), self.func.as_ref()])
        )
    }
}

impl fmt::Display for Reduce {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            REDUCE,
            braced_vec_to_string(&vec![
                self.start.as_ref(),
                self.end.as_ref(),
                self.func.as_ref(),
                self.op.as_ref(),
                self.seed.as_ref(),
            ])
        )
    }
}

impl fmt::Display for FiniteSetReduce {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_REDUCE,
            braced_vec_to_string(&vec![
                self.set.as_ref(),
                self.func.as_ref(),
                self.op.as_ref(),
                self.seed.as_ref(),
            ])
        )
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for CartDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            CART_DIM,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            PROJ,
            braced_vec_to_string(&vec![self.set.as_ref(), self.dim.as_ref()])
        )
    }
}

impl fmt::Display for TupleDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            TUPLE_DIM,
            braced_vec_to_string(&vec![self.arg.as_ref()])
        )
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.symbol.as_ref() {
            Some(symbol) => write!(f, "{}", symbol.identity_spine(symbol.display_name())),
            None => write!(f, "{}", self.name),
        }
    }
}

impl fmt::Display for FnObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", fn_obj_to_string(self.head.as_ref(), &self.body))
    }
}

pub fn fn_obj_to_string(head: &FnObjHead, body: &Vec<Vec<Box<Obj>>>) -> String {
    let mut fn_obj_string = head.to_string();
    for group in body.iter() {
        fn_obj_string = format!("{}{}", fn_obj_string, braced_vec_to_string(group));
    }
    fn_obj_string
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.normalized_value)
    }
}

impl fmt::Display for Add {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, ADD, self.right)
    }
}

impl fmt::Display for Sub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, SUB, self.right)
    }
}

impl fmt::Display for Mul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MUL, self.right)
    }
}

impl fmt::Display for Div {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, DIV, self.right)
    }
}

impl fmt::Display for Mod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MOD, self.right)
    }
}

impl fmt::Display for Gcd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", GCD, self.left, self.right)
    }
}

impl fmt::Display for Lcm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", LCM, self.left, self.right)
    }
}

impl fmt::Display for Floor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", FLOOR, self.arg)
    }
}

impl fmt::Display for Ceil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", CEIL, self.arg)
    }
}

impl fmt::Display for Min {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", MIN, self.left, self.right)
    }
}

impl fmt::Display for Max {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", MAX, self.left, self.right)
    }
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", EXP, self.arg)
    }
}

impl fmt::Display for Ln {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", LN, self.arg)
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", SIGN, self.arg)
    }
}

impl fmt::Display for Factorial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", FACTORIAL, self.arg)
    }
}

impl fmt::Display for Pow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.base, POW, self.exponent)
    }
}

impl fmt::Display for MatrixAdd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MATRIX_ADD, self.right)
    }
}

impl fmt::Display for MatrixSub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MATRIX_SUB, self.right)
    }
}

impl fmt::Display for MatrixMul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MATRIX_MUL, self.right)
    }
}

impl fmt::Display for MatrixScalarMul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.scalar, MATRIX_SCALAR_MUL, self.matrix)
    }
}

impl fmt::Display for MatrixPow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.base, MATRIX_POW, self.exponent)
    }
}

impl fmt::Display for Abs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {}{}{}", ABS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Sin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", SIN, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Cos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", COS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Tan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", TAN, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Cot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", COT, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for RealPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", RE, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for ImaginaryPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", IMG, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for ComplexAbs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", C_ABS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Sqrt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {}{}{}", SQRT, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Log {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}{}{}",
            LOG, LEFT_BRACE, self.base, COMMA, self.arg, RIGHT_BRACE
        )
    }
}

impl fmt::Display for Union {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            UNION,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for Intersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            INTERSECT,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for SetMinus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            SET_MINUS,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for SetDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            SET_DIFF,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for BigUnion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            BIG_UNION,
            braced_vec_to_string(&vec![self.left.as_ref()])
        )
    }
}

impl fmt::Display for BigIntersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            BIG_INTERSECT,
            braced_vec_to_string(&vec![self.left.as_ref()])
        )
    }
}

impl fmt::Display for IdentifierWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.symbol.as_ref() {
            Some(symbol) => write!(f, "{}", symbol.identity_spine(symbol.display_name())),
            None => write!(f, "{}{}{}", self.mod_name, MOD_SIGN, self.name),
        }
    }
}

impl fmt::Display for ListSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", curly_braced_vec_to_string(&self.list))
    }
}

impl fmt::Display for SetBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{} {}{} {}{}",
            LEFT_CURLY_BRACE,
            self.param_binding,
            self.param_set,
            COLON,
            vec_to_string_join_by_comma(&self.facts),
            RIGHT_CURLY_BRACE
        )
    }
}

impl fmt::Display for GeneralCart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}({}, {}, {})",
            GENERAL_CART, self.index_set, self.family_set, self.family_fn
        )
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}", CART, braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for PowerSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            POWER_SET,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl From<Identifier> for Obj {
    fn from(id: Identifier) -> Self {
        Obj::Atom(AtomObj::Identifier(id))
    }
}

impl From<usize> for Obj {
    fn from(n: usize) -> Self {
        Number::new(n.to_string()).into()
    }
}

impl From<Number> for Obj {
    fn from(n: Number) -> Self {
        Obj::Number(n)
    }
}

impl From<ImaginaryUnit> for Obj {
    fn from(i: ImaginaryUnit) -> Self {
        Obj::ImaginaryUnit(i)
    }
}

impl From<EulerNumber> for Obj {
    fn from(e: EulerNumber) -> Self {
        Obj::EulerNumber(e)
    }
}

impl From<Pi> for Obj {
    fn from(pi: Pi) -> Self {
        Obj::Pi(pi)
    }
}

impl From<Add> for Obj {
    fn from(a: Add) -> Self {
        Obj::Add(a)
    }
}

impl From<MatrixAdd> for Obj {
    fn from(m: MatrixAdd) -> Self {
        Obj::MatrixAdd(m)
    }
}

impl From<MatrixSub> for Obj {
    fn from(m: MatrixSub) -> Self {
        Obj::MatrixSub(m)
    }
}

impl From<MatrixMul> for Obj {
    fn from(m: MatrixMul) -> Self {
        Obj::MatrixMul(m)
    }
}

impl From<MatrixScalarMul> for Obj {
    fn from(m: MatrixScalarMul) -> Self {
        Obj::MatrixScalarMul(m)
    }
}

impl From<MatrixPow> for Obj {
    fn from(m: MatrixPow) -> Self {
        Obj::MatrixPow(m)
    }
}

impl From<Sub> for Obj {
    fn from(s: Sub) -> Self {
        Obj::Sub(s)
    }
}

impl From<FnObj> for Obj {
    fn from(f: FnObj) -> Self {
        Obj::FnObj(f)
    }
}

impl From<Mul> for Obj {
    fn from(m: Mul) -> Self {
        Obj::Mul(m)
    }
}

impl From<Div> for Obj {
    fn from(d: Div) -> Self {
        Obj::Div(d)
    }
}

impl From<Mod> for Obj {
    fn from(m: Mod) -> Self {
        Obj::Mod(m)
    }
}

impl From<Gcd> for Obj {
    fn from(g: Gcd) -> Self {
        Obj::Gcd(g)
    }
}

impl From<Lcm> for Obj {
    fn from(x: Lcm) -> Self {
        Obj::Lcm(x)
    }
}

impl From<Floor> for Obj {
    fn from(x: Floor) -> Self {
        Obj::Floor(x)
    }
}

impl From<Ceil> for Obj {
    fn from(x: Ceil) -> Self {
        Obj::Ceil(x)
    }
}

impl From<Min> for Obj {
    fn from(x: Min) -> Self {
        Obj::Min(x)
    }
}

impl From<Max> for Obj {
    fn from(x: Max) -> Self {
        Obj::Max(x)
    }
}

impl From<Exp> for Obj {
    fn from(x: Exp) -> Self {
        Obj::Exp(x)
    }
}

impl From<Ln> for Obj {
    fn from(x: Ln) -> Self {
        Obj::Ln(x)
    }
}

impl From<Sign> for Obj {
    fn from(x: Sign) -> Self {
        Obj::Sign(x)
    }
}

impl From<Factorial> for Obj {
    fn from(x: Factorial) -> Self {
        Obj::Factorial(x)
    }
}

impl From<Pow> for Obj {
    fn from(p: Pow) -> Self {
        Obj::Pow(p)
    }
}

impl From<Abs> for Obj {
    fn from(a: Abs) -> Self {
        Obj::Abs(a)
    }
}

impl From<Sin> for Obj {
    fn from(x: Sin) -> Self {
        Obj::Sin(x)
    }
}

impl From<Cos> for Obj {
    fn from(x: Cos) -> Self {
        Obj::Cos(x)
    }
}

impl From<Tan> for Obj {
    fn from(x: Tan) -> Self {
        Obj::Tan(x)
    }
}

impl From<Cot> for Obj {
    fn from(x: Cot) -> Self {
        Obj::Cot(x)
    }
}

impl From<RealPart> for Obj {
    fn from(real_part: RealPart) -> Self {
        Obj::RealPart(real_part)
    }
}

impl From<ImaginaryPart> for Obj {
    fn from(imaginary_part: ImaginaryPart) -> Self {
        Obj::ImaginaryPart(imaginary_part)
    }
}

impl From<ComplexAbs> for Obj {
    fn from(complex_abs: ComplexAbs) -> Self {
        Obj::ComplexAbs(complex_abs)
    }
}

impl From<Sqrt> for Obj {
    fn from(s: Sqrt) -> Self {
        Obj::Sqrt(s)
    }
}

impl From<Log> for Obj {
    fn from(l: Log) -> Self {
        Obj::Log(l)
    }
}

impl From<Union> for Obj {
    fn from(u: Union) -> Self {
        Obj::Union(u)
    }
}

impl From<Intersect> for Obj {
    fn from(i: Intersect) -> Self {
        Obj::Intersect(i)
    }
}

impl From<SetMinus> for Obj {
    fn from(s: SetMinus) -> Self {
        Obj::SetMinus(s)
    }
}

impl From<SetDiff> for Obj {
    fn from(s: SetDiff) -> Self {
        Obj::SetDiff(s)
    }
}

impl From<BigUnion> for Obj {
    fn from(c: BigUnion) -> Self {
        Obj::BigUnion(c)
    }
}

impl From<BigIntersect> for Obj {
    fn from(c: BigIntersect) -> Self {
        Obj::BigIntersect(c)
    }
}

impl From<PowerSet> for Obj {
    fn from(p: PowerSet) -> Self {
        Obj::PowerSet(p)
    }
}

impl From<GeneralCart> for Obj {
    fn from(g: GeneralCart) -> Self {
        Obj::GeneralCart(g)
    }
}

impl From<ListSet> for Obj {
    fn from(l: ListSet) -> Self {
        Obj::ListSet(l)
    }
}

impl From<SetBuilder> for Obj {
    fn from(s: SetBuilder) -> Self {
        Obj::SetBuilder(s)
    }
}

impl From<Cart> for Obj {
    fn from(c: Cart) -> Self {
        Obj::Cart(c)
    }
}

impl From<CartDim> for Obj {
    fn from(c: CartDim) -> Self {
        Obj::CartDim(c)
    }
}

impl From<Proj> for Obj {
    fn from(p: Proj) -> Self {
        Obj::Proj(p)
    }
}

impl From<TupleDim> for Obj {
    fn from(t: TupleDim) -> Self {
        Obj::TupleDim(t)
    }
}

impl From<Tuple> for Obj {
    fn from(t: Tuple) -> Self {
        Obj::Tuple(t)
    }
}

impl From<FiniteSetSize> for Obj {
    fn from(c: FiniteSetSize) -> Self {
        Obj::FiniteSetSize(c)
    }
}

impl From<FiniteSetMax> for Obj {
    fn from(x: FiniteSetMax) -> Self {
        Obj::FiniteSetMax(x)
    }
}

impl From<FiniteSetMin> for Obj {
    fn from(x: FiniteSetMin) -> Self {
        Obj::FiniteSetMin(x)
    }
}

impl From<FnRange> for Obj {
    fn from(r: FnRange) -> Self {
        Obj::FnRange(r)
    }
}

impl From<Replacement> for Obj {
    fn from(r: Replacement) -> Self {
        Obj::Replacement(r)
    }
}

impl From<Sum> for Obj {
    fn from(s: Sum) -> Self {
        Obj::Sum(s)
    }
}

impl From<SumOfFiniteSet> for Obj {
    fn from(s: SumOfFiniteSet) -> Self {
        Obj::SumOfFiniteSet(s)
    }
}

impl From<Product> for Obj {
    fn from(p: Product) -> Self {
        Obj::Product(p)
    }
}

impl From<ProductOfFiniteSet> for Obj {
    fn from(p: ProductOfFiniteSet) -> Self {
        Obj::ProductOfFiniteSet(p)
    }
}

impl From<Reduce> for Obj {
    fn from(r: Reduce) -> Self {
        Obj::Reduce(r)
    }
}

impl From<FiniteSetReduce> for Obj {
    fn from(r: FiniteSetReduce) -> Self {
        Obj::FiniteSetReduce(r)
    }
}

impl From<Range> for Obj {
    fn from(r: Range) -> Self {
        Obj::Range(r)
    }
}

impl From<ClosedRange> for Obj {
    fn from(r: ClosedRange) -> Self {
        Obj::ClosedRange(r)
    }
}

impl From<IntervalObj> for Obj {
    fn from(r: IntervalObj) -> Self {
        Obj::IntervalObj(r)
    }
}

impl From<OneSideInfinityIntervalObj> for Obj {
    fn from(r: OneSideInfinityIntervalObj) -> Self {
        Obj::OneSideInfinityIntervalObj(r)
    }
}

impl From<FiniteSeqSet> for Obj {
    fn from(v: FiniteSeqSet) -> Self {
        Obj::FiniteSeqSet(v)
    }
}

impl From<SeqSet> for Obj {
    fn from(v: SeqSet) -> Self {
        Obj::SeqSet(v)
    }
}

impl From<FiniteSeqListObj> for Obj {
    fn from(v: FiniteSeqListObj) -> Self {
        Obj::FiniteSeqListObj(v)
    }
}

impl From<MatrixSet> for Obj {
    fn from(v: MatrixSet) -> Self {
        Obj::MatrixSet(v)
    }
}

impl From<MatrixListObj> for Obj {
    fn from(v: MatrixListObj) -> Self {
        Obj::MatrixListObj(v)
    }
}

impl From<ObjAtIndex> for Obj {
    fn from(o: ObjAtIndex) -> Self {
        Obj::ObjAtIndex(o)
    }
}

impl From<IdentifierWithMod> for Obj {
    fn from(m: IdentifierWithMod) -> Self {
        Obj::Atom(AtomObj::IdentifierWithMod(m))
    }
}

impl From<StructObj> for Obj {
    fn from(s: StructObj) -> Self {
        Obj::StructObj(s)
    }
}

impl From<ObjAsStructInstanceWithFieldAccess> for Obj {
    fn from(s: ObjAsStructInstanceWithFieldAccess) -> Self {
        Obj::ObjAsStructInstanceWithFieldAccess(s)
    }
}

impl From<InstantiatedTemplateObj> for Obj {
    fn from(t: InstantiatedTemplateObj) -> Self {
        Obj::InstantiatedTemplateObj(t)
    }
}

impl From<StandardSet> for Obj {
    fn from(s: StandardSet) -> Self {
        Obj::StandardSet(s)
    }
}

impl Identifier {
    /// Build a name-shaped [`Obj`] (via [`AtomObj::Identifier`]). Parameter is String (not &str).
    pub fn mk(name: String) -> Obj {
        Identifier::new(name).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn display_keeps_parentheses_on_composite_divisor() {
        let one = number("1");
        let two = number("2");
        let three = number("3");

        let divided_by_product: Obj =
            Div::new(one.clone(), Mul::new(two.clone(), three.clone()).into()).into();
        let divided_by_quotient: Obj =
            Div::new(one.clone(), Div::new(two.clone(), three.clone()).into()).into();
        let left_associative_quotient: Obj = Div::new(Div::new(one, two).into(), three).into();

        assert_eq!(divided_by_product.to_string(), "1 / (2 * 3)");
        assert_eq!(divided_by_quotient.to_string(), "1 / (2 / 3)");
        assert_eq!(left_associative_quotient.to_string(), "1 / 2 / 3");
    }

    #[test]
    fn display_uses_two_sided_interval_literals() {
        let zero = number("0");
        let one = number("1");

        assert_eq!(
            IntervalObj::new_left_open_right_open(zero.clone(), one.clone()).to_string(),
            "'(0, 1)"
        );
        assert_eq!(
            IntervalObj::new_left_open_right_closed(zero.clone(), one.clone()).to_string(),
            "'(0, 1]"
        );
        assert_eq!(
            IntervalObj::new_left_closed_right_open(zero.clone(), one.clone()).to_string(),
            "'[0, 1)"
        );
        assert_eq!(
            IntervalObj::new_left_closed_right_closed(zero, one).to_string(),
            "'[0, 1]"
        );
    }

    #[test]
    fn display_uses_one_sided_interval_literals() {
        let zero = number("0");

        assert_eq!(
            OneSideInfinityIntervalObj::new_left_open(zero.clone()).to_string(),
            "'(0,)"
        );
        assert_eq!(
            OneSideInfinityIntervalObj::new_left_closed(zero.clone()).to_string(),
            "'[0,)"
        );
        assert_eq!(
            OneSideInfinityIntervalObj::new_right_open(zero.clone()).to_string(),
            "'(,0)"
        );
        assert_eq!(
            OneSideInfinityIntervalObj::new_right_closed(zero).to_string(),
            "'(,0]"
        );
    }

    fn number(value: &str) -> Obj {
        Number::new(value.to_string()).into()
    }
}
