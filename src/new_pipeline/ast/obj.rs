//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names (name is identity); FactId; LineFile.
//!
//! Layout: `Obj` first; each payload type follows in the same order as its `Obj` variant.
//! Nested helpers that are not themselves `Obj` variants sit with their owning variant.

use super::fact::QuantifierFreeFact;
use super::names::AtomicName;
use super::param::SetBoundParameterList;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obj {
    Identifier(IdentifierObj),
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
    Quot(Quot),
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
    Arcsin(Arcsin),
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
    BigUnion(BigUnion),
    BigIntersect(BigIntersect),
    IndexUnion(IndexUnion),
    IndexIntersect(IndexIntersect),
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
    StructObj(StructObj),
    ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
    OneSideInfinityIntervalObj(OneSideInfinityIntervalObj),
    IntervalObj(IntervalObj),
}

// Binder / parameter name (always plain; never module-qualified).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Identifier {
    pub name: String,
}

// Free or module-qualified name used as an object (at most three `::` segments).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentifierObj {
    pub name: AtomicName,
}

impl IdentifierObj {
    pub fn new(name: AtomicName) -> Self {
        Self { name }
    }

    pub fn plain(name: String) -> Self {
        Self {
            name: AtomicName::plain(name),
        }
    }
}

// FnObj
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnObjHead {
    Identifier(IdentifierObj),
    /// Anonymous function literal used as applied head, e.g. `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FiniteSeqListObj(FiniteSeqListObj),
    ObjAtIndex(ObjAtIndex),
    ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnObj {
    pub head: Box<FnObjHead>,
    pub body: Vec<Vec<Box<Obj>>>,
}

// Number
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Number {
    pub normalized_value: String,
}

// ImaginaryUnit
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImaginaryUnit;

// EulerNumber
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EulerNumber;

// Pi
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pi;

// Add
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Add {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Sub
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Mul
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Div
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Div {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Mod
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mod {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Quot
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quot {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Gcd
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gcd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Lcm
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lcm {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Floor
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Floor {
    pub arg: Box<Obj>,
}

// Ceil
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ceil {
    pub arg: Box<Obj>,
}

// Min
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Min {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Max
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Max {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Exp
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exp {
    pub arg: Box<Obj>,
}

// Ln
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ln {
    pub arg: Box<Obj>,
}

// Sign
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sign {
    pub arg: Box<Obj>,
}

// Factorial
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorial {
    pub arg: Box<Obj>,
}

// Pow
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

// Abs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Abs {
    pub arg: Box<Obj>,
}

// Sin
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sin {
    pub arg: Box<Obj>,
}

// Arcsin
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arcsin {
    pub arg: Box<Obj>,
}

// Cos
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cos {
    pub arg: Box<Obj>,
}

// Tan
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tan {
    pub arg: Box<Obj>,
}

// Cot
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cot {
    pub arg: Box<Obj>,
}

// RealPart
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealPart {
    pub arg: Box<Obj>,
}

// ImaginaryPart
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImaginaryPart {
    pub arg: Box<Obj>,
}

// ComplexAbs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexAbs {
    pub arg: Box<Obj>,
}

// Sqrt
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sqrt {
    pub arg: Box<Obj>,
}

// Log
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Log {
    pub base: Box<Obj>,
    pub arg: Box<Obj>,
}

// Union
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Union {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// Intersect
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Intersect {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// SetMinus
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetMinus {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// BigUnion
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigUnion {
    pub left: Box<Obj>,
}

// BigIntersect
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigIntersect {
    pub left: Box<Obj>,
}

// IndexUnion
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexUnion {
    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// IndexIntersect
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexIntersect {
    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// PowerSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PowerSet {
    pub set: Box<Obj>,
}

// GeneralCart
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneralCart {
    pub index_set: Box<Obj>,
    pub family_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// ListSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListSet {
    pub list: Vec<Box<Obj>>,
}

// SetBuilder
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBuilderBody {
    pub param_binding: Identifier,
    pub param_set: Box<Obj>,
    pub facts: Vec<QuantifierFreeFact>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBuilder {
    /// User spelling; display only.
    pub surface: SetBuilderBody,
    /// Alpha-normalized identity (`□N`); ops / ir / known-memory keys.
    pub alpha: SetBuilderBody,
}

// FnSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetBody {
    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    /// The return set may depend on the function's parameters and is instantiated at application.
    pub ret_set: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSet {
    /// User spelling; display only.
    pub surface: FnSetBody,
    /// Alpha-normalized identity (`□N`); ops / ir / known-memory keys.
    pub alpha: FnSetBody,
}

// AnonymousFn
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnonymousFnBody {
    pub body: FnSetBody,
    pub equal_to: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnonymousFn {
    /// User spelling; display only.
    pub surface: AnonymousFnBody,
    /// Alpha-normalized identity (`□N`); ops / ir / known-memory keys.
    pub alpha: AnonymousFnBody,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnSetSpace {
    Set(FnSet),
    Anon(AnonymousFn),
}

// Cart
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cart {
    pub args: Vec<Box<Obj>>,
}

// CartDim
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CartDim {
    pub set: Box<Obj>,
}

// Proj
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proj {
    pub set: Box<Obj>,
    pub dim: Box<Obj>,
}

// TupleDim
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleDim {
    pub arg: Box<Obj>,
}

// Tuple
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tuple {
    pub args: Vec<Box<Obj>>,
}

// FiniteSetSize
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetSize {
    pub set: Box<Obj>,
}

// FiniteSetMax
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetMax {
    pub set: Box<Obj>,
}

// FiniteSetMin
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetMin {
    pub set: Box<Obj>,
}

// FnRange
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnRange {
    pub function: Box<Obj>,
}

// Replacement
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replacement {
    pub prop_name: AtomicName,
    pub source_set: Box<Obj>,
}

// Sum
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sum {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

// SumOfFiniteSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

// Product
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Product {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

// ProductOfFiniteSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

// Reduce
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reduce {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

// FiniteSetReduce
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetReduce {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

// Range
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Range {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// ClosedRange
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedRange {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// FiniteSeqSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSeqSet {
    pub set: Box<Obj>,
    pub n: Box<Obj>,
}

// SeqSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqSet {
    pub set: Box<Obj>,
}

// FiniteSeqListObj
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSeqListObj {
    pub objs: Vec<Box<Obj>>,
}

// ObjAtIndex
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjAtIndex {
    pub obj: Box<Obj>,
    pub index: Box<Obj>,
}

// StandardSet
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StandardSet {
    NPos,
    N,
    Q,
    Z,
    R,
    C,
    QPos,
    RPos,
    QNeg,
    ZNeg,
    RNeg,
    QStar,
    ZStar,
    RStar,
    CStar,
}

// StructObj
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructObj {
    pub name: AtomicName,
    pub params: Vec<Obj>,
}

// ObjAsStructInstanceWithFieldAccess
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjAsStructInstanceWithFieldAccess {
    pub obj: Box<Obj>,
    pub field_name: String,
    /// Filled by execution/instantiation, never by parsing. It preserves the
    /// field owner when substituting a typed receiver with an arbitrary value.
    pub resolved_struct_carrier: Option<Box<StructObj>>,
}

// InstantiatedTemplateObj
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstantiatedTemplateObj {
    pub template_name: AtomicName,
    pub args: Vec<Obj>,
}

// OneSideInfinityIntervalObj
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OneSideInfinityIntervalObj {
    LeftOpen(OneSideInfinityIntervalObjStruct),
    LeftClosed(OneSideInfinityIntervalObjStruct),
    RightOpen(OneSideInfinityIntervalObjStruct),
    RightClosed(OneSideInfinityIntervalObjStruct),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneSideInfinityIntervalObjStruct {
    pub start: Box<Obj>,
}

// IntervalObj
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntervalObj {
    LeftOpenRightOpen(IntervalObjStruct),
    LeftOpenRightClosed(IntervalObjStruct),
    LeftClosedRightOpen(IntervalObjStruct),
    LeftClosedRightClosed(IntervalObjStruct),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntervalObjStruct {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

impl Identifier {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

/// Litex binder-slot identity after `alpha_normalize` (U+25A1 + index).
pub const BINDER_SLOT_PREFIX: &str = "□";

pub fn binder_slot_name(index: usize) -> String {
    format!("{BINDER_SLOT_PREFIX}{index}")
}

pub fn is_binder_slot_name(name: &str) -> bool {
    let rest = match name.strip_prefix(BINDER_SLOT_PREFIX) {
        Some(r) => r,
        None => return false,
    };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

