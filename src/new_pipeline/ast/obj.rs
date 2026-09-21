//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: BoundName / IdentifierId for plain refs; FactId; LineFile.
//!
//! Layout: `Obj` first; each payload type follows in the same order as its `Obj` variant.
//! Nested helpers that are not themselves `Obj` variants sit with their owning variant.
//!
//! Pure-set model: every well-defined Litex object satisfies `$is_set`. Numerals,
//! function values, N/Z/Q/R/C, user sets, and fn spaces are all `Obj` — different
//! math interfaces, one carrier. Membership `$in` is a Fact between two objects.
//! The host `Object` type is meta-level only: not an internal universal set writable
//! on either side of `$in`. Unrestricted comprehension is forbidden; set formers
//! are bounded (SetBuilder, replacement, …) with their own WD obligations.

use super::fact::QuantifierFreeFact;
use super::names::{AtomicName, BoundName, PlainName};
use super::param::SetBoundParameterList;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

// Mathematical value / expression. Not a proposition (see Fact) and not an env action (see Stmt).
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
    ObjAtIndex(ObjAtIndex),
    StandardSet(StandardSet),
    StructObj(StructObj),
    FieldAccess(FieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
    OneSideInfinityIntervalObj(OneSideInfinityIntervalObj),
    IntervalObj(IntervalObj),
}

// Free or module-qualified name used as an object (at most three `::` segments).
// Plain occurrences carry IdentifierId; qualified names do not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdentifierObj {
    Plain {
        id: IdentifierId,
        name: PlainName,
    },
    WithExportFileId {
        export_file_id: usize,
        name: PlainName,
    },
    WithModAndExportFileId {
        global_mod_id: usize,
        export_file_id: usize,
        name: PlainName,
    },
}

impl IdentifierObj {
    pub fn plain(id: IdentifierId, name: PlainName) -> Self {
        IdentifierObj::Plain { id, name }
    }

    pub fn from_bound_name(bound: &BoundName) -> Self {
        IdentifierObj::Plain {
            id: bound.id,
            name: bound.name.clone(),
        }
    }

    pub fn with_export_file_id(export_file_id: usize, name: PlainName) -> Self {
        IdentifierObj::WithExportFileId {
            export_file_id,
            name,
        }
    }

    pub fn with_mod_and_export_file_id(
        global_mod_id: usize,
        export_file_id: usize,
        name: PlainName,
    ) -> Self {
        IdentifierObj::WithModAndExportFileId {
            global_mod_id,
            export_file_id,
            name,
        }
    }

    pub fn display_string(&self) -> String {
        match self {
            IdentifierObj::Plain { name, .. } => name.clone(),
            IdentifierObj::WithExportFileId {
                export_file_id,
                name,
            } => format!("f{export_file_id}::{name}"),
            IdentifierObj::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => format!("m{global_mod_id}::f{export_file_id}::{name}"),
        }
    }

    // IR key: plain embeds IdentifierId; qualified matches AtomicName spelling.
    pub fn ir_string(&self) -> String {
        match self {
            IdentifierObj::Plain { id, name } => format!("#{}#{}", id.value(), name),
            other => other.display_string(),
        }
    }
}

// FnObj
// Applied heads only when a callable contract is easy to recover:
// Identifier / template instance → InFunctionSet; AnonymousFnLiteral → its own FnSet;
// FieldAccess → field carrier type. ObjAtIndex is intentionally not a head: `t[i]` is
// just an element, with no stable function signature, so `t[i](a)` is rejected at parse.
// Keep `Obj::ObjAtIndex` for tuple/cart indexing such as `(1, 2)[1]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnObjHead {
    Identifier(IdentifierObj),
    /// Anonymous function literal used as applied head, e.g. `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FieldAccess(FieldAccess),
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

// Bounded comprehension `{x S: facts}` over an already available set `S`.
// Not `{x: P(x)}`. Facts stay quantifier-free so the builder has a simple index shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBuilder {
    pub param_binding: BoundName,
    pub param_set: Box<Obj>,
    pub facts: Vec<QuantifierFreeFact>,
}

// Function space `fn(x S, ...) T`. Parameters are SetBound only (`x S`), never `A set`.
// Dom facts are ordered WD assumptions; `ret_set` may depend on parameters and is
// instantiated at application. For definitions over an arbitrary set, use template.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSet {
    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    // May depend on the function's parameters; instantiated at application.
    pub ret_set: Box<Obj>,
}

// Concrete function value belonging to a FnSet (same binder / WD story as FnSet).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnonymousFn {
    pub body: FnSet,
    pub equal_to: Box<Obj>,
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

// `replacement(P, A)`: image of A under a functional set-valued relation P.
// WD requires more than children: uniqueness / functionality of P on A (Manual Sets).
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

// FieldAccess — surface `x.y` / `x.y.z` (one node, fields left-to-right).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldAccess {
    pub obj: Box<Obj>,
    pub fields: Vec<String>,
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

