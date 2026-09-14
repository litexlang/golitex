//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String display names plus IdentifierId on Identifier atoms; FactId; LineFile.

use super::fact::QuantifierFreeFact;
use super::names::AtomicName;
use super::param::SetBoundParameterList;
use crate::new_pipeline::runtime::IdentifierId;

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Add {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sub {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mul {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Div {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mod {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quot {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gcd {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lcm {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/arithmetic_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pow {    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

// from object/atom.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomObj {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Bound(BoundParamObj),
}

// from object/binary_set_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Union {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/binary_set_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Intersect {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/binary_set_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetMinus {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/complex_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealPart {    pub arg: Box<Obj>,
}

// from object/complex_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImaginaryPart {    pub arg: Box<Obj>,
}

// from object/complex_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexAbs {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sqrt {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exp {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ln {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sign {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorial {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Abs {    pub arg: Box<Obj>,
}

// from object/elementary_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Log {    pub base: Box<Obj>,
    pub arg: Box<Obj>,
}

// from object/finite_set_measures.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetSize {    pub set: Box<Obj>,
}

// from object/finite_set_measures.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetMax {    pub set: Box<Obj>,
}

// from object/finite_set_measures.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetMin {    pub set: Box<Obj>,
}

// from object/function_application.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnObj {    pub head: Box<FnObjHead>,
    pub body: Vec<Vec<Box<Obj>>>,
}

// from object/function_head.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnObjHead {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    Bound(BoundParamObj),
    /// Anonymous function literal used as applied head, e.g. `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FiniteSeqListObj(FiniteSeqListObj),
    ObjAtIndex(ObjAtIndex),
    ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
}

// from object/function_images.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnRange {    pub function: Box<Obj>,
}

// from object/function_images.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replacement {    pub prop_name: AtomicName,
    pub source_set: Box<Obj>,
}

// from object/function_set.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetBody {    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    /// The return set may depend on the function's parameters and is instantiated at application.
    pub ret_set: Box<Obj>,
}

// from object/function_set.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSet {    pub body: FnSetBody,
}

// from object/function_set.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnonymousFn {    pub body: FnSetBody,
    pub equal_to: Box<Obj>,
}

// from object/function_set.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnSetSpace {
    Set(FnSet),
    Anon(AnonymousFn),
}

// from object/identifier.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Identifier {
    pub name: String,
    pub identifier_id: IdentifierId,
}

// from object/identifier.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentifierWithMod {
    pub mod_name: String,
    pub name: String,
    pub identifier_id: IdentifierId,
}

// from object/indexing.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjAtIndex {    pub obj: Box<Obj>,
    pub index: Box<Obj>,
}

// from object/intervals.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OneSideInfinityIntervalObj {
    LeftOpen(OneSideInfinityIntervalObjStruct),
    LeftClosed(OneSideInfinityIntervalObjStruct),
    RightOpen(OneSideInfinityIntervalObjStruct),
    RightClosed(OneSideInfinityIntervalObjStruct),
}

// from object/intervals.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneSideInfinityIntervalObjStruct {    pub start: Box<Obj>,
}

// from object/intervals.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntervalObj {
    LeftOpenRightOpen(IntervalObjStruct),
    LeftOpenRightClosed(IntervalObjStruct),
    LeftClosedRightOpen(IntervalObjStruct),
    LeftClosedRightClosed(IntervalObjStruct),
}

// from object/intervals.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntervalObjStruct {    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// from object/iterated_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sum {    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

// from object/iterated_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumOfFiniteSet {    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

// from object/iterated_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Product {    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

// from object/iterated_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductOfFiniteSet {    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

// from object/iterated_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reduce {    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

// from object/iterated_operations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetReduce {    pub set: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

// from object/numeric_constants.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Number {    pub normalized_value: String,
}

// from object/numeric_constants.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImaginaryUnit;

// from object/numeric_constants.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EulerNumber;

// from object/numeric_constants.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pi;

// from object/object.rs
#[derive(Clone, Debug, PartialEq, Eq)]
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

// from object/parameter.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundParamObj {
    pub name: String,
}

// from object/ranges_and_sequences.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Range {    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// from object/ranges_and_sequences.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedRange {    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// from object/ranges_and_sequences.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSeqSet {    pub set: Box<Obj>,
    pub n: Box<Obj>,
}

// from object/ranges_and_sequences.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqSet {    pub set: Box<Obj>,
}

// from object/ranges_and_sequences.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSeqListObj {    pub objs: Vec<Box<Obj>>,
}

// from object/rounding_and_extrema.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Floor {    pub arg: Box<Obj>,
}

// from object/rounding_and_extrema.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ceil {    pub arg: Box<Obj>,
}

// from object/rounding_and_extrema.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Min {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/rounding_and_extrema.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Max {    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// from object/set_aggregations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigUnion {    pub left: Box<Obj>,
}

// from object/set_aggregations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigIntersect {    pub left: Box<Obj>,
}

// from object/set_aggregations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexUnion {    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// from object/set_aggregations.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexIntersect {    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// from object/set_construction.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PowerSet {    pub set: Box<Obj>,
}

// from object/set_construction.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListSet {    pub list: Vec<Box<Obj>>,
}

// from object/set_construction.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetBuilder {    pub param_binding: String,
    pub param_set: Box<Obj>,
    pub facts: Vec<QuantifierFreeFact>,
}

// from object/standard_set.rs
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

// from object/structure_instances.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructObj {    pub name: AtomicName,
    pub params: Vec<Obj>,
}

// from object/structure_instances.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjAsStructInstanceWithFieldAccess {    pub obj: Box<Obj>,
    pub field_name: String,
    /// Filled by execution/instantiation, never by parsing. It preserves the
    /// field owner when substituting a typed receiver with an arbitrary value.
    pub resolved_struct_carrier: Option<Box<StructObj>>,
}

// from object/structure_instances.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstantiatedTemplateObj {    pub template_name: AtomicName,
    pub args: Vec<Obj>,
}

// from object/trigonometric_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sin {    pub arg: Box<Obj>,
}

// from object/trigonometric_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arcsin {    pub arg: Box<Obj>,
}

// from object/trigonometric_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cos {    pub arg: Box<Obj>,
}

// from object/trigonometric_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tan {    pub arg: Box<Obj>,
}

// from object/trigonometric_functions.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cot {    pub arg: Box<Obj>,
}

// from object/tuples_and_cartesian.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tuple {    pub args: Vec<Box<Obj>>,
}

// from object/tuples_and_cartesian.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleDim {    pub arg: Box<Obj>,
}

// from object/tuples_and_cartesian.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CartDim {    pub set: Box<Obj>,
}

// from object/tuples_and_cartesian.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proj {    pub set: Box<Obj>,
    pub dim: Box<Obj>,
}

// from object/tuples_and_cartesian.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneralCart {    pub index_set: Box<Obj>,
    pub family_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// from object/tuples_and_cartesian.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cart {    pub args: Vec<Box<Obj>>,
}

