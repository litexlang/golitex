//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: BoundName / IdentifierId for plain refs; FactId; SourceLine.
//!
//! Layout: top-level `Obj` is 16 families; each family enum wraps the same leaf
//! payload structs as before. Leaf structs follow in stable order after `Obj`.
//! Nested helpers that are not themselves `Obj` variants sit with their owning leaf.
//!
//! Pure-set model: every well-defined Litex object satisfies `$is_set`. Numerals,
//! function values, N/Z/Q/R/C, user sets, and fn spaces are all `Obj` — different
//! math interfaces, one carrier. Membership `$in` is a Fact between two objects.
//! The host `Object` type is meta-level only: not an internal universal set writable
//! on either side of `$in`. Unrestricted comprehension is forbidden; set formers
//! are bounded (SetBuilder, ranges, …) with their own WD obligations.

use super::fact::QuantifierFreeFact;
use super::names::{AtomicName, BoundName, PlainName};
use super::param::SetBoundParameterList;
use crate::runtime::runtime_ids::IdentifierId;

// Mathematical value / expression. Not a proposition (see Fact) and not an env action (see Stmt).
// Shape cut: one nesting level of family enums; leaf payloads unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obj {
    // Free or qualified name used as a value. Example: `a`, `m1::f0::Point`.
    Identifier(IdentifierObj),

    // Function application. Example: `f(1)`, `fn(x R) R {x}(a)`.
    FnObj(FnObj),

    // Numeric / named constants. Example: `2`, `2.5`, `i`, `e`, `pi`.
    Literal(Literal),

    // Built-in number sets and signed/nonzero variants. Example: `N`, `R+`, `Z*`.
    StandardSet(StandardSet),

    // Real arithmetic ops. Example: `1 + 2`, `abs(-3)`, `min(7, (-2))`.
    ArithmeticOperator(ArithmeticOperator),

    // Integer-specific ops. Example: `(-7) % 3`, `gcd(54, (-24))`, `3!`.
    IntegerOperator(IntegerOperator),

    // Trig and inverse trig. Example: `sin(0)`, `arctan(0)`.
    TrigOperator(TrigOperator),

    // Exp / log / sqrt. Example: `exp(0)`, `ln(1)`, `log(2, 8)`, `sqrt(4)`.
    ExpLogOperator(ExpLogOperator),

    // Complex-part ops. Example: `re(i)`, `img(i)`, `C_abs(i)`.
    ComplexOperator(ComplexOperator),

    // Set algebra and indexed families. Example: `union({1}, {2})`, `power_set({1})`.
    SetOperator(SetOperator),

    // Set constructors / formers. Example: `{1, 2}`, `{x R: x > 0}`, `range(1, 3)`.
    SetFormer(SetFormer),

    // Cartesian products, tuples, and indexing. Example: `cart(R, Z)`, `(1, 2)`, `(1, 2)[1]`.
    ProductShape(ProductShape),

    // Function spaces and concrete functions. Example: `fn(x R) R`, `fn(x R) R {x}`, `fn_range(f)`.
    FunctionSpace(FunctionSpace),

    // Indexed sums / products / fold. Example: `sum(1, n, f)`, `finite_set_product(S, f)`.
    IteratedOperator(IteratedOperator),

    // Finite-set statistics. Example: `finite_set_size({1, 2})`, `finite_set_max({1, 3})`.
    FiniteSetStat(FiniteSetStat),

    // Named structs and field paths. Example: `&Point`, `p.x`.
    StructAndFieldAccessObj(StructAndFieldAccessObj),

    // Template instance. Example: `\carrier_copy<R>`.
    InstantiatedTemplateObj(InstantiatedTemplateObj),
}

// Named / numeric constants that are not StandardSet.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    Number(Number),               // `2`, `2.4`
    ImaginaryUnit(ImaginaryUnit), // `i`
    EulerNumber(EulerNumber),     // `e`
    Pi(Pi),                       // `pi`
}

// Binary / unary real-or-complex arithmetic (carriers depend on the op).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArithmeticOperator {
    // What: addition. Surface: `a + b`. Domain: `a, b $in C`. Example: `1 + 2`.
    Add(Add),
    // What: subtraction. Surface: `a - b`. Domain: `a, b $in C`. Example: `5 - 2`.
    Sub(Sub),
    // What: additive inverse. Surface: `-a`. Domain: `a $in C`. Example: `-3`.
    Neg(Neg),
    // What: multiplication. Surface: `a * b`. Domain: `a, b $in C`. Example: `2 * 3`.
    Mul(Mul),
    // What: division. Surface: `a / b`. Domain: `a, b $in C` and `b != 0`. Example: `6 / 2`.
    Div(Div),
    // What: exponentiation. Surface: `a^b` (right-associative; tighter than `* /`).
    // Domain is multi-branch (not a single carrier pair); see `Pow`. Example: `2^3` (8).
    Pow(Pow),
    // Absolute value on reals. Surface: `abs(x)`. Example: `abs(-3)` (3).
    Abs(Abs),
    // Binary minimum of reals. Surface: `min(a, b)`. Example: `min(7, (-2))` (-2).
    Min(Min),
    // Binary maximum of reals. Surface: `max(a, b)`. Example: `max(7, (-2))` (7).
    Max(Max),
    // Greatest integer ≤ x. Surface: `floor(x)`. Example: `floor(3.7)` (3).
    Floor(Floor),
    // Least integer ≥ x. Surface: `ceil(x)`. Example: `ceil(3.2)` (4).
    Ceil(Ceil),
    // Sign of a real (−1 / 0 / 1). Surface: `sign(x)`. Example: `sign(-9)` (-1).
    Sign(Sign),
}

// Ops whose primary meaning is on integers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntegerOperator {
    // Remainder after integer division. Surface: `a % d`. Example: `(-7) % 3` (2).
    Mod(Mod),

    // Integer quotient: `a = d * quot(a, d) + a % d`. Surface: `quot(a, d)`. Example: `quot(-7, 3)` (-3).
    Quot(Quot),

    // Greatest common divisor. Surface: `gcd(a, b)`. Example: `gcd(54, (-24))` (6).
    Gcd(Gcd),

    // Least common multiple. Surface: `lcm(a, b)`. Example: `lcm(12, (-18))` (36).
    Lcm(Lcm),

    // Factorial. Surface: `factorial(n)`, also postfix `n!`. Example: `3!` (6).
    Factorial(Factorial),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrigOperator {
    Sin(Sin),
    Cos(Cos),
    Tan(Tan),
    Cot(Cot),
    Arcsin(Arcsin),
    Arccos(Arccos),
    Arctan(Arctan),
    Arccot(Arccot),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpLogOperator {
    Exp(Exp),   // exponential e^x. Surface: `exp(x)`. Example: `exp(0)` (1)
    Ln(Ln),     // natural log. Surface: `ln(x)`. Example: `ln(1)` (0)
    Log(Log),   // log with explicit base. Surface: `log(b, x)`. Example: `log(2, 8)` (3)
    Sqrt(Sqrt), // principal square root. Surface: `sqrt(x)`. Example: `sqrt(4)` (2)
}

// Complex coordinate / modulus ops (not ordinary real `abs`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComplexOperator {
    // Real part of a complex. Surface: `re(z)`. Example: `re(i)` (0).
    RealPart(RealPart),

    // Imaginary part of a complex. Surface: `img(z)`. Example: `img(i)` (1).
    ImaginaryPart(ImaginaryPart),

    // Complex modulus. Surface: `C_abs(z)`. Example: `C_abs(i)` (1).
    ComplexAbs(ComplexAbs),
}

// Set-forming operators on already available sets / families.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SetOperator {
    // Binary union: elements in A or in B.
    // Surface: `union(A, B)`. Example: `union({1}, {2, 3})` ({1, 2, 3}).
    Union(Union),

    // Binary intersection: elements in both A and B.
    // Surface: `intersect(A, B)`. Example: `intersect({1, 2}, {2, 3})` ({2}).
    Intersect(Intersect),

    // Relative complement: elements in A but not in B.
    // Surface: `set_minus(A, B)`. Example: `set_minus({1, 2, 3}, {2})` ({1, 3}).
    SetMinus(SetMinus),

    // Union of a family of sets (here: a set of sets).
    // Surface: `family_union(F)`. Example: `family_union({{1}, {2, 3}})` ({1, 2, 3}).
    FamilyUnion(FamilyUnion),

    // Intersection of a family of sets (here: a set of sets).
    // Surface: `family_intersect(F)`. Example: `family_intersect({{1, 2}, {2, 3}})` ({2}).
    FamilyIntersect(FamilyIntersect),

    // Indexed union ∪_{i ∈ I} A(i), where A is a set-valued family into ambient X.
    // Args: index set I, ambient set X, family function A : I → power_set(X).
    // Surface / Example: `index_union(I, X, A)`.
    IndexUnion(IndexUnion),

    // Indexed intersection ∩_{i ∈ I} A(i), same argument roles as IndexUnion.
    // Args: index set I, ambient set X, family function A : I → power_set(X).
    // Surface / Example: `index_intersect(I, X, A)`.
    IndexIntersect(IndexIntersect),

    // Set of all subsets of S. Surface: `power_set(S)`. Example: `power_set({1})` ({{}, {1}}).
    PowerSet(PowerSet),

    // Set of choice functions picking one point from each factor g(α), α ∈ I.
    // Args: index set I, ambient set S, family function g : I → S.
    // Surface / Example: `index_cart(I, S, g)`.
    IndexCart(IndexCart),
}

// Ways to build a set from elements, formulas, ranges, or sequence spaces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SetFormer {
    // Finite enumeration by listing elements. Example: `{1, 2}`.
    ListSet(ListSet),

    // Bounded comprehension `{x S: facts}` over an already available set S.
    // Example: `{x R: x > 0}`.
    SetBuilder(SetBuilder),

    // Half-open integer interval set {start, …, end-1}. Surface: `range(a, b)`. Example: `range(1, 3)` ({1, 2}).
    Range(Range),

    // Closed integer interval set {start, …, end}. Surface: `closed_range(a, b)`. Example: `closed_range(1, 2)` ({1, 2}).
    ClosedRange(ClosedRange),

    // Length-n sequences in S (n may be 0). Essentially the FnSet of maps from
    // the length-n index set into S. Example: `finite_seq(S, n)`.
    FiniteSeqSet(FiniteSeqSet),

    // Infinite sequences in S. Essentially the FnSet `fn(N) S`. Example: `seq(S)`.
    SeqSet(SeqSet),

    // One-sided real ray (unbounded on one side). Example: `'[a,)`, `'(,b]`.
    OneSideInfinityIntervalObj(OneSideInfinityIntervalObj),

    // Bounded real interval with open/closed endpoints. Example: `'[a, b]`, `'(a, b)`.
    IntervalObj(IntervalObj),
}

// Fixed-arity products, tuples, and their dimensions / projections / indexing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProductShape {
    // Cartesian product of two or more sets. Example: `cart(R, Z)`.
    Cart(Cart),

    // Ordered tuple value (an element of some cart). Example: `(1, 2)`.
    Tuple(Tuple),

    // Number of factors of a cart. Surface: `cart_dim(C)`. Example: `cart_dim(cart(R, Z))` (2).
    CartDim(CartDim),

    // Length of a tuple. Surface: `tuple_dim(t)`. Example: `tuple_dim((1, 2))` (2).
    TupleDim(TupleDim),

    // i-th factor *set* of a cart (1-based). Surface: `proj(C, i)`. Example: `proj(cart(R, Z), 1)` (R).
    Proj(Proj),

    // i-th *component* of a tuple / sequence (1-based). Surface: `t[i]`. Example: `(1, 2)[1]` (1).
    ObjAtIndex(ObjAtIndex),
}

// Function type, concrete function value, and image of a function.
// Language surface index: docs/Manual.md § Functions, application, and range
// (Function surface index). Named definitions: HaveFn* stmts and
// `have by fn_preimage` in ast/stmt.rs — not fields on these objects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionSpace {
    // Function space / type: maps with given domain carriers and return set.
    // Example: `fn(x R) R`, `fn(x R: x > 0) R`.
    FnSet(FnSet),

    // Concrete function belonging to a FnSet (binders + defining expression).
    // Example: `fn(x R) R {x + 1}`.
    AnonymousFn(AnonymousFn),

    // Image of a function (range as a set). Example: `fn_range(f)`.
    // See Manual § Functions, application, and range.
    FnRange(FnRange),
}

// Indexed sums / products and folds over integer ranges or finite sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IteratedOperator {
    // Sum of f(i) over a closed integer index range. Example: `sum(1, n, f)`.
    Sum(Sum),

    // Sum of f(x) over a finite set (order irrelevant). Example: `finite_set_sum(S, f)`.
    SumOfFiniteSet(SumOfFiniteSet),

    // Product of f(i) over a closed integer index range. Example: `product(1, n, f)`.
    Product(Product),

    // Product of f(x) over a finite set. Example: `finite_set_product(S, f)`.
    ProductOfFiniteSet(ProductOfFiniteSet),

    // Left fold of f over a closed integer index range with binary op and seed.
    // Example: `reduce(1, 3, f, op, seed)`.
    Reduce(Reduce),

    // Order-independent fold of f over a finite set with binary op and seed.
    // Example: `finite_set_reduce(S, f, op, seed)`.
    FiniteSetReduce(FiniteSetReduce),
}

// Statistics extracted from a finite set of numbers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FiniteSetStat {
    // Cardinality. Surface: `finite_set_size(S)`. Example: `finite_set_size({1, 2})` (2).
    FiniteSetSize(FiniteSetSize),

    // Greatest element. Surface: `finite_set_max(S)`. Example: `finite_set_max({1, 3})` (3).
    FiniteSetMax(FiniteSetMax),

    // Least element. Surface: `finite_set_min(S)`. Example: `finite_set_min({1, 3})` (1).
    FiniteSetMin(FiniteSetMin),
}

// Named structure types and field paths on structure values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructAndFieldAccessObj {
    // Structure type name, optionally parameterized. Example: `&Point`, `&Group<s>`.
    StructObj(StructObj),

    // Field path into a structure value (left-to-right). Example: `p.x`, `g.mul`.
    FieldAccess(FieldAccess),
}

// Free or module-qualified name used as an object (at most three `::` segments).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdentifierObj {
    // Local / session name with runtime IdentifierId. Example: `a`.
    Plain {
        id: IdentifierId,
        name: PlainName,
    },

    // Name qualified by export file id. Example surface: `f0::Point`.
    WithExportFileId {
        export_file_id: usize,
        name: PlainName,
    },

    // Name qualified by module id and export file id. Example surface: `m1::f0::Point`.
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
// Keep `Obj::ProductShape(ProductShape::ObjAtIndex(...))` for tuple/cart indexing such as `(1, 2)[1]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnObjHead {
    Identifier(IdentifierObj),
    // Anonymous function literal used as applied head. Example: `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FieldAccess(FieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnObj {
    pub head: Box<FnObjHead>,
    // Curried argument groups. Example: `f(a, b)(c)` → two groups.
    pub body: Vec<Vec<Box<Obj>>>,
}

// Decimal / integer numeral text after normalization. Example: `2`, `2.40` → `"2.4"`.
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

// What: addition of two objects.
// Surface: `a + b`
// Domain: `a, b $in C`.
// Example: `1 + 2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Add {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: subtraction of two objects.
// Surface: `a - b`
// Domain: `a, b $in C`.
// Example: `5 - 2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: additive inverse (unary minus).
// Surface: `-a` (not the same AST as `0 - a`).
// Domain: `a $in C`.
// Example: `-3`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Neg {
    pub arg: Box<Obj>,
}

// What: multiplication of two objects.
// Surface: `a * b`
// Domain: `a, b $in C`.
// Example: `2 * 3`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: division of two objects.
// Surface: `a / b`
// Domain: `a, b $in C` and `b != 0`.
// Example: `6 / 2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Div {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: Euclidean remainder.
// Surface: `a % d`
// Example: `(-7) % 3` (2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mod {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: Euclidean quotient.
// Surface: `quot(a, d)`
// Example: `quot(-7, 3)` (-3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quot {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: greatest common divisor.
// Surface: `gcd(a, b)`
// Example: `gcd(54, (-24))` (6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gcd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: least common multiple.
// Surface: `lcm(a, b)`
// Example: `lcm(12, (-18))` (36).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lcm {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: greatest integer ≤ arg.
// Surface: `floor(x)`
// Example: `floor(3.7)` (3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Floor {
    pub arg: Box<Obj>,
}

// What: least integer ≥ arg.
// Surface: `ceil(x)`
// Example: `ceil(3.2)` (4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ceil {
    pub arg: Box<Obj>,
}

// What: binary minimum of reals.
// Surface: `min(a, b)`
// Example: `min(7, (-2))` (-2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Min {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: binary maximum of reals.
// Surface: `max(a, b)`
// Example: `max(7, (-2))` (7).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Max {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: real exponential.
// Surface: `exp(x)`
// Example: `exp(0)` (1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exp {
    pub arg: Box<Obj>,
}

// What: natural logarithm.
// Surface: `ln(x)`
// Example: `ln(1)` (0).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ln {
    pub arg: Box<Obj>,
}

// What: sign of a real (−1 / 0 / 1).
// Surface: `sign(x)`
// Example: `sign(-9)` (-1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sign {
    pub arg: Box<Obj>,
}

// What: factorial.
// Surface: `factorial(n)`, also postfix `n!`
// Example: `3!` (6).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorial {
    pub arg: Box<Obj>,
}

// What: exponentiation `base^exponent`.
// Surface: `a^b` (right-associative; write `t^(-1)`, not `t^-1`).
// Example: `2^3` (8).
//
// Domain is intentionally multi-branch (WD tries these in order in new_pipeline):
// - complex base + natural exponent: `base $in C`, `exponent $in N`
//   (includes the convention `0^0 = 1`)
// - nonzero complex base + integer exponent: `base $in C`, `base != 0`,
//   `exponent $in Z`
//
// Broader real/rational branches (e.g. positive real base with real exponent)
// are documented in Manual / legacy routes; general `C^R` / `C^C` is out of
// scope. Invalid examples: `i^(1/2)`, `0^(-1)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

// What: absolute value on reals.
// Surface: `abs(x)`
// Example: `abs(-3)` (3).
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

// Arccos
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arccos {
    pub arg: Box<Obj>,
}

// Arctan
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arctan {
    pub arg: Box<Obj>,
}

// Arccot
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arccot {
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

// What: real part of a complex.
// Surface: `re(z)`
// Example: `re(i)` (0).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealPart {
    pub arg: Box<Obj>,
}

// What: imaginary part of a complex.
// Surface: `img(z)`
// Example: `img(i)` (1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImaginaryPart {
    pub arg: Box<Obj>,
}

// What: complex modulus.
// Surface: `C_abs(z)`
// Example: `C_abs(i)` (1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexAbs {
    pub arg: Box<Obj>,
}

// What: principal square root.
// Surface: `sqrt(x)`
// Example: `sqrt(4)` (2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sqrt {
    pub arg: Box<Obj>,
}

// What: logarithm with explicit base.
// Surface: `log(b, x)`
// Example: `log(2, 8)` (3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Log {
    pub base: Box<Obj>,
    pub arg: Box<Obj>,
}

// What: binary union of two sets.
// Surface: `union(A, B)`
// Example: `union({1}, {2, 3})` ({1, 2, 3}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Union {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: binary intersection of two sets.
// Surface: `intersect(A, B)`
// Example: `intersect({1, 2}, {2, 3})` ({2}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Intersect {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: relative complement (elements in left but not in right).
// Surface: `set_minus(A, B)`
// Example: `set_minus({1, 2, 3}, {2})` ({1, 3}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetMinus {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

// What: union of a family of sets — in Litex that family is a set of sets.
// Surface: `family_union(F)`
// Example: `family_union({{1}, {2, 3}})` ({1, 2, 3}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyUnion {
    pub left: Box<Obj>,
}

// What: intersection of a family of sets — in Litex that family is a set of sets.
// Surface: `family_intersect(F)`
// Example: `family_intersect({{1, 2}, {2, 3}})` ({2}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyIntersect {
    pub left: Box<Obj>,
}

// Indexed union ∪_{i ∈ I} A(i) ⊆ X.
// `index_union(I, X, A)` ↔ fields: index_set=I, ambient_set=X, family_fn=A
// where A : I → power_set(X).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexUnion {
    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// Indexed intersection ∩_{i ∈ I} A(i) ⊆ X; same field roles as IndexUnion.
// `index_intersect(I, X, A)` ↔ index_set=I, ambient_set=X, family_fn=A.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexIntersect {
    pub index_set: Box<Obj>,
    pub ambient_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// What: power set of a set.
// Surface: `power_set(S)`
// Example: `power_set({1})` ({{}, {1}}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PowerSet {
    pub set: Box<Obj>,
}

// Set of choice functions on a family g indexed by I (values live in ambient S).
// `index_cart(I, S, g)` ↔ index_set=I, family_set=S, family_fn=g.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexCart {
    pub index_set: Box<Obj>,
    pub family_set: Box<Obj>,
    pub family_fn: Box<Obj>,
}

// Finite enumeration set. Example: `{1, 2}`.
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
// Surface index: Manual § Functions, application, and range.
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

// Fixed-arity cartesian product of sets. Example: `cart(R, Z)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cart {
    pub args: Vec<Box<Obj>>,
}

// Dimension of a cartesian product set.
// Surface: `cart_dim(C)`
// Example: `cart_dim(cart(R, Z))` (2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CartDim {
    pub set: Box<Obj>,
}

// i-th factor set of a cart.
// Surface: `proj(C, i)`
// Example: `proj(cart(R, Z), 1)` (R).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proj {
    pub set: Box<Obj>,
    pub dim: Box<Obj>,
}

// Length of a tuple.
// Surface: `tuple_dim(t)`
// Example: `tuple_dim((1, 2))` (2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TupleDim {
    pub arg: Box<Obj>,
}

// Ordered tuple value. Example: `(1, 2)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tuple {
    pub args: Vec<Box<Obj>>,
}

// What: cardinality of a finite set.
// Surface: `finite_set_size(S)`
// Example: `finite_set_size({1, 2})` (2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetSize {
    pub set: Box<Obj>,
}

// What: maximum of a finite real/integer set.
// Surface: `finite_set_max(S)`
// Example: `finite_set_max({1, 3})` (3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetMax {
    pub set: Box<Obj>,
}

// What: minimum of a finite real/integer set.
// Surface: `finite_set_min(S)`
// Example: `finite_set_min({1, 3})` (1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetMin {
    pub set: Box<Obj>,
}

// Image of a function. Example: `fn_range(f)`.
// Surface index: Manual § Functions, application, and range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnRange {
    pub function: Box<Obj>,
}

// Sum of f(i) over a closed integer index range [start, end]. Example: `sum(1, n, f)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sum {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

// Sum of f over a finite set. Example: `finite_set_sum(S, f)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

// Product of f(i) over a closed integer index range [start, end]. Example: `product(1, n, f)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Product {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

// Product of f over a finite set. Example: `finite_set_product(S, f)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductOfFiniteSet {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
}

// Left fold of f over a closed integer index range with binary op and seed.
// Example: `reduce(1, 3, f, op, seed)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reduce {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

// Fold over a finite set. Example: `finite_set_reduce(S, f, op, seed)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSetReduce {
    pub set: Box<Obj>,
    pub func: Box<Obj>,
    pub op: Box<Obj>,
    pub seed: Box<Obj>,
}

// Half-open integer range {start, …, end-1}.
// Surface: `range(a, b)`
// Example: `range(1, 3)` ({1, 2}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Range {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// Closed integer range {start, …, end}.
// Surface: `closed_range(a, b)`
// Example: `closed_range(1, 2)` ({1, 2}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedRange {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

// Length-n sequences in S. Essentially the FnSet of maps from the length-n
// index set into S. Example: `finite_seq(S, n)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSeqSet {
    pub set: Box<Obj>,
    pub n: Box<Obj>,
}

// Infinite sequences in S. Essentially the FnSet `fn(N) S`. Example: `seq(S)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqSet {
    pub set: Box<Obj>,
}

// What: tuple / sequence indexing (1-based).
// Surface: `t[i]`
// Example: `(1, 2)[1]` (1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjAtIndex {
    pub obj: Box<Obj>,
    pub index: Box<Obj>,
}

// Built-in number sets and common signed / nonzero variants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StandardSet {
    NPos,  // positive naturals `N+`
    N,     // naturals including 0 `N`
    Q,     // rationals `Q`
    Z,     // integers `Z`
    R,     // reals `R`
    C,     // complexes `C`
    QPos,  // positive rationals `Q+`
    RPos,  // positive reals `R+`
    QNeg,  // negative rationals `Q-`
    ZNeg,  // negative integers `Z-`
    RNeg,  // negative reals `R-`
    QStar, // nonzero rationals `Q*`
    ZStar, // nonzero integers `Z*`
    RStar, // nonzero reals `R*`
    CStar, // nonzero complexes `C*`
}

// Named structure type, possibly with parameters. Example: `&Point`, `&Group<s>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructObj {
    pub name: AtomicName,
    pub params: Vec<Obj>,
}

// Field path. Example: `p.x`, `g.mul`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldAccess {
    pub obj: Box<Obj>,
    pub fields: Vec<String>,
}

// Instantiated template object. Example: `\carrier_copy<R>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstantiatedTemplateObj {
    pub template_name: AtomicName,
    pub args: Vec<Obj>,
}

// One-sided real rays (unbounded on one side). Endpoint openness is in the variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OneSideInfinityIntervalObj {
    // (a, +∞). Example: `'(a,)`.
    LowerOpen(OneSideInfinityIntervalObjStruct),
    // [a, +∞). Example: `'[a,)`.
    LowerClosed(OneSideInfinityIntervalObjStruct),
    // (−∞, a). Example: `'(,a)`.
    UpperOpen(OneSideInfinityIntervalObjStruct),
    // (−∞, a]. Example: `'(,a]`.
    UpperClosed(OneSideInfinityIntervalObjStruct),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OneSideInfinityIntervalObjStruct {
    pub start: Box<Obj>,
}

// Bounded real intervals. Endpoint openness is in the variant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntervalObj {
    // (a, b). Example: `'(a, b)`.
    LeftOpenRightOpen(IntervalObjStruct),
    // (a, b]. Example: `'(a, b]`.
    LeftOpenRightClosed(IntervalObjStruct),
    // [a, b). Example: `'[a, b)`.
    LeftClosedRightOpen(IntervalObjStruct),
    // [a, b]. Example: `'[a, b]`.
    LeftClosedRightClosed(IntervalObjStruct),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntervalObjStruct {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}
