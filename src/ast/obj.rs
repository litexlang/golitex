//! Framework AST data shapes.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: BoundName / IdentifierId for plain refs; FactId; SourceLine.
//!
//! Layout: top-level `Obj` groups mathematical families; each family enum wraps the same leaf
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
    MatrixOperator(MatrixOperator),
    // Finite real supremum/infimum selected only from proved candidate/existence.
    BoundOperator(BoundOperator),
    IntegralOperator(IntegralOperator),
    DerivativeOperator(DerivativeOperator),
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

    // Real hyperbolic functions. Example: `sinh(0)`, `cosh(0)`.
    HyperbolicOperator(HyperbolicOperator),

    // Finite real limits selected only after convergence is proved.
    LimitOperator(LimitOperator),

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
    Sec(Sec),
    Csc(Csc),
    Arcsin(Arcsin),
    Arccos(Arccos),
    Arctan(Arctan),
    Arccot(Arccot),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HyperbolicOperator {
    Sinh(Sinh),
    Cosh(Cosh),
    Tanh(Tanh),
    Coth(Coth),
    Sech(Sech),
    Csch(Csch),
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
    Conjugate(Conjugate),
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
    SymmetricDifference(SymmetricDifference),

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
    // the one-based index set 1..n into S. Example: `finite_seq(S, n)`.
    FiniteSeqSet(FiniteSeqSet),

    // All two-argument functions on 1..rows × 1..cols with values in set.
    MatrixSet(MatrixSet),

    // Infinite sequences in S. Essentially the FnSet `fn(N+) S`. Example: `seq(S)`.
    SeqSet(SeqSet),

    // One-sided real ray (unbounded on one side). Example: `'[a,)`, `'(,b]`.
    OneSideInfinityIntervalObj(OneSideInfinityIntervalObj),

    // Bounded real interval with open/closed endpoints. Example: `'[a, b]`, `'(a, b)`.
    IntervalObj(IntervalObj),
}

// Finite function values and Cartesian sets of such functions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProductShape {
    Cart(Cart),
    Tuple(Tuple),
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

    // Strict composition: outer(inner(args)), retaining the complete inner domain.
    Composition(Composition),

    // Image of a function (range as a set). Example: `fn_range(f)`.
    // See Manual § Functions, application, and range.
    FnRange(FnRange),

    // Input fiber of a value. Example: `preimage(f, y)`.
    Preimage(Preimage),

    // Inputs whose outputs belong to a set. Example: `preimage_set(f, Y)`.
    PreimageSet(PreimageSet),
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

// Applied function expressions. WD determines the actual callable contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnObjHead {
    Identifier(IdentifierObj),
    // Anonymous function literal used as applied head. Example: `fn(x R) R {x}(a)`.
    AnonymousFnLiteral(Box<AnonymousFn>),
    FieldAccess(FieldAccess),
    InstantiatedTemplateObj(InstantiatedTemplateObj),
    Object(Box<Obj>),
}

impl FnObjHead {
    pub fn from_obj(obj: Obj) -> Self {
        match obj {
            Obj::Identifier(id) => Self::Identifier(id),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(value)) => {
                Self::AnonymousFnLiteral(Box::new(value))
            }
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(value)) => {
                Self::FieldAccess(value)
            }
            Obj::InstantiatedTemplateObj(value) => Self::InstantiatedTemplateObj(value),
            other => Self::Object(Box::new(other)),
        }
    }
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
// Domain is intentionally multi-branch (WD tries these in order):
// - closed positive rational base + closed rational noninteger exponent
// - real base + natural exponent (includes `0^0 = 1`)
// - complex base + natural exponent
// - nonzero complex base + integer exponent
// - positive real base + real exponent
// - nonnegative real base + positive real exponent
//
// General `C^R` / `C^C` and negative bases with noninteger exponents remain
// outside this domain. Invalid examples: `i^(1/2)`, `0^(-1)`.
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

// Strict function composition. Both spellings `compose(f,g)` / `f ∘ g`
// retain the tree; signatures and proof scopes belong to WD evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Composition {
    pub outer: Box<Obj>,
    pub inner: Box<Obj>,
}

impl Composition {
    pub fn new(outer: Obj, inner: Obj) -> Self {
        Self {
            outer: Box::new(outer),
            inner: Box::new(inner),
        }
    }
}

// Image of a function. Example: `fn_range(f)`.
// Surface index: Manual § Functions, application, and range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnRange {
    pub function: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Preimage {
    pub function: Box<Obj>,
    pub value: Box<Obj>,
}

impl Preimage {
    pub fn new(function: Obj, value: Obj) -> Self {
        Self {
            function: Box::new(function),
            value: Box::new(value),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreimageSet {
    pub function: Box<Obj>,
    pub target_set: Box<Obj>,
}

impl PreimageSet {
    pub fn new(function: Obj, target_set: Obj) -> Self {
        Self {
            function: Box::new(function),
            target_set: Box::new(target_set),
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixSet {
    pub set: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatrixOperator {
    Determinant(Determinant),
    ZeroMatrix(ZeroMatrix),
    IdentityMatrix(IdentityMatrix),
    Transpose(MatrixTranspose),
    ConjugateTranspose(MatrixConjugateTranspose),
    Trace(MatrixTrace),
    Add(MatrixAdd),
    Subtract(MatrixSubtract),
    Scale(MatrixScale),
    Multiply(MatrixMultiply),
    Apply(MatrixApply),
    Power(MatrixPower),
    Inverse(MatrixInverse),
    Rank(MatrixRank),
    Minor(MatrixMinor),
    Cofactor(MatrixCofactor),
    Adjugate(MatrixAdjugate),
    Diagonal(MatrixDiagonal),
    OuterProduct(MatrixOuterProduct),
    InnerProduct(FiniteInnerProduct),
    EuclideanNorm(EuclideanNorm),
    FrobeniusNorm(MatrixFrobeniusNorm),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Determinant {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZeroMatrix {
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityMatrix {
    pub order: Box<Obj>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixTranspose {
    pub matrix: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixConjugateTranspose {
    pub matrix: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixTrace {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixAdd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixSubtract {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixScale {
    pub scalar: Box<Obj>,
    pub matrix: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixMultiply {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub rows: Box<Obj>,
    pub inner: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixApply {
    pub matrix: Box<Obj>,
    pub vector: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixPower {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
    pub exponent: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixInverse {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixRank {
    pub matrix: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixMinor {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
    pub row: Box<Obj>,
    pub col: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixCofactor {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
    pub row: Box<Obj>,
    pub col: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixAdjugate {
    pub matrix: Box<Obj>,
    pub order: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixDiagonal {
    pub vector: Box<Obj>,
    pub order: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixOuterProduct {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteInnerProduct {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub dimension: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EuclideanNorm {
    pub vector: Box<Obj>,
    pub dimension: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixFrobeniusNorm {
    pub matrix: Box<Obj>,
    pub rows: Box<Obj>,
    pub cols: Box<Obj>,
}

impl MatrixOperator {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Determinant(_) => "det",
            Self::ZeroMatrix(_) => "zero_matrix",
            Self::IdentityMatrix(_) => "identity_matrix",
            Self::Transpose(_) => "transpose",
            Self::ConjugateTranspose(_) => "conjugate_transpose",
            Self::Trace(_) => "trace",
            Self::Add(_) => "matrix_add",
            Self::Subtract(_) => "matrix_sub",
            Self::Scale(_) => "matrix_scale",
            Self::Multiply(_) => "matrix_mul",
            Self::Apply(_) => "matrix_apply",
            Self::Power(_) => "matrix_power",
            Self::Inverse(_) => "matrix_inverse",
            Self::Rank(_) => "matrix_rank",
            Self::Minor(_) => "matrix_minor",
            Self::Cofactor(_) => "matrix_cofactor",
            Self::Adjugate(_) => "matrix_adjugate",
            Self::Diagonal(_) => "diagonal_matrix",
            Self::OuterProduct(_) => "outer_product",
            Self::InnerProduct(_) => "inner_product",
            Self::EuclideanNorm(_) => "euclidean_norm",
            Self::FrobeniusNorm(_) => "frobenius_norm",
        }
    }

    pub fn operand_refs(&self) -> Vec<&Obj> {
        match self {
            Self::Determinant(x) => vec![&x.matrix, &x.order],
            Self::ZeroMatrix(x) => vec![&x.rows, &x.cols],
            Self::IdentityMatrix(x) => vec![&x.order],
            Self::Transpose(x) => vec![&x.matrix, &x.rows, &x.cols],
            Self::ConjugateTranspose(x) => vec![&x.matrix, &x.rows, &x.cols],
            Self::Trace(x) => vec![&x.matrix, &x.order],
            Self::Add(x) => vec![&x.left, &x.right, &x.rows, &x.cols],
            Self::Subtract(x) => vec![&x.left, &x.right, &x.rows, &x.cols],
            Self::Scale(x) => vec![&x.scalar, &x.matrix, &x.rows, &x.cols],
            Self::Multiply(x) => vec![&x.left, &x.right, &x.rows, &x.inner, &x.cols],
            Self::Apply(x) => vec![&x.matrix, &x.vector, &x.rows, &x.cols],
            Self::Power(x) => vec![&x.matrix, &x.order, &x.exponent],
            Self::Inverse(x) => vec![&x.matrix, &x.order],
            Self::Rank(x) => vec![&x.matrix, &x.rows, &x.cols],
            Self::Minor(x) => vec![&x.matrix, &x.order, &x.row, &x.col],
            Self::Cofactor(x) => vec![&x.matrix, &x.order, &x.row, &x.col],
            Self::Adjugate(x) => vec![&x.matrix, &x.order],
            Self::Diagonal(x) => vec![&x.vector, &x.order],
            Self::OuterProduct(x) => vec![&x.left, &x.right, &x.rows, &x.cols],
            Self::InnerProduct(x) => vec![&x.left, &x.right, &x.dimension],
            Self::EuclideanNorm(x) => vec![&x.vector, &x.dimension],
            Self::FrobeniusNorm(x) => vec![&x.matrix, &x.rows, &x.cols],
        }
    }

    pub fn try_map_operands<E>(
        &self,
        mut map: impl FnMut(&Obj) -> Result<Obj, E>,
    ) -> Result<Self, E> {
        Ok(match self {
            Self::Determinant(x) => Self::Determinant(Determinant {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
            }),
            Self::ZeroMatrix(x) => Self::ZeroMatrix(ZeroMatrix {
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::IdentityMatrix(x) => Self::IdentityMatrix(IdentityMatrix {
                order: Box::new(map(&x.order)?),
            }),
            Self::Transpose(x) => Self::Transpose(MatrixTranspose {
                matrix: Box::new(map(&x.matrix)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::ConjugateTranspose(x) => Self::ConjugateTranspose(MatrixConjugateTranspose {
                matrix: Box::new(map(&x.matrix)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Add(x) => Self::Add(MatrixAdd {
                left: Box::new(map(&x.left)?),
                right: Box::new(map(&x.right)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Subtract(x) => Self::Subtract(MatrixSubtract {
                left: Box::new(map(&x.left)?),
                right: Box::new(map(&x.right)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Scale(x) => Self::Scale(MatrixScale {
                scalar: Box::new(map(&x.scalar)?),
                matrix: Box::new(map(&x.matrix)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Multiply(x) => Self::Multiply(MatrixMultiply {
                left: Box::new(map(&x.left)?),
                right: Box::new(map(&x.right)?),
                rows: Box::new(map(&x.rows)?),
                inner: Box::new(map(&x.inner)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Apply(x) => Self::Apply(MatrixApply {
                matrix: Box::new(map(&x.matrix)?),
                vector: Box::new(map(&x.vector)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Power(x) => Self::Power(MatrixPower {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
                exponent: Box::new(map(&x.exponent)?),
            }),
            Self::Inverse(x) => Self::Inverse(MatrixInverse {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
            }),
            Self::Rank(x) => Self::Rank(MatrixRank {
                matrix: Box::new(map(&x.matrix)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Minor(x) => Self::Minor(MatrixMinor {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
                row: Box::new(map(&x.row)?),
                col: Box::new(map(&x.col)?),
            }),
            Self::Cofactor(x) => Self::Cofactor(MatrixCofactor {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
                row: Box::new(map(&x.row)?),
                col: Box::new(map(&x.col)?),
            }),
            Self::Adjugate(x) => Self::Adjugate(MatrixAdjugate {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
            }),
            Self::Diagonal(x) => Self::Diagonal(MatrixDiagonal {
                vector: Box::new(map(&x.vector)?),
                order: Box::new(map(&x.order)?),
            }),
            Self::OuterProduct(x) => Self::OuterProduct(MatrixOuterProduct {
                left: Box::new(map(&x.left)?),
                right: Box::new(map(&x.right)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::InnerProduct(x) => Self::InnerProduct(FiniteInnerProduct {
                left: Box::new(map(&x.left)?),
                right: Box::new(map(&x.right)?),
                dimension: Box::new(map(&x.dimension)?),
            }),
            Self::EuclideanNorm(x) => Self::EuclideanNorm(EuclideanNorm {
                vector: Box::new(map(&x.vector)?),
                dimension: Box::new(map(&x.dimension)?),
            }),
            Self::FrobeniusNorm(x) => Self::FrobeniusNorm(MatrixFrobeniusNorm {
                matrix: Box::new(map(&x.matrix)?),
                rows: Box::new(map(&x.rows)?),
                cols: Box::new(map(&x.cols)?),
            }),
            Self::Trace(x) => Self::Trace(MatrixTrace {
                matrix: Box::new(map(&x.matrix)?),
                order: Box::new(map(&x.order)?),
            }),
        })
    }
}

// Infinite sequences in S. Essentially the FnSet `fn(N+) S`. Example: `seq(S)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqSet {
    pub set: Box<Obj>,
}

// What: tuple / sequence indexing (1-based).
// Surface: `t[i]`
// Example: `(1, 2)[1]` (1).

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

// `sec`: real argument, cos(arg) != 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sec {
    pub arg: Box<Obj>,
}

// `csc`: real argument, sin(arg) != 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Csc {
    pub arg: Box<Obj>,
}

// `conj`: complex argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conjugate {
    pub arg: Box<Obj>,
}

// `sinh`: real argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sinh {
    pub arg: Box<Obj>,
}

// `cosh`: real argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cosh {
    pub arg: Box<Obj>,
}

// `tanh`: real argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tanh {
    pub arg: Box<Obj>,
}

// `coth`: nonzero real argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coth {
    pub arg: Box<Obj>,
}

// `sech`: real argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sech {
    pub arg: Box<Obj>,
}

// `csch`: nonzero real argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Csch {
    pub arg: Box<Obj>,
}

// `set_diff`: two well-defined objects in the pure-set model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymmetricDifference {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundOperator {
    Supremum(Supremum),
    Infimum(Infimum),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Supremum {
    pub set: Box<Obj>,
}
impl Supremum {
    pub fn new(set: Obj) -> Self {
        Self { set: Box::new(set) }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Infimum {
    pub set: Box<Obj>,
}
impl Infimum {
    pub fn new(set: Obj) -> Self {
        Self { set: Box::new(set) }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LimitOperator {
    Sequence(SequenceLimit),
    SequenceLimsup(SequenceLimsup),
    SequenceLiminf(SequenceLiminf),
    Function(FunctionLimit),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SequenceLimit {
    pub sequence: Box<Obj>,
}
impl SequenceLimit {
    pub fn new(sequence: Obj) -> Self {
        Self {
            sequence: Box::new(sequence),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SequenceLimsup {
    pub sequence: Box<Obj>,
}
impl SequenceLimsup {
    pub fn new(sequence: Obj) -> Self {
        Self {
            sequence: Box::new(sequence),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SequenceLiminf {
    pub sequence: Box<Obj>,
}
impl SequenceLiminf {
    pub fn new(sequence: Obj) -> Self {
        Self {
            sequence: Box::new(sequence),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionLimit {
    pub function: Box<Obj>,
    pub approach: LimitApproach,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LimitApproach {
    AtPoint(Box<Obj>),
    FromLeft(Box<Obj>),
    FromRight(Box<Obj>),
    AtPositiveInfinity,
    AtNegativeInfinity,
}

impl LimitApproach {
    pub fn with_point(&self, point: Obj) -> Self {
        match self {
            Self::AtPoint(_) => Self::AtPoint(Box::new(point)),
            Self::FromLeft(_) => Self::FromLeft(Box::new(point)),
            Self::FromRight(_) => Self::FromRight(Box::new(point)),
            Self::AtPositiveInfinity => Self::AtPositiveInfinity,
            Self::AtNegativeInfinity => Self::AtNegativeInfinity,
        }
    }
    pub fn try_map_point<E>(&self, f: impl FnOnce(&Obj) -> Result<Obj, E>) -> Result<Self, E> {
        Ok(match self.point() {
            Some(p) => self.with_point(f(p)?),
            None => self.clone(),
        })
    }
    pub fn operand_refs<'a>(&'a self, function: &'a Obj, value: &'a Obj) -> Vec<&'a Obj> {
        let mut args = vec![function];
        args.extend(self.point());
        args.push(value);
        args
    }
    pub fn threshold_set(&self) -> Obj {
        Obj::StandardSet(if self.point().is_some() {
            StandardSet::RPos
        } else {
            StandardSet::R
        })
    }
    pub fn same_direction(&self, other: &Self) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(other)
    }
    pub fn value_name(&self) -> &'static str {
        match self {
            Self::AtPoint(_) => "lim",
            Self::FromLeft(_) => "lim_left",
            Self::FromRight(_) => "lim_right",
            Self::AtPositiveInfinity => "lim_pos_inf",
            Self::AtNegativeInfinity => "lim_neg_inf",
        }
    }
    pub fn predicate_name(&self) -> &'static str {
        match self {
            Self::AtPoint(_) => "has_limit_at",
            Self::FromLeft(_) => "has_limit_left",
            Self::FromRight(_) => "has_limit_right",
            Self::AtPositiveInfinity => "has_limit_pos_inf",
            Self::AtNegativeInfinity => "has_limit_neg_inf",
        }
    }

    pub fn point(&self) -> Option<&Obj> {
        match self {
            Self::AtPoint(point) | Self::FromLeft(point) | Self::FromRight(point) => Some(point),
            Self::AtPositiveInfinity | Self::AtNegativeInfinity => None,
        }
    }
}

impl FunctionLimit {
    pub fn with_approach(function: Obj, approach: LimitApproach) -> Self {
        Self {
            function: Box::new(function),
            approach,
        }
    }

    pub fn new(function: Obj, point: Obj) -> Self {
        Self {
            function: Box::new(function),
            approach: LimitApproach::AtPoint(Box::new(point)),
        }
    }
}

/// Finite real derivative selected only from proved candidate/existence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivativeOperator {
    AtPoint(DerivativeAt),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivativeAt {
    pub function: Box<Obj>,
    pub point: Box<Obj>,
}
impl DerivativeAt {
    pub fn new(function: Obj, point: Obj) -> Self {
        Self {
            function: Box::new(function),
            point: Box::new(point),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntegralOperator {
    Riemann(RiemannIntegral),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RiemannIntegral {
    pub function: Box<Obj>,
    pub lower: Box<Obj>,
    pub upper: Box<Obj>,
}
impl RiemannIntegral {
    pub fn new(function: Obj, lower: Obj, upper: Obj) -> Self {
        Self {
            function: Box::new(function),
            lower: Box::new(lower),
            upper: Box::new(upper),
        }
    }
}
