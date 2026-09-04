import Mathlib

/-!
# The Litex object universe

This module is the identity layer of the new Litex representation.  A Litex
object is a persistent term, rather than a dynamically typed box around a
native Lean value.  Native values, membership, well-definedness, statements,
and compiler evidence are deliberately defined in later modules.

There are two kinds of operation heads:

* `BuiltinHead.core` contains the operations known by the Litex kernel;
* `BuiltinHead.extension` gives a namespaced escape hatch for a future module
  without changing the shape of `Object`.

Consequently, `Union`, `Sum`, matrices, structures, and user-facing numeric
operations all have the same object identity discipline.  Their mathematical
laws are not hidden in this syntax type: a later builtin-rule module must
provide the corresponding proof before a compiler bridge can use Mathlib.
-/

namespace Litex

/-! ## Stable names and builtin heads -/

/** A stable identity for a source-level symbol.  Binding provenance is kept
    out of the object term; bound variables use de Bruijn indices below. */
structure SymbolId where
  value : Nat
deriving DecidableEq, Inhabited, Repr

namespace SymbolId

def ofNat (value : Nat) : SymbolId :=
  ⟨value⟩

@[simp] theorem ofNat_value (value : Nat) : (ofNat value).value = value :=
  rfl

end SymbolId

/** The core operation vocabulary.  The names follow the current Litex object
    model, while the open `extension` branch in `BuiltinHead` keeps the term
    universe extensible. */
inductive CoreBuiltin where
  | imaginaryUnit
  | eulerNumber
  | pi
  | add
  | sub
  | mul
  | div
  | mod
  | quot
  | gcd
  | lcm
  | floor
  | ceil
  | min
  | max
  | exp
  | ln
  | sign
  | factorial
  | pow
  | abs
  | sin
  | arcsin
  | cos
  | tan
  | cot
  | realPart
  | imaginaryPart
  | complexAbs
  | sqrt
  | log
  | union
  | intersect
  | setMinus
  | bigUnion
  | bigIntersect
  | indexUnion
  | indexIntersect
  | powerSet
  | generalCart
  | listSet
  | setBuilder
  | fnSet
  | anonymousFn
  | cart
  | cartDim
  | proj
  | tupleDim
  | tuple
  | finiteSetSize
  | finiteSetMax
  | finiteSetMin
  | fnRange
  | replacement
  | sum
  | sumOfFiniteSet
  | product
  | productOfFiniteSet
  | reduce
  | finiteSetReduce
  | range
  | closedRange
  | finiteSeqSet
  | seqSet
  | finiteSeqList
  | objAtIndex
  | standardSet
  | matrixSet
  | matrixList
  | matrixAdd
  | matrixSub
  | matrixMul
  | matrixScalarMul
  | matrixPow
  | structObject
  | fieldAccess
  | templateInstance
  | oneSideInfinityInterval
  | interval
deriving DecidableEq, Inhabited, Repr

/** A builtin head is part of an object's identity.  Extensions are tagged by
    an id in their own namespace; they do not silently acquire core semantics. */
inductive BuiltinHead where
  | core : CoreBuiltin → BuiltinHead
  | extension : Nat → BuiltinHead
deriving DecidableEq, Inhabited, Repr

/-! ## Literal and object terms -/

/** Literal payloads that are already part of the object syntax.  In particular,
    `real` and `complex` are syntax-level literals, not an assertion that every
    object can be observed as a native number. */
inductive Literal where
  | boolean : Bool → Literal
  | natural : Nat → Literal
  | integer : Int → Literal
  | rational : ℚ → Literal
  | real : ℝ → Literal
  | complex : ℂ → Literal
  | text : String → Literal

/**
One identity space for all Litex expressions.

`variable` uses a de Bruijn index, so alpha-renamed binders have the same
shape.  `builtin` is deliberately generic: the operation's head identifies
the operation and its list preserves the source argument order.  `lambda`
stores binder-domain objects and a body; a predicate or set-builder therefore
remains inspectable syntax instead of a captured Lean closure.
*/
inductive Object where
  | variable : Nat → Object
  | symbol : SymbolId → Object
  | literal : Literal → Object
  | apply : Object → Object → Object
  | builtin : BuiltinHead → List Object → Object
  | lambda : List Object → Object → Object

namespace Object

/** Litex's function application constructor. */
def Apply (function argument : Object) : Object :=
  .apply function argument

/** Left-associated application of a finite argument list. */
def ApplyMany (function : Object) : List Object → Object
  | [] => function
  | argument :: arguments => ApplyMany (Apply function argument) arguments

/** Construct a core builtin application. */
def Core (operation : CoreBuiltin) (arguments : List Object) : Object :=
  .builtin (.core operation) arguments

/** Construct an extension builtin application. */
def Extension (identifier : Nat) (arguments : List Object) : Object :=
  .builtin (.extension identifier) arguments

/** Construct a lambda over de Bruijn-indexed variables. */
def Lambda (domains : List Object) (body : Object) : Object :=
  .lambda domains body

/-! Distinguished carrier symbols.  Their semantics is supplied by the later
    statement/builtin-rule layers; here they are simply stable object terms. -/

def N : Object :=
  .symbol (SymbolId.ofNat 0)

def Z : Object :=
  .symbol (SymbolId.ofNat 1)

def Q : Object :=
  .symbol (SymbolId.ofNat 2)

def R : Object :=
  .symbol (SymbolId.ofNat 3)

def C : Object :=
  .symbol (SymbolId.ofNat 4)

/-! Common constructors.  The full vocabulary remains available through
    `Core`; these names make the object representation readable in rules and
    generated terms. -/

def Union (left right : Object) : Object :=
  Core .union [left, right]

def Intersect (left right : Object) : Object :=
  Core .intersect [left, right]

def SetMinus (left right : Object) : Object :=
  Core .setMinus [left, right]

def BigUnion (family : Object) : Object :=
  Core .bigUnion [family]

def BigIntersect (family : Object) : Object :=
  Core .bigIntersect [family]

def IndexUnion (index family : Object) : Object :=
  Core .indexUnion [index, family]

def IndexIntersect (index family : Object) : Object :=
  Core .indexIntersect [index, family]

def PowerSet (set : Object) : Object :=
  Core .powerSet [set]

def ListSet (elements : List Object) : Object :=
  Core .listSet elements

def SetBuilder (base predicate : Object) : Object :=
  Core .setBuilder [base, predicate]

def FnSet (domain codomain graph : Object) : Object :=
  Core .fnSet [domain, codomain, graph]

def AnonymousFn (domains : List Object) (body : Object) : Object :=
  Core .anonymousFn (domains ++ [body])

def Cart (factors : List Object) : Object :=
  Core .cart factors

def GeneralCart (families : Object) : Object :=
  Core .generalCart [families]

def Tuple (elements : List Object) : Object :=
  Core .tuple elements

def FnRange (function : Object) : Object :=
  Core .fnRange [function]

def Replacement (domain function : Object) : Object :=
  Core .replacement [domain, function]

/** A bounded sum is represented as `(start, end, function)`, matching the
    current Litex object model. */
def Sum (start finish function : Object) : Object :=
  Core .sum [start, finish, function]

def SumOfFiniteSet (set function : Object) : Object :=
  Core .sumOfFiniteSet [set, function]

def Product (start finish function : Object) : Object :=
  Core .product [start, finish, function]

def ProductOfFiniteSet (set function : Object) : Object :=
  Core .productOfFiniteSet [set, function]

def Reduce (start finish function operation seed : Object) : Object :=
  Core .reduce [start, finish, function, operation, seed]

def FiniteSetReduce (set function operation seed : Object) : Object :=
  Core .finiteSetReduce [set, function, operation, seed]

def Range (start finish : Object) : Object :=
  Core .range [start, finish]

def ClosedRange (start finish : Object) : Object :=
  Core .closedRange [start, finish]

def ObjAtIndex (sequence index : Object) : Object :=
  Core .objAtIndex [sequence, index]

def StandardSet (name : Object) : Object :=
  Core .standardSet [name]

def MatrixSet (rows columns entry : Object) : Object :=
  Core .matrixSet [rows, columns, entry]

def MatrixList (rows : List Object) : Object :=
  Core .matrixList rows

def StructObject (fields : List Object) : Object :=
  Core .structObject fields

def FieldAccess (structure field : Object) : Object :=
  Core .fieldAccess [structure, field]

def TemplateInstance (template parameters : List Object) : Object :=
  Core .templateInstance (template :: parameters)

def Interval (left right : Object) : Object :=
  Core .interval [left, right]

/-! A shallow child view is useful to serializers and proof tooling.  It does
    not assign semantics to any builtin. -/

def children : Object → List Object
  | .variable _ => []
  | .symbol _ => []
  | .literal _ => []
  | .apply function argument => [function, argument]
  | .builtin _ arguments => arguments
  | .lambda domains body => domains ++ [body]

@[simp] theorem apply_self (function argument : Object) :
    Apply function argument = Apply function argument :=
  rfl

@[simp] theorem union_shape (left right : Object) :
    Union left right = .builtin (.core .union) [left, right] :=
  rfl

@[simp] theorem sum_shape (start finish function : Object) :
    Sum start finish function = .builtin (.core .sum) [start, finish, function] :=
  rfl

end Object

/-! ## Structural semantic equality

`Same` is intentionally only the identity/congruence skeleton.  It can carry
an explicit real-to-complex literal embedding, while operation-specific
equations (for example a Mathlib interpretation of `Union`) belong to
`builtin_rules.lean` and must be proved there.
-/

inductive Same : Object → Object → Prop where
  | refl (object : Object) : Same object object
  | symm {left right : Object} : Same left right → Same right left
  | trans {left middle right : Object} :
      Same left middle → Same middle right → Same left right
  | applyCongr {function function' argument argument' : Object} :
      Same function function' →
      Same argument argument' →
      Same (Object.Apply function argument) (Object.Apply function' argument')
  | builtinCongr {head : BuiltinHead} {arguments arguments' : List Object} :
      List.Forall₂ Same arguments arguments' →
      Same (.builtin head arguments) (.builtin head arguments')
  | lambdaCongr {domains domains' : List Object} {body body' : Object} :
      List.Forall₂ Same domains domains' →
      Same body body' →
      Same (.lambda domains body) (.lambda domains' body')
  | realComplex (value : ℝ) :
      Same (.literal (.real value)) (.literal (.complex (value : ℂ)))

namespace Same

theorem reflNoObservation (object : Object) : Same object object :=
  .refl object

theorem apply (function function' argument argument' : Object)
    (hf : Same function function') (ha : Same argument argument') :
    Same (Object.Apply function argument) (Object.Apply function' argument') :=
  .applyCongr hf ha

theorem builtin (head : BuiltinHead) {arguments arguments' : List Object}
    (h : List.Forall₂ Same arguments arguments') :
    Same (.builtin head arguments) (.builtin head arguments') :=
  .builtinCongr h

theorem lambda (domains domains' : List Object) (body body' : Object)
    (hd : List.Forall₂ Same domains domains') (hb : Same body body') :
    Same (.lambda domains body) (.lambda domains' body') :=
  .lambdaCongr hd hb

theorem realComplexLiteral (value : ℝ) :
    Same (Object.literal (.real value))
      (Object.literal (.complex (value : ℂ))) :=
  .realComplex value

end Same

end Litex
