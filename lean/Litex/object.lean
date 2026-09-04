import Mathlib

/-!
# The Litex object universe

`Object` is the syntax/identity layer of Litex.  Its constructors mirror the
outer variants of the Rust `Obj` enum.  A bound occurrence is an `Atom.bound`
with a stable `SymbolId`; it is not a Lean variable, lambda, or dynamically
typed box.  Conditions stored inside set/function constructors are syntax
(`Formula`) and acquire meaning only in `statement.lean`/`builtin_rules.lean`.
-/

namespace Litex

/-! ## Stable source names -/

inductive ReservedSymbol where
  | N
  | Z
  | Q
  | R
  | C
deriving DecidableEq, Inhabited, Repr

inductive SymbolId where
  | reserved : ReservedSymbol → SymbolId
  | user : Nat → SymbolId
deriving DecidableEq, Inhabited, Repr

structure Symbol where
  id : SymbolId
  displayName : String
deriving DecidableEq, Inhabited, Repr

structure QualifiedSymbol where
  moduleName : String
  name : String
  id : SymbolId
deriving DecidableEq, Inhabited, Repr

inductive Atom where
  | identifier : Symbol → Atom
  | identifierWithMod : QualifiedSymbol → Atom
  | bound : Symbol → Atom
deriving DecidableEq, Inhabited, Repr

namespace SymbolId

def ofNat (value : Nat) : SymbolId :=
  .user value

@[simp] theorem ofNat_eq_user (value : Nat) : ofNat value = .user value :=
  rfl

theorem user_ne_reserved (value : Nat) (name : ReservedSymbol) :
    SymbolId.user value ≠ SymbolId.reserved name := by
  intro h
  cases h

end SymbolId

/-! ## Literal payloads and non-object syntax payloads -/

structure Number where
  normalizedValue : String
deriving DecidableEq, Inhabited, Repr

inductive Literal where
  | boolean : Bool → Literal
  | natural : Nat → Literal
  | integer : Int → Literal
  | rational : ℚ → Literal
  | real : ℝ → Literal
  | complex : ℂ → Literal
  | text : String → Literal
deriving Inhabited

inductive IntervalSide where
  | leftOpen
  | leftClosed
  | rightOpen
  | rightClosed
deriving DecidableEq, Inhabited, Repr

inductive IntervalBoundary where
  | leftOpenRightOpen
  | leftOpenRightClosed
  | leftClosedRightOpen
  | leftClosedRightClosed
deriving DecidableEq, Inhabited, Repr

/-! `Formula` is deliberately only a source formula.  It contains no proof,
    WD cache, environment, or Lean closure. -/

mutual

  inductive Object where
    | atom : Atom → Object
    | fnObj : FnHead → List (List Object) → Object
    | number : Number → Object
    | literal : Literal → Object
    | imaginaryUnit : Object
    | eulerNumber : Object
    | pi : Object
    | add : Object → Object → Object
    | sub : Object → Object → Object
    | mul : Object → Object → Object
    | div : Object → Object → Object
    | mod : Object → Object → Object
    | quot : Object → Object → Object
    | gcd : Object → Object → Object
    | lcm : Object → Object → Object
    | floor : Object → Object
    | ceil : Object → Object
    | min : Object → Object → Object
    | max : Object → Object → Object
    | exp : Object → Object
    | ln : Object → Object
    | sign : Object → Object
    | factorial : Object → Object
    | pow : Object → Object → Object
    | abs : Object → Object
    | sin : Object → Object
    | arcsin : Object → Object
    | cos : Object → Object
    | tan : Object → Object
    | cot : Object → Object
    | realPart : Object → Object
    | imaginaryPart : Object → Object
    | complexAbs : Object → Object
    | sqrt : Object → Object
    | log : Object → Object → Object
    | union : Object → Object → Object
    | intersect : Object → Object → Object
    | setMinus : Object → Object → Object
    | bigUnion : Object → Object
    | bigIntersect : Object → Object
    | indexUnion : Object → Object → Object → Object
    | indexIntersect : Object → Object → Object → Object
    | powerSet : Object → Object
    | generalCart : Object → Object → Object → Object
    | listSet : List Object → Object
    | setBuilder : Symbol → Object → List Formula → Object
    | fnSet : List (List (Symbol × Object)) → List Formula → Object → Object
    | anonymousFn : List (List (Symbol × Object)) → List Formula → Object → Object → Object
    | cart : List Object → Object
    | cartDim : Object → Object
    | proj : Object → Object → Object
    | tupleDim : Object → Object
    | tuple : List Object → Object
    | finiteSetSize : Object → Object
    | finiteSetMax : Object → Object
    | finiteSetMin : Object → Object
    | fnRange : Object → Object
    | replacement : String → Object → Object
    | sum : Object → Object → Object → Object
    | sumOfFiniteSet : Object → Object → Object
    | product : Object → Object → Object → Object
    | productOfFiniteSet : Object → Object → Object
    | reduce : Object → Object → Object → Object → Object → Object
    | finiteSetReduce : Object → Object → Object → Object → Object
    | range : Object → Object → Object
    | closedRange : Object → Object → Object
    | finiteSeqSet : Object → Object → Object
    | seqSet : Object → Object
    | finiteSeqListObj : List Object → Object
    | objAtIndex : Object → Object → Object
    | standardSet : String → Object
    | matrixSet : Object → Object → Object → Object
    | matrixListObj : List (List Object) → Object
    | matrixAdd : Object → Object → Object
    | matrixSub : Object → Object → Object
    | matrixMul : Object → Object → Object
    | matrixScalarMul : Object → Object → Object
    | matrixPow : Object → Object → Object
    | structObj : String → List Object → Object
    | fieldAccess : Object → String → Object
    | instantiatedTemplateObj : String → List Object → Object
    | oneSideInfinityIntervalObj : IntervalSide → Object → Object
    | intervalObj : IntervalBoundary → Object → Object → Object

  inductive FnHead where
    | identifier : Symbol → FnHead
    | identifierWithMod : QualifiedSymbol → FnHead
    | bound : Symbol → FnHead
    | anonymousFnLiteral : List (List (Symbol × Object)) → List Formula → Object → Object → FnHead
    | finiteSeqListObj : List Object → FnHead
    | objAtIndex : Object → Object → FnHead
    | fieldAccess : Object → String → FnHead
    | instantiatedTemplateObj : String → List Object → FnHead
    | matrixOperator : Object → FnHead

  inductive Formula where
    | truth : Formula
    | falsity : Formula
    | same : Object → Object → Formula
    | inSet : Object → Object → Formula
    | lt : Object → Object → Formula
    | le : Object → Object → Formula
    | not : Formula → Formula
    | and : List Formula → Formula
    | or : List Formula → Formula
    | implies : Formula → Formula → Formula

end

namespace Object

/-! ## Named constructors and carrier symbols -/

def Apply (head : FnHead) (arguments : List Object) : Object :=
  .fnObj head [arguments]

def N : Object := .atom (.identifier {
  id := .reserved .N
  displayName := "N"
})

def Z : Object := .atom (.identifier {
  id := .reserved .Z
  displayName := "Z"
})

def Q : Object := .atom (.identifier {
  id := .reserved .Q
  displayName := "Q"
})

def R : Object := .atom (.identifier {
  id := .reserved .R
  displayName := "R"
})

def C : Object := .atom (.identifier {
  id := .reserved .C
  displayName := "C"
})

def Union (left right : Object) : Object := .union left right
def Intersect (left right : Object) : Object := .intersect left right
def SetMinus (left right : Object) : Object := .setMinus left right
def BigUnion (family : Object) : Object := .bigUnion family
def BigIntersect (family : Object) : Object := .bigIntersect family
def IndexUnion (indexSet ambient family : Object) : Object :=
  .indexUnion indexSet ambient family
def IndexIntersect (indexSet ambient family : Object) : Object :=
  .indexIntersect indexSet ambient family
def PowerSet (set : Object) : Object := .powerSet set
def GeneralCart (indexSet familySet familyFn : Object) : Object :=
  .generalCart indexSet familySet familyFn
def ListSet (elements : List Object) : Object := .listSet elements
def SetBuilder (binding : Symbol) (set : Object) (facts : List Formula) : Object :=
  .setBuilder binding set facts
def FnSet (parameters : List (List (Symbol × Object)))
    (facts : List Formula) (returnSet : Object) : Object :=
  .fnSet parameters facts returnSet
def AnonymousFn (parameters : List (List (Symbol × Object)))
    (facts : List Formula) (returnSet body : Object) : Object :=
  .anonymousFn parameters facts returnSet body
def Cart (factors : List Object) : Object := .cart factors
def Tuple (elements : List Object) : Object := .tuple elements
def FnRange (function : Object) : Object := .fnRange function
def Replacement (propertyName : String) (sourceSet : Object) : Object :=
  .replacement propertyName sourceSet
def Sum (start finish function : Object) : Object := .sum start finish function
def SumOfFiniteSet (set function : Object) : Object := .sumOfFiniteSet set function
def Product (start finish function : Object) : Object := .product start finish function
def ProductOfFiniteSet (set function : Object) : Object := .productOfFiniteSet set function
def Reduce (start finish function operation seed : Object) : Object :=
  .reduce start finish function operation seed
def FiniteSetReduce (set function operation seed : Object) : Object :=
  .finiteSetReduce set function operation seed
def Range (start finish : Object) : Object := .range start finish
def ClosedRange (start finish : Object) : Object := .closedRange start finish
def FiniteSeqSet (set bound : Object) : Object := .finiteSeqSet set bound
def SeqSet (set : Object) : Object := .seqSet set
def FiniteSeqList (elements : List Object) : Object := .finiteSeqListObj elements
def ObjAtIndex (object index : Object) : Object := .objAtIndex object index
def StandardSet (name : String) : Object := .standardSet name
def MatrixSet (set rowLength columnLength : Object) : Object :=
  .matrixSet set rowLength columnLength
def MatrixList (rows : List (List Object)) : Object := .matrixListObj rows
def StructObject (name : String) (parameters : List Object) : Object :=
  .structObj name parameters
def FieldAccess (record : Object) (fieldName : String) : Object :=
  .fieldAccess record fieldName
def TemplateInstance (name : String) (arguments : List Object) : Object :=
  .instantiatedTemplateObj name arguments
def OneSideInfinityInterval (side : IntervalSide) (start : Object) : Object :=
  .oneSideInfinityIntervalObj side start
def Interval (boundary : IntervalBoundary) (start finish : Object) : Object :=
  .intervalObj boundary start finish

@[simp] theorem union_shape (left right : Object) :
    Union left right = .union left right :=
  rfl

@[simp] theorem sum_shape (start finish function : Object) :
    Sum start finish function = .sum start finish function :=
  rfl

/-! ## Structural semantic equality

The object layer only records identity/congruence.  A later semantic layer
decides when an operation has a mathematical interpretation and supplies the
corresponding proof. -/

inductive Same : Object → Object → Prop where
  | refl (object : Object) : Same object object
  | symm {left right : Object} : Same left right → Same right left
  | trans {left middle right : Object} :
      Same left middle → Same middle right → Same left right
  | fnObjCongr {head head' : FnHead} {body body' : List (List Object)} :
      head = head' → body = body' → Same (.fnObj head body) (.fnObj head' body')
  | realComplex (value : ℝ) :
      Same (.literal (.real value)) (.literal (.complex (value : ℂ)))

namespace Same

theorem reflNoObservation (object : Object) : Same object object :=
  .refl object

theorem ofEq {left right : Object} (h : left = right) : Same left right := by
  cases h
  exact .refl _

theorem fnObj (head : FnHead) (body : List (List Object)) :
    Same (.fnObj head body) (.fnObj head body) :=
  .refl _

theorem realComplexLiteral (value : ℝ) :
    Same (.literal (.real value)) (.literal (.complex (value : ℂ))) :=
  .realComplex value

end Same

end Object

end Litex
