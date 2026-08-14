import Mathlib

/-!
# Litex target semantic core

This module is the shared, versioned interpretation boundary used by generated
Litex-to-Lean proofs. `Litex.Object` is the Lean carrier of source-level Litex
objects; it is not an internal universal set. Membership remains an explicit
`Litex.In` proposition, and proof-carrying operations consume the exact
well-definedness evidence retained by the Litex verifier.

The axioms in this file interpret source primitives and representation
bridges. Concrete verifier rules belong in `Litex.BuiltinRules`, where they are
proved as ordinary Lean theorems. Generated files import that module and check
`abiVersion`; they do not repeat this core.

See `lean/SEMANTIC_REFERENCE.md` for the declaration-by-declaration
correspondence with Tao's *Analysis I*, target-only engineering choices,
extensions beyond the book, trust boundaries, and known implementation drift.
-/

namespace Litex

/-- Version of the shared target ABI expected by generated Litex proofs. -/
def abiVersion : Nat := 7

axiom Object : Type

noncomputable section

axiom In : Object → Object → Prop

/-- Source set inclusion remains an ordinary proposition over explicit Litex
membership. It is defined, not axiomatized, so a checked inclusion proof can
be applied directly to a checked element-membership proof. -/
def Subset (left right : Object) : Prop :=
  ∀ x : Object, In x left → In x right

/-- Litex uses the pure-set branch: every source object is set-like. Source
`$is_set` facts can still keep their own `FactId`; the proposition itself is
definitionally true and therefore adds no independent semantic axiom. -/
def IsSet (_ : Object) : Prop := True

theorem everyObjectIsSet (x : Object) : IsSet x := by
  trivial

def IsNonemptySet (s : Object) : Prop :=
  ∃ x : Object, In x s

def IsFiniteSet (s : Object) : Prop :=
  Set.Finite {x : Object | In x s}

axiom embedComplex : ℂ → Object
axiom embedComplex_injective : Function.Injective embedComplex

instance (n : Nat) : OfNat Object n where
  ofNat := embedComplex (n : ℂ)

/-- Source-level strict comparison on real-valued Litex objects. -/
axiom Lt : Object → Object → Prop
/-- Source-level non-strict comparison on real-valued Litex objects. -/
axiom Le : Object → Object → Prop

@[simp] axiom lt_embedReal (a b : ℝ) :
  Lt (embedComplex (a : ℂ)) (embedComplex (b : ℂ)) ↔ a < b
@[simp] axiom le_embedReal (a b : ℝ) :
  Le (embedComplex (a : ℂ)) (embedComplex (b : ℂ)) ↔ a ≤ b

axiom N : Object
axiom Z : Object
axiom Q : Object
axiom R : Object
axiom C : Object
axiom NPos : Object
axiom ZNeg : Object
axiom ZStar : Object
axiom QPos : Object
axiom QNeg : Object
axiom QStar : Object
axiom RPos : Object
axiom RNeg : Object
axiom RStar : Object
axiom CStar : Object

/-- The source constant `pi`, represented by Mathlib's real pi inside the
universal complex embedding. This constructor is total and needs no
well-definedness premise. -/
def pi : Object := embedComplex (Real.pi : ℂ)

/-- Source-level binary set union. Construction is total; sethood and
membership properties remain separate propositions and proofs. -/
axiom union : Object → Object → Object

/-- Source set-builder. The base carrier stays separate from its predicate so
membership can replay the exact base-membership and body proofs. -/
axiom setBuilder (base : Object) (predicate : Object → Prop) : Object

@[simp] axiom inSetBuilder_iff
    {x base : Object} {predicate : Object → Prop} :
  In x (setBuilder base predicate) ↔ In x base ∧ predicate x

/-- One representative indexed aggregate: a tuple family with a positive
dimension of at least two and a value at each source index. -/
axiom IsTuple : Object → Prop
axiom closedRange : Object → Object → Object
axiom tupleDim : Object → Object
axiom atIndex : Object → Object → Object
axiom tupleObject
    (dimension : Object)
    (value : Object → Object) :
    In dimension NPos → Le 2 dimension → Object

axiom tupleObjectIsTuple
    (dimension : Object)
    (value : Object → Object)
    (positive : In dimension NPos)
    (atLeastTwo : Le 2 dimension) :
  IsTuple (tupleObject dimension value positive atLeastTwo)

@[simp] axiom tupleObject_dim
    (dimension : Object)
    (value : Object → Object)
    (positive : In dimension NPos)
    (atLeastTwo : Le 2 dimension) :
  tupleDim (tupleObject dimension value positive atLeastTwo) = dimension

@[simp] axiom tupleObject_at
    (dimension : Object)
    (value : Object → Object)
    (positive : In dimension NPos)
    (atLeastTwo : Le 2 dimension)
    (index : Object) :
  atIndex (tupleObject dimension value positive atLeastTwo) index = value index

theorem isSetR : IsSet R := by
  trivial

axiom inN_iff {x : Object} :
  In x N ↔ ∃ n : ℕ, embedComplex (n : ℂ) = x
axiom inNPos_iff {x : Object} :
  In x NPos ↔ ∃ n : ℕ, 0 < n ∧ embedComplex (n : ℂ) = x
axiom inZ_iff {x : Object} :
  In x Z ↔ ∃ z : ℤ, embedComplex (z : ℂ) = x
axiom inQ_iff {x : Object} :
  In x Q ↔ ∃ q : ℚ, embedComplex (q : ℂ) = x
axiom inR_iff {x : Object} :
  In x R ↔ ∃ r : ℝ, embedComplex (r : ℂ) = x
axiom inC_iff {x : Object} :
  In x C ↔ ∃ z : ℂ, embedComplex z = x
axiom inRPos_iff {x : Object} :
  In x RPos ↔ ∃ r : ℝ, 0 < r ∧ embedComplex (r : ℂ) = x

axiom add (a b : Object) : In a C → In b C → Object
axiom sub (a b : Object) : In a C → In b C → Object
axiom mul (a b : Object) : In a C → In b C → Object
axiom div (a b : Object) : In a C → In b C → b ≠ 0 → Object

@[simp] axiom add_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C) :
  add (embedComplex a) (embedComplex b) ha hb = embedComplex (a + b)
@[simp] axiom sub_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C) :
  sub (embedComplex a) (embedComplex b) ha hb = embedComplex (a - b)
@[simp] axiom mul_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C) :
  mul (embedComplex a) (embedComplex b) ha hb = embedComplex (a * b)
@[simp] axiom div_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C)
    (hb0 : embedComplex b ≠ 0) :
  div (embedComplex a) (embedComplex b) ha hb hb0 = embedComplex (a / b)

/-- Litex's canonical finite-set literal invariant: source entries are
pairwise distinct in their source order. -/
def ListSetWellDefined (xs : List Object) : Prop :=
  xs.Pairwise (· ≠ ·)

axiom listSet (xs : List Object) :
  ListSetWellDefined xs → Object

@[simp] axiom inListSet_iff {x : Object} {xs : List Object}
    {h : ListSetWellDefined xs} :
  In x (listSet xs h) ↔ x ∈ xs

def arg (args : List Object) (index : Nat) : Object :=
  args.getD index 0

structure FnSpec where
  arity : Nat
  requirements : List Object → Prop
  range : List Object → Object

axiom FnSet : FnSpec → Object
axiom Applicable : Object → List Object → Prop
axiom apply :
  (f : Object) →
  (args : List Object) →
  Applicable f args →
  Object

def IsChoiceFunctionFor
    (indexSet _familySet family chooser : Object) : Prop :=
  ∀ (alpha : Object), In alpha indexSet →
    ∀ (chooserApplicable : Applicable chooser [alpha])
      (familyApplicable : Applicable family [alpha]),
      In (apply chooser [alpha] chooserApplicable)
        (apply family [alpha] familyApplicable)

instance : CoeFun Object fun f =>
    (args : List Object) → Applicable f args → Object where
  coe := apply

axiom fnSetApplicable
    {f : Object}
    {spec : FnSpec}
    {args : List Object} :
    In f (FnSet spec) →
    args.length = spec.arity →
    spec.requirements args →
    Applicable f args

axiom fnSetResult
    {f : Object}
    {spec : FnSpec}
    {args : List Object}
    (hf : In f (FnSet spec))
    (hLength : args.length = spec.arity)
    (hRequirements : spec.requirements args) :
    In (f args (fnSetApplicable hf hLength hRequirements)) (spec.range args)

/-- A checked source function object. The constructor consumes the exact
pointwise range proof retained by the Litex verifier. -/
axiom functionObject
    (spec : FnSpec)
    (body : List Object → Object)
    (closed : ∀ args, args.length = spec.arity → spec.requirements args →
      In (body args) (spec.range args)) : Object

axiom functionObjectInFnSet
    (spec : FnSpec)
    (body : List Object → Object)
    (closed : ∀ args, args.length = spec.arity → spec.requirements args →
      In (body args) (spec.range args)) :
  In (functionObject spec body closed) (FnSet spec)

@[simp] axiom functionObject_apply
    (spec : FnSpec)
    (body : List Object → Object)
    (closed : ∀ args, args.length = spec.arity → spec.requirements args →
      In (body args) (spec.range args))
    (args : List Object)
    (applicable : Applicable (functionObject spec body closed) args) :
  apply (functionObject spec body closed) args applicable = body args

end

end Litex
