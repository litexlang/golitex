import Mathlib

namespace Litex

/-- Version of the shared target ABI expected by generated Litex proofs. -/
def abiVersion : Nat := 2

axiom Object : Type

noncomputable section

axiom In : Object → Object → Prop
axiom IsSet : Object → Prop

def IsNonemptySet (s : Object) : Prop :=
  IsSet s ∧ ∃ x : Object, In x s

def IsFiniteSet (s : Object) : Prop :=
  IsSet s ∧ Set.Finite {x : Object | In x s}

axiom embedComplex : ℂ → Object
axiom embedComplex_injective : Function.Injective embedComplex

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

axiom inN_iff {x : Object} :
  In x N ↔ ∃ n : ℕ, embedComplex (n : ℂ) = x
axiom inZ_iff {x : Object} :
  In x Z ↔ ∃ z : ℤ, embedComplex (z : ℂ) = x
axiom inQ_iff {x : Object} :
  In x Q ↔ ∃ q : ℚ, embedComplex (q : ℂ) = x
axiom inR_iff {x : Object} :
  In x R ↔ ∃ r : ℝ, embedComplex (r : ℂ) = x
axiom inC_iff {x : Object} :
  In x C ↔ ∃ z : ℂ, embedComplex z = x

axiom add (a b : Object) : In a C → In b C → Object
axiom sub (a b : Object) : In a C → In b C → Object
axiom mul (a b : Object) : In a C → In b C → Object
axiom div : Object → Object → Object

@[simp] axiom add_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C) :
  add (embedComplex a) (embedComplex b) ha hb = embedComplex (a + b)
@[simp] axiom sub_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C) :
  sub (embedComplex a) (embedComplex b) ha hb = embedComplex (a - b)
@[simp] axiom mul_embedComplex (a b : ℂ)
    (ha : In (embedComplex a) C) (hb : In (embedComplex b) C) :
  mul (embedComplex a) (embedComplex b) ha hb = embedComplex (a * b)
@[simp] axiom div_embedComplex (a b : ℂ) :
  div (embedComplex a) (embedComplex b) = embedComplex (a / b)

instance (n : Nat) : OfNat Object n where
  ofNat := embedComplex (n : ℂ)

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

end

end Litex
