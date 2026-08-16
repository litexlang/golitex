import Mathlib

/-!
# Litex target semantic core

This module is the shared, versioned interpretation boundary used by generated
Litex-to-Lean proofs. `Litex.Object` is the Lean carrier of source-level Litex
objects; it is not an internal universal set. Membership remains an explicit
`Litex.In` proposition. Object denotation is proof-free; the exact
well-definedness evidence retained by the Litex verifier is replayed as
propositions in the corresponding Lean proof environment.

The axioms in this file interpret source primitives and representation
bridges. Concrete verifier rules belong in `Litex.Rules`, where they are
proved as ordinary Lean theorems. Generated files import that module; they do
not repeat this core or add an ABI-version declaration.

See `lean/SEMANTIC_REFERENCE.md` for the declaration-by-declaration
correspondence with Tao's *Analysis I*, target-only engineering choices,
extensions beyond the book, trust boundaries, and known implementation drift.
-/

namespace Litex

/-- Version of the shared target ABI expected by generated Litex proofs. -/
def abiVersion : Nat := 10

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

/-- The source constant `i`, represented by Mathlib's imaginary unit. -/
def i : Object := embedComplex Complex.I

/-- The source constant `e`, represented by the real exponential at one. -/
def e : Object := embedComplex (Real.exp 1 : ℂ)

/-- The source constant `pi`, represented by Mathlib's real pi inside the
universal complex embedding. These constants are total and need no
well-definedness premise. -/
def pi : Object := embedComplex (Real.pi : ℂ)

/-- Source-level binary set union. Construction is total; sethood and
membership properties remain separate propositions and proofs. -/
axiom union : Object → Object → Object

/-- The ordinary set constructors use Mathlib's familiar pointwise set
semantics at the `Litex.In` boundary. Their object terms remain total and
proof-free. -/
axiom intersect : Object → Object → Object
axiom setMinus : Object → Object → Object
axiom bigUnion : Object → Object
axiom bigIntersect : Object → Object
axiom powerSet : Object → Object

@[simp] axiom inUnion_iff {x left right : Object} :
  In x (union left right) ↔ In x left ∨ In x right

@[simp] axiom inIntersect_iff {x left right : Object} :
  In x (intersect left right) ↔ In x left ∧ In x right

@[simp] axiom inSetMinus_iff {x left right : Object} :
  In x (setMinus left right) ↔ In x left ∧ ¬ In x right

@[simp] axiom inBigUnion_iff {x family : Object} :
  In x (bigUnion family) ↔ ∃ member : Object, In member family ∧ In x member

@[simp] axiom inBigIntersect_iff {x family : Object} :
  In x (bigIntersect family) ↔ ∀ member : Object, In member family → In x member

@[simp] axiom inPowerSet_iff {x base : Object} :
  In x (powerSet base) ↔ Subset x base

/-- Source set-builder. The base carrier stays separate from its predicate so
membership can replay the exact base-membership and body proofs. -/
axiom setBuilder (base : Object) (predicate : Object → Prop) : Object

@[simp] axiom inSetBuilder_iff
    {x base : Object} {predicate : Object → Prop} :
  In x (setBuilder base predicate) ↔ In x base ∧ predicate x

/-- One representative indexed aggregate: a tuple family with a positive
dimension of at least two and a value at each source index. -/
axiom IsTuple : Object → Prop
axiom range : Object → Object → Object
axiom closedRange : Object → Object → Object
axiom tupleDim : Object → Object
axiom atIndex : Object → Object → Object
axiom tupleLiteral : List Object → Object
axiom sequenceLiteral : List Object → Object
axiom tupleObject
    (dimension : Object)
    (value : Object → Object) : Object

axiom tupleObjectIsTuple
    (dimension : Object)
    (value : Object → Object) :
  IsTuple (tupleObject dimension value)

@[simp] axiom tupleLiteralIsTuple (xs : List Object) :
  IsTuple (tupleLiteral xs)

@[simp] axiom tupleObject_dim
    (dimension : Object)
    (value : Object → Object) :
  tupleDim (tupleObject dimension value) = dimension

@[simp] axiom tupleObject_at
    (dimension : Object)
    (value : Object → Object)
    (index : Object) :
  atIndex (tupleObject dimension value) index = value index

@[simp] axiom tupleLiteral_dim (xs : List Object) :
  tupleDim (tupleLiteral xs) = embedComplex (xs.length : ℂ)

@[simp] axiom sequenceLiteral_dim (xs : List Object) :
  tupleDim (sequenceLiteral xs) = embedComplex (xs.length : ℂ)

@[simp] axiom inRange_iff {x start finish : Object} :
  In x (range start finish) ↔ In x Z ∧ Le start x ∧ Lt x finish

@[simp] axiom inClosedRange_iff {x start finish : Object} :
  In x (closedRange start finish) ↔ In x Z ∧ Le start x ∧ Le x finish

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

/-! Arithmetic object denotation is total at the target representation layer.
The source verifier still proves complex membership and divisor nonzeroness
before accepting these objects; those facts are replayed separately. -/
axiom add : Object → Object → Object
axiom sub : Object → Object → Object
axiom mul : Object → Object → Object
axiom div : Object → Object → Object

@[simp] axiom add_embedComplex (a b : ℂ) :
  add (embedComplex a) (embedComplex b) = embedComplex (a + b)
@[simp] axiom sub_embedComplex (a b : ℂ) :
  sub (embedComplex a) (embedComplex b) = embedComplex (a - b)
@[simp] axiom mul_embedComplex (a b : ℂ) :
  mul (embedComplex a) (embedComplex b) = embedComplex (a * b)
@[simp] axiom div_embedComplex (a b : ℂ) :
  div (embedComplex a) (embedComplex b) = embedComplex (a / b)

/-- Litex's canonical finite-set literal invariant: source entries are
pairwise distinct in their source order. -/
def ListSetWellDefined (xs : List Object) : Prop :=
  xs.Pairwise (· ≠ ·)

axiom listSet : List Object → Object

@[simp] axiom inListSet_iff {x : Object} {xs : List Object} :
  In x (listSet xs) ↔ x ∈ xs

@[reducible] def arg (args : List Object) (index : Nat) : Object :=
  args.getD index 0

structure FnSpec where
  arity : Nat
  requirements : List Object → Prop
  /-- The result carrier may itself require the exact ordered evidence that
  made the source application well-defined. -/
  range :
    (args : List Object) →
    args.length = arity →
    requirements args →
    Object

axiom FnSet : FnSpec → Object

@[reducible] def fnSpaceRequirementsFrom
    (args : List Object) (index : Nat) : List Object → Prop
  | [] => True
  | input :: inputs =>
      ∃ _ : In (arg args index) input,
        fnSpaceRequirementsFrom args (index + 1) inputs

@[reducible] def fnSpaceSpec (inputs : List Object) (output : Object) : FnSpec :=
  { arity := inputs.length
    requirements := fun args => fnSpaceRequirementsFrom args 0 inputs
    range := fun _ _ _ => output }

/-- The object of functions with one exact application layer, fixed input
sets, no extra domain conditions, and a fixed output set. -/
@[reducible] def fnSpace (inputs : List Object) (output : Object) : Object :=
  FnSet (fnSpaceSpec inputs output)

@[reducible] def fnSpace1 (input output : Object) : Object :=
  fnSpace [input] output

@[reducible] def fnSpace2 (input₀ input₁ output : Object) : Object :=
  fnSpace [input₀, input₁] output

@[reducible] def fnSpace3 (input₀ input₁ input₂ output : Object) : Object :=
  fnSpace [input₀, input₁, input₂] output

@[reducible] def fnSpace4 (input₀ input₁ input₂ input₃ output : Object) : Object :=
  fnSpace [input₀, input₁, input₂, input₃] output

@[reducible] def fnSpace5 (input₀ input₁ input₂ input₃ input₄ output : Object) : Object :=
  fnSpace [input₀, input₁, input₂, input₃, input₄] output

/-- Sequence carriers are ordinary function spaces. A finite sequence uses
the exact closed positive-index interval retained by the source verifier. -/
@[reducible] def finiteSequenceSet (values length : Object) : Object :=
  fnSpace1 (closedRange 1 length) values

@[reducible] def sequenceSet (values : Object) : Object :=
  fnSpace1 NPos values

/-- General Cartesian products and finite-set folds are proof-free object
denotations. Their sethood, callable contracts, range checks, operation laws,
and seed checks are separate verifier-owned propositions. -/
axiom generalCart : Object → Object → Object → Object
axiom finiteSetSum : Object → Object → Object
axiom finiteSetProduct : Object → Object → Object
axiom finiteSetReduce : Object → Object → Object → Object → Object

/-- Indexed scalar folds are the corresponding finite-set operations over the
closed integer interval used by the Litex verifier. Source well-definedness can
still reject an empty `sum` or `product`; that certificate is not object data. -/
@[reducible] def sum (start finish function : Object) : Object :=
  finiteSetSum (closedRange start finish) function

@[reducible] def product (start finish function : Object) : Object :=
  finiteSetProduct (closedRange start finish) function

@[reducible] def reduce
    (start finish function operation seed : Object) : Object :=
  finiteSetReduce (closedRange start finish) function operation seed

axiom Applicable : Object → List Object → Prop
/-! Object denotation is independent of its well-definedness proof.  The
verifier-owned `Applicable` evidence is replayed in the Lean proof environment
that corresponds to the Litex runtime environment which produced it. -/
axiom apply : Object → List Object → Object

def IsChoiceFunctionFor
    (indexSet _familySet family chooser : Object) : Prop :=
  ∀ (alpha : Object), In alpha indexSet →
    ∀ (_chooserApplicable : Applicable chooser [alpha])
      (_familyApplicable : Applicable family [alpha]),
      In (apply chooser [alpha]) (apply family [alpha])

@[simp] axiom inGeneralCart_iff
    {chooser indexSet familySet family : Object} :
  In chooser (generalCart indexSet familySet family) ↔
    In chooser (fnSpace1 indexSet (bigUnion familySet)) ∧
      IsChoiceFunctionFor indexSet familySet family chooser

instance : CoeFun Object fun _ =>
    (args : List Object) → Object where
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
    In (f args)
      (spec.range args hLength hRequirements)

/-- Readable applicability bridge for an ordinary, nondependent function
space. Generated proofs use this instead of exposing `FnSpec`. -/
theorem fnSpaceApplicable
    {f inputs output args}
    (hf : In f (fnSpace inputs output))
    (hLength : args.length = inputs.length)
    (hRequirements : fnSpaceRequirementsFrom args 0 inputs) :
    Applicable f args := by
  exact fnSetApplicable (args := args) hf hLength hRequirements

/-- Readable result-membership bridge for an ordinary, nondependent function
space. -/
theorem fnSpaceResult
    {f inputs output args}
    (hf : In f (fnSpace inputs output))
    (hLength : args.length = inputs.length)
    (hRequirements : fnSpaceRequirementsFrom args 0 inputs) :
    In (f args) output := by
  simpa only [fnSpace, fnSpaceSpec] using
    (fnSetResult (args := args) hf hLength hRequirements)

/-- A source function object. Its denotation depends on the specification and
body, not on which pointwise range proof the verifier selected. -/
axiom functionObject
    (spec : FnSpec)
    (body :
      (args : List Object) →
      args.length = spec.arity →
      spec.requirements args → Object) : Object

/-- The verifier-owned pointwise closure proof establishes function-space
membership without becoming an argument of the function object itself. -/
axiom functionObjectInFnSet
    (spec : FnSpec)
    (body :
      (args : List Object) →
      args.length = spec.arity →
      spec.requirements args → Object)
    (closed : ∀ args hLength hRequirements,
      In (body args hLength hRequirements)
        (spec.range args hLength hRequirements)) :
  In (functionObject spec body) (FnSet spec)

/-- Applicability of a checked function object retains the source arity
certificate. These projections let definition replay consume the same proof
telescope even when the caller cites an already named `Applicable` fact. -/
axiom functionObjectApplicableLength
    (spec : FnSpec)
    (body :
      (args : List Object) →
      args.length = spec.arity →
      spec.requirements args → Object)
    (args : List Object)
    (_applicable : Applicable (functionObject spec body) args) :
  args.length = spec.arity

/-- Applicability of a checked function object retains the exact ordered
requirements certificate used by its dependent body and range. -/
axiom functionObjectApplicableRequirements
    (spec : FnSpec)
    (body :
      (args : List Object) →
      args.length = spec.arity →
      spec.requirements args → Object)
    (args : List Object)
    (_applicable : Applicable (functionObject spec body) args) :
  spec.requirements args

@[simp] axiom functionObject_apply
    (spec : FnSpec)
    (body :
      (args : List Object) →
      args.length = spec.arity →
      spec.requirements args → Object)
    (args : List Object)
    (applicable : Applicable (functionObject spec body) args) :
  apply (functionObject spec body) args =
    body args
      (functionObjectApplicableLength spec body args applicable)
      (functionObjectApplicableRequirements spec body args applicable)

end

end Litex
