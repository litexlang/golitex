import Mathlib

/-!
# Core2: identity-first Litex universe prototype

This file is deliberately isolated from `Litex.Core`.  It is a semantic
prototype, not a replacement for the active compiler ABI yet.

The central invariant is that every Litex expression has one `Object` identity.
Carrier membership, semantic equality, and native Mathlib observations are
separate relations/views; membership never manufactures a new representative.
-/

namespace Litex.Core2

universe u

/-- One identity space for Litex expressions.

The constructors are syntax/identity handles, not native Lean values with a
single universal payload.  A predicate used by a set-builder is itself an
`Object` term, so it can be retained and replayed rather than captured as an
uninspectable meta-level closure.
-/
inductive Object where
  | variable : Nat → Object
  | symbol : Nat → Object
  | natural : Nat → Object
  | integer : Int → Object
  | rational : ℚ → Object
  | real : ℝ → Object
  | complex : ℂ → Object
  | apply : Object → Object → Object
  | lambda : Object → Object
  | predicateTrue : Object
  | predicateIn : Object → Object
  | predicateSame : Object → Object
  | predicateAnd : Object → Object → Object
  | setBuilder : Object → Object → Object

/-- Litex's function application operation in the unified universe. -/
def Apply (function argument : Object) : Object :=
  .apply function argument

/-- Distinguished carrier objects.  They are objects, not Lean types. -/
def R : Object :=
  .symbol 0

def C : Object :=
  .symbol 1

/-- Heterogeneous semantic equality between Litex objects. -/
inductive Same : Object → Object → Prop where
  | refl (x : Object) : Same x x
  | realComplex (value : ℝ) : Same (.real value) (.complex value)
  | symm {x y : Object} : Same x y → Same y x
  | trans {x y z : Object} : Same x y → Same y z → Same x z
  | applyCongr
      {function function' argument argument' : Object} :
      Same function function' →
      Same argument argument' →
      Same (Apply function argument) (Apply function' argument')
  | setBuilderCongr
      {base base' predicate predicate' : Object} :
      Same base base' →
      Same predicate predicate' →
      Same (.setBuilder base predicate) (.setBuilder base' predicate')

/-!
Membership and predicate satisfaction are mutually inductive.  This gives the
set-builder law a real proof object while keeping its predicate an Object term.
-/
mutual
  /-- `In x carrier` classifies the object `x` without changing its identity. -/
  inductive In : Object → Object → Prop where
    | realValue {x : Object} (value : ℝ) :
        Same x (.real value) → In x R
    | complexValue {x : Object} (value : ℂ) :
        Same x (.complex value) → In x C
    | setBuilder {x base predicate : Object} :
        In x base → Holds predicate x → In x (.setBuilder base predicate)

  /-- Proof that a predicate Object is satisfied by an Object. -/
  inductive Holds : Object → Object → Prop where
    | true (x : Object) : Holds .predicateTrue x
    | inCarrier {x carrier : Object} :
        In x carrier → Holds (.predicateIn carrier) x
    | same {x value : Object} :
        Same x value → Holds (.predicateSame value) x
    | and {x left right : Object} :
        Holds left x → Holds right x → Holds (.predicateAnd left right) x
end

namespace Same

theorem reflNoObservation (x : Object) : Same x x :=
  .refl x

end Same

/-- Canonical native complex observation of an Object.

The fallback value for non-complex syntax is intentionally not a semantic
claim.  All native consumers must first retain the appropriate `In` evidence.
The observer is total so it never depends on which membership proof happened
to be supplied at a call site.
-/
def ComplexValue : Object → ℂ
  | .real value => value
  | .complex value => value
  | _ => 0

/-- The real observation used only for objects admitted to `R`. -/
def RealValue (x : Object) : ℝ :=
  (ComplexValue x).re

theorem same_complexValue {x y : Object} (h : Same x y) :
    ComplexValue x = ComplexValue y := by
  induction h with
  | refl x => rfl
  | realComplex value => rfl
  | symm h ih => exact ih.symm
  | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  | applyCongr hf ha ihf iha => rfl
  | setBuilderCongr hb hp ihb ihp => rfl

theorem same_realValue {x y : Object} (h : Same x y) :
    RealValue x = RealValue y := by
  exact congrArg Complex.re (same_complexValue h)

theorem realValue_same_real
    {x : Object} {value : ℝ}
    (h : Same x (.real value)) :
    RealValue x = value := by
  have observed := same_realValue h
  simpa [RealValue, ComplexValue] using observed

theorem complexValue_same_complex
    {x : Object} {value : ℂ}
    (h : Same x (.complex value)) :
    ComplexValue x = value := by
  simpa [ComplexValue] using same_complexValue h

@[simp] theorem real_complexValue (value : ℝ) :
    ComplexValue (.real value) = (value : ℂ) := by
  rfl

@[simp] theorem complex_complexValue (value : ℂ) :
    ComplexValue (.complex value) = value := by
  rfl

@[simp] theorem real_realValue (value : ℝ) :
    RealValue (.real value) = value := by
  simp [RealValue, ComplexValue]

theorem inR_has_realValue
    {x : Object}
    (h : In x R) :
    ∃ value : ℝ, RealValue x = value := by
  rcases h with ⟨value, sameValue⟩
  exact ⟨value, realValue_same_real sameValue⟩

theorem inC_has_complexValue
    {x : Object}
    (h : In x C) :
    ∃ value : ℂ, ComplexValue x = value := by
  cases h with
  | complexValue value sameValue =>
      exact ⟨value, complexValue_same_complex sameValue⟩

theorem real_in_complex (value : ℝ) :
    In (.real value) C := by
  exact In.complexValue value (Same.realComplex value)

theorem complex_in_complex (value : ℂ) :
    In (.complex value) C := by
  exact In.complexValue value (Same.refl (.complex value))

theorem real_in_real (value : ℝ) :
    In (.real value) R := by
  exact In.realValue value (Same.refl (.real value))

theorem apply_same_self (function argument : Object) :
    Same (Apply function argument) (Apply function argument) := by
  exact Same.applyCongr (Same.refl function) (Same.refl argument)

theorem in_setBuilder_iff
    {x base predicate : Object} :
    In x (.setBuilder base predicate) ↔
      In x base ∧ Holds predicate x := by
  constructor
  · intro h
    cases h with
    | setBuilder hbase hpredicate => exact ⟨hbase, hpredicate⟩
  · rintro ⟨hbase, hpredicate⟩
    exact In.setBuilder hbase hpredicate

/-- Object-level real order.  It is meaningful only with real membership. -/
def ObjLe (left right : Object) : Prop :=
  RealValue left ≤ RealValue right

@[simp] theorem realObjLe_iff (left right : ℝ) :
    ObjLe (.real left) (.real right) ↔ left ≤ right := by
  simp [ObjLe, RealValue, ComplexValue]

/-- Native real values represented by real members of a Litex Object set. -/
def RealMembers (set : Object) : Set ℝ :=
  {value |
    ∃ x : Object,
      In x set ∧ In x R ∧ RealValue x = value}

/-- Object-level least-upper-bound certificate. -/
def RealLeastUpperBound (set candidate : Object) : Prop :=
  In candidate R ∧
    (∀ x : Object, In x set → In x R ∧ ObjLe x candidate) ∧
    (∀ upper : Object,
      In upper R →
        (∀ x : Object, In x set → ObjLe x upper) →
        ObjLe candidate upper)

/-!
The Mathlib bridge uses the same Object `x` throughout the source contract.
No `In.rep`, `Subset.rep`, or representative equality is introduced here.
-/
theorem realLeastUpperBoundExists
    (set upper : Object)
    (setSubsetReal : ∀ x : Object, In x set → In x R)
    (setNonempty : ∃ x : Object, In x set)
    (_upperReal : In upper R)
    (boundsEveryMember :
      ∀ x : Object, In x set → ObjLe x upper) :
    ∃ candidate : Object, RealLeastUpperBound set candidate := by
  let values : Set ℝ := RealMembers set
  have valuesNonempty : values.Nonempty := by
    rcases setNonempty with ⟨x, hx⟩
    have hxReal := setSubsetReal x hx
    exact ⟨RealValue x, ⟨x, hx, hxReal, rfl⟩⟩
  have valuesBounded : BddAbove values := by
    refine ⟨RealValue upper, ?_⟩
    intro value valueInValues
    rcases valueInValues with ⟨x, hx, hxReal, hvalue⟩
    rw [← hvalue]
    exact boundsEveryMember x hx
  let supremum : ℝ := sSup values
  have supremumIsLUB : IsLUB values supremum := by
    exact isLUB_csSup valuesNonempty valuesBounded
  refine ⟨.real supremum, ?_⟩
  refine ⟨real_in_real supremum, ?_, ?_⟩
  · intro x hx
    have hxReal := setSubsetReal x hx
    have valueInValues : RealValue x ∈ values :=
      ⟨x, hx, hxReal, rfl⟩
    have valueLeSupremum := supremumIsLUB.1 valueInValues
    constructor
    · exact hxReal
    · simpa [ObjLe, RealValue, ComplexValue] using valueLeSupremum
  · intro upperObject upperCandidateReal candidateBounds
    have valuesLeCandidate : ∀ value ∈ values, value ≤ RealValue upperObject := by
      intro value valueInValues
      rcases valueInValues with ⟨x, hx, hxReal, hvalue⟩
      rw [← hvalue]
      simpa [ObjLe] using candidateBounds x hx
    have supremumLeCandidate := supremumIsLUB.2 valuesLeCandidate
    simpa [ObjLe, RealValue, ComplexValue] using supremumLeCandidate

/-!
## Tracer theorems

These examples are intentionally small.  They check that alpha-renamed
binders and repeated `Apply` use one Object identity, and that an Object-level
completeness contract can bridge once to Mathlib's `Set ℝ`/`sSup` route.
-/

theorem alphaRenamedFunctionContract
    (function domain codomain : Object) :
    (∀ x : Object, In x domain → In (Apply function x) codomain) ↔
      (∀ y : Object, In y domain → In (Apply function y) codomain) := by
  rfl

theorem repeatedApplyHasOneIdentity
    (function argument : Object) :
    Apply function argument = Apply function argument := by
  rfl

theorem setBuilderTrueMember
    {x base : Object}
    (hx : In x base) :
    In x (.setBuilder base .predicateTrue) := by
  exact In.setBuilder hx (Holds.true x)

def singletonRealSet (value : ℝ) : Object :=
  .setBuilder R (.predicateSame (.real value))

theorem singletonRealSet_subsetReal (value : ℝ) :
    ∀ x : Object, In x (singletonRealSet value) → In x R := by
  intro x hx
  exact (in_setBuilder_iff.mp hx).1

theorem singletonRealSet_nonempty (value : ℝ) :
    ∃ x : Object, In x (singletonRealSet value) := by
  refine ⟨.real value, ?_⟩
  apply In.setBuilder (real_in_real value)
  exact Holds.same (Same.refl (.real value))

theorem singletonRealSet_bounded (value : ℝ) :
    ∀ x : Object, In x (singletonRealSet value) →
      ObjLe x (.real value) := by
  intro x hx
  rcases (in_setBuilder_iff.mp hx).2 with hpredicate
  cases hpredicate with
  | same h =>
      have hvalue := realValue_same_real h
      change RealValue x ≤ value
      exact hvalue.le

theorem singletonRealSet_has_lub (value : ℝ) :
    ∃ candidate : Object,
      RealLeastUpperBound (singletonRealSet value) candidate := by
  exact realLeastUpperBoundExists
    (singletonRealSet value)
    (.real value)
    (singletonRealSet_subsetReal value)
    (singletonRealSet_nonempty value)
    (real_in_real value)
    (singletonRealSet_bounded value)

end Litex.Core2
