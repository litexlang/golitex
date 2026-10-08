import Mathlib.Data.Complex.Basic
import Mathlib.SetTheory.ZFC.Ordinal

/-! Litex object semantics, certified constructors, and native numeric bridges.

`Obj` always includes its well-definedness proof. Host representations remain
generic, and source equality and membership use their fixed denotations.
`NumericModel.model` is an explicit candidate for the numeric slice; it is not
a default model or a completed model of all Litex objects and rules.
-/

universe u v w

namespace Litex

inductive StandardSetValue where
  | natural
  | integer
  | rational
  | real
  | complex
  deriving DecidableEq, Repr

/-- An explicit contract for a future mathematical model, not an instantiated
model or a collection of global axioms. The object API is conditional on it. -/
structure Semantics where
  Value : Type u
  mem : Value → Value → Prop
  isSet : Value → Prop
  number : ℂ → Value
  standard : StandardSetValue → Value
  addValue : Value → Value → Value
  divValue : Value → Value → Value
  number_injective : Function.Injective number
  complex_members : ∀ x, mem x (standard .complex) ↔ ∃ z, x = number z
  real_members : ∀ x, mem x (standard .real) ↔ ∃ r : ℝ, x = number (r : ℂ)
  real_subset_complex : ∀ x, mem x (standard .real) → mem x (standard .complex)
  member_isSet : ∀ {x A}, mem x A → isSet x
  standard_isSet : ∀ A, isSet (standard A)
  add_numbers : ∀ a b, addValue (number a) (number b) = number (a + b)
  div_numbers : ∀ a b, b ≠ 0 → divValue (number a) (number b) = number (a / b)
  add_closed : ∀ {a b},
    mem a (standard .complex) → mem b (standard .complex) →
    mem (addValue a b) (standard .complex)
  div_closed : ∀ {a b},
    mem a (standard .complex) → mem b (standard .complex) →
    b ≠ number 0 → mem (divValue a b) (standard .complex)

end Litex

namespace Litex

/-- Fixed meaning and admissibility for one host representation. There is no
fallback instance certifying arbitrary Lean types. -/
class Representation (M : Semantics.{u}) (α : Type v) where
  wd : α → Prop
  denote : α → M.Value
  wd_isSet : ∀ {a}, wd a → M.isSet (denote a)

def WD {M : Semantics.{u}} {α : Type v} [Representation M α] (a : α) : Prop :=
  Representation.wd (M := M) a

structure Obj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  val : α
  wd : WD (M := M) val

def denote {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : M.Value :=
  Representation.denote a.val

def Same {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  denote a = denote b

def In {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (A : Obj (M := M) β) : Prop :=
  M.mem (denote a) (denote A)

def IsSet {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : Prop :=
  M.isSet (denote a)

def isSet {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : IsSet a :=
  Representation.wd_isSet a.wd

def sameRefl {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : Same a a :=
  rfl

instance complexRepresentation (M : Semantics.{u}) : Representation M ℂ where
  wd _ := True
  denote := M.number
  wd_isSet {a} _ := M.member_isSet ((M.complex_members (M.number a)).mpr ⟨a, rfl⟩)

instance standardRepresentation (M : Semantics.{u}) :
    Representation M StandardSetValue where
  wd _ := True
  denote := M.standard
  wd_isSet {a} _ := M.standard_isSet a

def number {M : Semantics.{u}} (z : ℂ) : Obj (M := M) ℂ :=
  ⟨z, True.intro⟩

def standardSet {M : Semantics.{u}} (A : StandardSetValue) :
    Obj (M := M) StandardSetValue :=
  ⟨A, True.intro⟩

def N {M : Semantics.{u}} : Obj (M := M) StandardSetValue := standardSet .natural
def Z {M : Semantics.{u}} : Obj (M := M) StandardSetValue := standardSet .integer
def Q {M : Semantics.{u}} : Obj (M := M) StandardSetValue := standardSet .rational
def R {M : Semantics.{u}} : Obj (M := M) StandardSetValue := standardSet .real
def C {M : Semantics.{u}} : Obj (M := M) StandardSetValue := standardSet .complex

def numberInC {M : Semantics.{u}} (z : ℂ) : In (number (M := M) z) C :=
  (M.complex_members (M.number z)).mpr ⟨z, rfl⟩

def realToComplex {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In a C :=
  M.real_subset_complex (denote a) haR

end Litex

namespace Litex

structure AddObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure DivObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance addRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] :
    Representation M (AddObj (M := M) α β) where
  wd a := In a.left C ∧ In a.right C
  denote a := M.addValue (denote a.left) (denote a.right)
  wd_isSet h := M.member_isSet (M.add_closed h.1 h.2)

instance divRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] :
    Representation M (DivObj (M := M) α β) where
  wd a := In a.left C ∧ In a.right C ∧ ¬ Same a.right (number 0)
  denote a := M.divValue (denote a.left) (denote a.right)
  wd_isSet h := M.member_isSet
    (M.div_closed h.1 h.2.1 h.2.2)

def add {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : Obj (M := M) (AddObj (M := M) α β) :=
  ⟨⟨a, b⟩, ⟨haC, hbC⟩⟩

def div {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (hb0 : ¬ Same b (number 0)) :
    Obj (M := M) (DivObj (M := M) α β) :=
  ⟨⟨a, b⟩, ⟨haC, hbC, hb0⟩⟩

def addInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : In (add a b haC hbC) C :=
  M.add_closed haC hbC

def divInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (hb0 : ¬ Same b (number 0)) :
    In (div a b haC hbC hb0) C :=
  M.div_closed haC hbC hb0

end Litex

namespace Litex

/-- A proved arithmetic law; this is not yet a replay of a Rust verifier result. -/
theorem addZero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    Same (add a (number 0) haC (numberInC 0)) a := by
  obtain ⟨z, hz⟩ := (M.complex_members (denote a)).mp haC
  change M.addValue (denote a) (M.number 0) = denote a
  rw [hz, M.add_numbers, add_zero]

end Litex

namespace Litex.NativeBridge

variable {M : Semantics.{u}}

def numberInR (r : ℝ) : In (number (M := M) (r : ℂ)) R :=
  (M.real_members (M.number (r : ℂ))).mpr ⟨r, rfl⟩

theorem complexEq {z w : ℂ}
    (h : Same (number (M := M) z) (number w)) : z = w :=
  M.number_injective h

def numberNonzero (z : ℂ) (hz : z ≠ 0) :
    ¬ Same (number (M := M) z) (number 0) :=
  fun h => hz (complexEq h)

theorem addSame_iff (x y z : ℂ) :
    Same (add (number (M := M) x) (number y) (numberInC x) (numberInC y))
      (number z) ↔ x + y = z := by
  change M.addValue (M.number x) (M.number y) = M.number z ↔ x + y = z
  rw [M.add_numbers]
  exact M.number_injective.eq_iff

theorem divSame_iff (x y z : ℂ) (hy : y ≠ 0) :
    Same (div (number (M := M) x) (number y)
      (numberInC x) (numberInC y) (numberNonzero y hy))
      (number z) ↔ x / y = z := by
  change M.divValue (M.number x) (M.number y) = M.number z ↔ x / y = z
  rw [M.div_numbers x y hy]
  exact M.number_injective.eq_iff

noncomputable def asComplex {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) : ℂ :=
  Classical.choose ((M.complex_members (denote a)).mp haC)

theorem asComplex_spec {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    denote a = M.number (asComplex a haC) :=
  Classical.choose_spec ((M.complex_members (denote a)).mp haC)

theorem asComplex_proofIndependent {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h₁ h₂ : In a C) :
    asComplex a h₁ = asComplex a h₂ :=
  M.number_injective ((asComplex_spec a h₁).symm.trans (asComplex_spec a h₂))

theorem same_iff_asComplex {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C) :
    Same a b ↔ asComplex a haC = asComplex b hbC := by
  change denote a = denote b ↔ _
  rw [asComplex_spec a haC, asComplex_spec b hbC]
  exact M.number_injective.eq_iff

end Litex.NativeBridge

namespace Litex.NumericModel

/-- An example-only encoding through a chosen well-order, not a selected
production representation of Litex numbers. -/
noncomputable def codeComplex (z : ℂ) : ZFSet.{0} :=
  Ordinal.toZFSet (Ordinal.typein (@WellOrderingRel ℂ) z)

theorem codeComplex_injective : Function.Injective codeComplex := by
  intro x y h
  exact Ordinal.typein_injective (@WellOrderingRel ℂ)
    (Ordinal.toZFSet_injective h)

/-- Decode an encoded complex value. The zero branch merely totalizes this
example model outside C; the public arithmetic constructors require C-membership
and never authorize that branch as the meaning of an arbitrary object. -/
noncomputable def decodeComplex (x : ZFSet.{0}) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, codeComplex z = x then Classical.choose h else 0

@[simp] theorem decodeComplex_codeComplex (z : ℂ) :
    decodeComplex (codeComplex z) = z := by
  classical
  have h : ∃ w : ℂ, codeComplex w = codeComplex z := ⟨z, rfl⟩
  unfold decodeComplex
  rw [dif_pos h]
  exact codeComplex_injective (Classical.choose_spec h)

/-- All five standard sets are actual ZF sets of the corresponding embedded
native numbers. No standard-set tag stands for the whole semantic universe. -/
noncomputable def standardSet : StandardSetValue → ZFSet.{0}
  | .natural => ZFSet.range (fun n : ℕ => codeComplex (n : ℂ))
  | .integer => ZFSet.range (fun n : ℤ => codeComplex (n : ℂ))
  | .rational => ZFSet.range (fun q : ℚ => codeComplex (q : ℂ))
  | .real => ZFSet.range (fun r : ℝ => codeComplex (r : ℂ))
  | .complex => ZFSet.range codeComplex

theorem complex_members (x : ZFSet.{0}) :
    x ∈ standardSet .complex ↔ ∃ z : ℂ, x = codeComplex z := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem real_members (x : ZFSet.{0}) :
    x ∈ standardSet .real ↔ ∃ r : ℝ, x = codeComplex (r : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, hr.symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, hr.symm⟩

theorem real_subset_complex (x : ZFSet.{0})
    (hx : x ∈ standardSet .real) : x ∈ standardSet .complex := by
  obtain ⟨r, rfl⟩ := (real_members x).mp hx
  exact (complex_members (codeComplex (r : ℂ))).mpr ⟨(r : ℂ), rfl⟩

noncomputable def addValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a + decodeComplex b)

noncomputable def divValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a / decodeComplex b)

theorem add_numbers (a b : ℂ) :
    addValue (codeComplex a) (codeComplex b) = codeComplex (a + b) := by
  simp only [addValue, decodeComplex_codeComplex]

theorem div_numbers (a b : ℂ) (_hb : b ≠ 0) :
    divValue (codeComplex a) (codeComplex b) = codeComplex (a / b) := by
  simp only [divValue, decodeComplex_codeComplex]

theorem add_closed {a b : ZFSet.{0}}
    (ha : a ∈ standardSet .complex) (hb : b ∈ standardSet .complex) :
    addValue a b ∈ standardSet .complex := by
  obtain ⟨x, rfl⟩ := (complex_members a).mp ha
  obtain ⟨y, rfl⟩ := (complex_members b).mp hb
  exact (complex_members _).mpr ⟨x + y, add_numbers x y⟩

theorem div_closed {a b : ZFSet.{0}}
    (ha : a ∈ standardSet .complex) (hb : b ∈ standardSet .complex)
    (hb0 : b ≠ codeComplex 0) : divValue a b ∈ standardSet .complex := by
  obtain ⟨x, rfl⟩ := (complex_members a).mp ha
  obtain ⟨y, rfl⟩ := (complex_members b).mp hb
  have hy0 : y ≠ 0 := fun h => hb0 (congrArg codeComplex h)
  exact (complex_members _).mpr ⟨x / y, div_numbers x y hy0⟩

/-- A concrete candidate for the numeric object interface; this does not
instantiate the remaining Litex set and function semantics. Every Value is
already a genuine ZF set, so its sethood predicate is True. Membership is
actual ZF membership and equality is faithful
to the injective encoding; neither proposition is trivialized. Arithmetic is
only source-valid under the separate WD/domain proofs required by Litex.Obj.
This witness installs no default model or Representation for arbitrary types. -/
noncomputable def model : Semantics.{1} where
  Value := ZFSet.{0}
  mem := fun x A => x ∈ A
  isSet := fun _ => True
  number := codeComplex
  standard := standardSet
  addValue := addValue
  divValue := divValue
  number_injective := codeComplex_injective
  complex_members := complex_members
  real_members := real_members
  real_subset_complex := real_subset_complex
  member_isSet := fun _ => True.intro
  standard_isSet := fun _ => True.intro
  add_numbers := add_numbers
  div_numbers := div_numbers
  add_closed := add_closed
  div_closed := div_closed

end Litex.NumericModel
