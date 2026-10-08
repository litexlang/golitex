import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.SetTheory.ZFC.Ordinal

/-! Litex object semantics, certified constructors, and native numeric bridges.

`Obj` always includes its well-definedness proof. Host representations remain
generic, and source equality and membership use their fixed denotations.
`NumericModel.model` is an explicit candidate for the numeric slice; it is not
a default model or a completed model of all Litex objects and rules.
-/

universe u v w x

namespace Litex

open Lean Elab Tactic Lean.Parser.Tactic in
/-- Check only the already selected rational-normalization adapter. An explicit
discharger supplies the source's certified denominator evidence. The fixed
denominator step may close the goal itself; otherwise its remaining polynomial
equality is checked by `ring`. No target shape or theorem search selects between
alternative proof routes. -/
elab (name := normalizeRational) "litex_normalize_rational" d:discharger : tactic => do
  evalTactic (← `(tactic| field_simp $d))
  if !(← getGoals).isEmpty then
    evalTactic (← `(tactic| ring))

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
  subValue : Value → Value → Value
  mulValue : Value → Value → Value
  negValue : Value → Value
  divValue : Value → Value → Value
  powValue : Value → Value → Value
  number_injective : Function.Injective number
  complex_members : ∀ x, mem x (standard .complex) ↔ ∃ z, x = number z
  natural_members : ∀ x, mem x (standard .natural) ↔ ∃ n : ℕ, x = number (n : ℂ)
  integer_members : ∀ x, mem x (standard .integer) ↔ ∃ z : ℤ, x = number (z : ℂ)
  rational_members : ∀ x, mem x (standard .rational) ↔ ∃ q : ℚ, x = number (q : ℂ)
  real_members : ∀ x, mem x (standard .real) ↔ ∃ r : ℝ, x = number (r : ℂ)
  real_subset_complex : ∀ x, mem x (standard .real) → mem x (standard .complex)
  member_isSet : ∀ {x A}, mem x A → isSet x
  standard_isSet : ∀ A, isSet (standard A)
  add_numbers : ∀ a b, addValue (number a) (number b) = number (a + b)
  sub_numbers : ∀ a b, subValue (number a) (number b) = number (a - b)
  mul_numbers : ∀ a b, mulValue (number a) (number b) = number (a * b)
  neg_numbers : ∀ a, negValue (number a) = number (-a)
  div_numbers : ∀ a b, b ≠ 0 → divValue (number a) (number b) = number (a / b)
  pow_numbers_nat : ∀ a (n : ℕ), powValue (number a) (number (n : ℂ)) = number (a ^ n)
  pow_numbers_int : ∀ a (z : ℤ), a ≠ 0 →
    powValue (number a) (number (z : ℂ)) = number (a ^ z)
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

/-- Source nonemptiness is existence in the semantic universe. It does not
choose a host representation or turn a fresh declaration into a number. -/
def IsNonempty {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop :=
  ∃ a : M.Value, M.mem a (denote A)

/-- Owned real comparisons use faithful real denotation witnesses. Membership
remains an ordinary fact, and a generic object's carrier does not change. In
particular these predicates do not install an order on arbitrary complex values. -/
def Le {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  ∃ r s : ℝ, denote a = M.number (r : ℂ) ∧
    denote b = M.number (s : ℂ) ∧ r ≤ s

def Lt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  ∃ r s : ℝ, denote a = M.number (r : ℂ) ∧
    denote b = M.number (s : ℂ) ∧ r < s

def isSet {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : IsSet a :=
  Representation.wd_isSet a.wd

def sameRefl {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : Same a a :=
  rfl

/-- Predicate transport uses denotation equality across host representations. -/
theorem inOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (A : Obj (M := M) γ) (B : Obj (M := M) δ)
    (hab : Same a b) (hAB : Same A B) (haA : In a A) : In b B :=
  Eq.mp (congrArg₂ M.mem hab hAB) haA

theorem isSetOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (hab : Same a b) (ha : IsSet a) : IsSet b :=
  Eq.mp (congrArg M.isSet hab) ha

theorem notSameOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (hab : Same a b) (hcd : Same c d) (hac : ¬ Same a c) : ¬ Same b d :=
  fun hbd => hac (hab.trans (hbd.trans hcd.symm))

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

def naturalToComplex {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) : In a C := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp haN
  exact (M.complex_members (denote a)).mpr ⟨(n : ℂ), hn⟩

def integerToComplex {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) : In a C := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  exact (M.complex_members (denote a)).mpr ⟨(z : ℂ), hz⟩

def naturalToInteger {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) : In a Z := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp haN
  exact (M.integer_members (denote a)).mpr ⟨(n : ℤ), by simpa only [Int.cast_natCast] using hn⟩

def naturalToReal {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) : In a R := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp haN
  exact (M.real_members (denote a)).mpr ⟨(n : ℝ), by simpa only [Complex.ofReal_natCast] using hn⟩

def integerToReal {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) : In a R := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  exact (M.real_members (denote a)).mpr ⟨(z : ℝ), by simpa only [Complex.ofReal_intCast] using hz⟩

def naturalToRational {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) : In a Q := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp haN
  exact (M.rational_members (denote a)).mpr ⟨(n : ℚ), by
    simpa only [Rat.cast_natCast] using hn⟩

def integerToRational {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) : In a Q := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  exact (M.rational_members (denote a)).mpr ⟨(z : ℚ), by
    simpa only [Rat.cast_intCast] using hz⟩

def rationalToReal {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haQ : In a Q) : In a R := by
  obtain ⟨q, hq⟩ := (M.rational_members (denote a)).mp haQ
  exact (M.real_members (denote a)).mpr ⟨(q : ℝ), by
    simpa only [Complex.ofReal_ratCast] using hq⟩

def rationalToComplex {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haQ : In a Q) : In a C :=
  realToComplex a (rationalToReal a haQ)

theorem standardNonempty {M : Semantics.{u}} (A : StandardSetValue) :
    IsNonempty (standardSet (M := M) A) := by
  cases A with
  | natural => exact ⟨M.number (0 : ℂ), (M.natural_members _).mpr ⟨0, by simp⟩⟩
  | integer => exact ⟨M.number (0 : ℂ), (M.integer_members _).mpr ⟨0, by simp⟩⟩
  | rational => exact ⟨M.number (0 : ℂ), (M.rational_members _).mpr ⟨0, by simp⟩⟩
  | real => exact ⟨M.number (0 : ℂ), (M.real_members _).mpr ⟨0, by simp⟩⟩
  | complex => exact ⟨M.number (0 : ℂ), (M.complex_members _).mpr ⟨0, rfl⟩⟩

end Litex

namespace Litex.Semantics

theorem sub_closed {M : Semantics.{u}} {a b : M.Value}
    (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex)) :
    M.mem (M.subValue a b) (M.standard .complex) := by
  obtain ⟨x, rfl⟩ := (M.complex_members a).mp ha
  obtain ⟨y, rfl⟩ := (M.complex_members b).mp hb
  exact (M.complex_members _).mpr ⟨x - y, M.sub_numbers x y⟩

theorem mul_closed {M : Semantics.{u}} {a b : M.Value}
    (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex)) :
    M.mem (M.mulValue a b) (M.standard .complex) := by
  obtain ⟨x, rfl⟩ := (M.complex_members a).mp ha
  obtain ⟨y, rfl⟩ := (M.complex_members b).mp hb
  exact (M.complex_members _).mpr ⟨x * y, M.mul_numbers x y⟩

theorem neg_closed {M : Semantics.{u}} {a : M.Value}
    (ha : M.mem a (M.standard .complex)) :
    M.mem (M.negValue a) (M.standard .complex) := by
  obtain ⟨x, rfl⟩ := (M.complex_members a).mp ha
  exact (M.complex_members _).mpr ⟨-x, M.neg_numbers x⟩

end Litex.Semantics

namespace Litex

structure AddObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure DivObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure SubObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure MulObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure NegObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

structure PowObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  base : Obj (M := M) α
  exponent : Obj (M := M) β

instance subRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] :
    Representation M (SubObj (M := M) α β) where
  wd a := In a.left C ∧ In a.right C
  denote a := M.subValue (denote a.left) (denote a.right)
  wd_isSet h := M.member_isSet (Semantics.sub_closed h.1 h.2)

instance mulRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] :
    Representation M (MulObj (M := M) α β) where
  wd a := In a.left C ∧ In a.right C
  denote a := M.mulValue (denote a.left) (denote a.right)
  wd_isSet h := M.member_isSet (Semantics.mul_closed h.1 h.2)

instance negRepresentation {M : Semantics.{u}} {α : Type v} [Representation M α] :
    Representation M (NegObj (M := M) α) where
  wd a := In a.arg C
  denote a := M.negValue (denote a.arg)
  wd_isSet h := M.member_isSet (Semantics.neg_closed h)

/-- The three supported integer-power domains are separate proof alternatives.
The source exponent remains an object, and its exact numeric value is certified.
None of these witnesses selects the object's denotation. -/
def PowDomain {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : PowObj (M := M) α β) : Prop :=
  (In a.base R ∧ ∃ n : ℕ, In a.exponent N ∧ Same a.exponent (number (n : ℂ))) ∨
  (In a.base C ∧ ∃ n : ℕ, In a.exponent N ∧ Same a.exponent (number (n : ℂ))) ∨
  (In a.base C ∧ ∃ z : ℤ, In a.exponent Z ∧
    ¬ Same a.base (number 0) ∧ Same a.exponent (number (z : ℂ)))

private theorem pow_nat_closed {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haC : In a C) (heValue : Same e (number (n : ℂ))) :
    M.mem (M.powValue (denote a) (denote e)) (M.standard .complex) := by
  obtain ⟨x, hx⟩ := (M.complex_members (denote a)).mp haC
  change denote e = M.number (n : ℂ) at heValue
  exact (M.complex_members _).mpr ⟨x ^ n, by rw [hx, heValue, M.pow_numbers_nat]⟩

private theorem pow_int_closed {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (z : ℤ)
    (haC : In a C) (ha0 : ¬ Same a (number 0))
    (heValue : Same e (number (z : ℂ))) :
    M.mem (M.powValue (denote a) (denote e)) (M.standard .complex) := by
  obtain ⟨x, hx⟩ := (M.complex_members (denote a)).mp haC
  have hx0 : x ≠ 0 := fun h => ha0 (hx.trans (congrArg M.number h))
  change denote e = M.number (z : ℂ) at heValue
  exact (M.complex_members _).mpr ⟨x ^ z, by rw [hx, heValue, M.pow_numbers_int x z hx0]⟩

instance powRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] :
    Representation M (PowObj (M := M) α β) where
  wd := PowDomain
  denote a := M.powValue (denote a.base) (denote a.exponent)
  wd_isSet h := M.member_isSet (by
    rcases h with ⟨haR, n, _heN, he⟩ | ⟨haC, n, _heN, he⟩ | ⟨haC, z, _heZ, ha0, he⟩
    · exact pow_nat_closed _ _ n (realToComplex _ haR) he
    · exact pow_nat_closed _ _ n haC he
    · exact pow_int_closed _ _ z haC ha0 he)

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

def sub {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : Obj (M := M) (SubObj (M := M) α β) :=
  ⟨⟨a, b⟩, ⟨haC, hbC⟩⟩

def mul {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : Obj (M := M) (MulObj (M := M) α β) :=
  ⟨⟨a, b⟩, ⟨haC, hbC⟩⟩

def neg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) : Obj (M := M) (NegObj (M := M) α) :=
  ⟨⟨a⟩, haC⟩

def powNatReal {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haR : In a R) (heN : In e N) (heValue : Same e (number (n : ℂ))) :
    Obj (M := M) (PowObj (M := M) α β) :=
  ⟨⟨a, e⟩, Or.inl ⟨haR, n, heN, heValue⟩⟩

def powNat {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haC : In a C) (heN : In e N) (heValue : Same e (number (n : ℂ))) :
    Obj (M := M) (PowObj (M := M) α β) :=
  ⟨⟨a, e⟩, Or.inr (Or.inl ⟨haC, n, heN, heValue⟩)⟩

def powInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (z : ℤ)
    (haC : In a C) (heZ : In e Z) (ha0 : ¬ Same a (number 0))
    (heValue : Same e (number (z : ℂ))) : Obj (M := M) (PowObj (M := M) α β) :=
  ⟨⟨a, e⟩, Or.inr (Or.inr ⟨haC, z, heZ, ha0, heValue⟩)⟩

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

def subInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : In (sub a b haC hbC) C :=
  Semantics.sub_closed haC hbC

def mulInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : In (mul a b haC hbC) C :=
  Semantics.mul_closed haC hbC

def negInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) : In (neg a haC) C :=
  Semantics.neg_closed haC

def powNatRealInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haR : In a R) (heN : In e N) (heValue : Same e (number (n : ℂ))) :
    In (powNatReal a e n haR heN heValue) C :=
  pow_nat_closed a e n (realToComplex a haR) heValue

def powNatInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haC : In a C) (heN : In e N) (heValue : Same e (number (n : ℂ))) :
    In (powNat a e n haC heN heValue) C :=
  pow_nat_closed a e n haC heValue

def powIntInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (z : ℤ)
    (haC : In a C) (heZ : In e Z) (ha0 : ¬ Same a (number 0))
    (heValue : Same e (number (z : ℂ))) : In (powInt a e z haC heZ ha0 heValue) C :=
  pow_int_closed a e z haC ha0 heValue

/-- Replay the structural C-membership rule using its actual two children.
The parent's certified domain still determines whether zero bases are legal;
the structural integer representative is checked against that domain's exact
exponent value before the corresponding numeric law is applied. -/
theorem powStructuralInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (haC : In p.val.base C) (heZ : In p.val.exponent Z) : In p C := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote p.val.exponent)).mp heZ
  have hdom : PowDomain p.val := p.wd
  change M.mem (M.powValue (denote p.val.base) (denote p.val.exponent))
    (M.standard .complex)
  rcases hdom with ⟨_haR, n, _heN, heValue⟩ |
    ⟨_wdC, n, _heN, heValue⟩ | ⟨_wdC, k, _heZ, ha0, heValue⟩
  · change denote p.val.exponent = M.number (n : ℂ) at heValue
    have agreement : (z : ℂ) = (n : ℂ) :=
      M.number_injective (hz.symm.trans heValue)
    exact pow_nat_closed p.val.base p.val.exponent n haC
      (hz.trans (congrArg M.number agreement))
  · change denote p.val.exponent = M.number (n : ℂ) at heValue
    have agreement : (z : ℂ) = (n : ℂ) :=
      M.number_injective (hz.symm.trans heValue)
    exact pow_nat_closed p.val.base p.val.exponent n haC
      (hz.trans (congrArg M.number agreement))
  · change denote p.val.exponent = M.number (k : ℂ) at heValue
    have agreement : (z : ℂ) = (k : ℂ) :=
      M.number_injective (hz.symm.trans heValue)
    exact pow_int_closed p.val.base p.val.exponent k haC ha0
      (hz.trans (congrArg M.number agreement))

theorem addInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haR : In a R) (hbR : In b R) :
    In (add a b (realToComplex a haR) (realToComplex b hbR)) R := by
  obtain ⟨x, hx⟩ := (M.real_members (denote a)).mp haR
  obtain ⟨y, hy⟩ := (M.real_members (denote b)).mp hbR
  exact (M.real_members _).mpr ⟨x + y, by
    change M.addValue (denote a) (denote b) = _
    rw [hx, hy, M.add_numbers, Complex.ofReal_add]⟩

theorem subInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haR : In a R) (hbR : In b R) :
    In (sub a b (realToComplex a haR) (realToComplex b hbR)) R := by
  obtain ⟨x, hx⟩ := (M.real_members (denote a)).mp haR
  obtain ⟨y, hy⟩ := (M.real_members (denote b)).mp hbR
  exact (M.real_members _).mpr ⟨x - y, by
    change M.subValue (denote a) (denote b) = _
    rw [hx, hy, M.sub_numbers, Complex.ofReal_sub]⟩

theorem mulInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haR : In a R) (hbR : In b R) :
    In (mul a b (realToComplex a haR) (realToComplex b hbR)) R := by
  obtain ⟨x, hx⟩ := (M.real_members (denote a)).mp haR
  obtain ⟨y, hy⟩ := (M.real_members (denote b)).mp hbR
  exact (M.real_members _).mpr ⟨x * y, by
    change M.mulValue (denote a) (denote b) = _
    rw [hx, hy, M.mul_numbers, Complex.ofReal_mul]⟩

theorem negInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In (neg a (realToComplex a haR)) R := by
  obtain ⟨x, hx⟩ := (M.real_members (denote a)).mp haR
  exact (M.real_members _).mpr ⟨-x, by
    change M.negValue (denote a) = _
    rw [hx, M.neg_numbers, Complex.ofReal_neg]⟩

theorem divInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haR : In a R) (hbR : In b R) (hb0 : ¬ Same b (number 0)) :
    In (div a b (realToComplex a haR) (realToComplex b hbR) hb0) R := by
  obtain ⟨x, hx⟩ := (M.real_members (denote a)).mp haR
  obtain ⟨y, hy⟩ := (M.real_members (denote b)).mp hbR
  have hy0 : (y : ℂ) ≠ 0 := fun h => hb0 (hy.trans (congrArg M.number h))
  exact (M.real_members _).mpr ⟨x / y, by
    change M.divValue (denote a) (denote b) = _
    rw [hx, hy, M.div_numbers _ _ hy0, Complex.ofReal_div]⟩

theorem addInQ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haQ : In a Q) (hbQ : In b Q) :
    In (add a b (rationalToComplex a haQ) (rationalToComplex b hbQ)) Q := by
  obtain ⟨x, hx⟩ := (M.rational_members (denote a)).mp haQ
  obtain ⟨y, hy⟩ := (M.rational_members (denote b)).mp hbQ
  exact (M.rational_members _).mpr ⟨x + y, by
    change M.addValue (denote a) (denote b) = _
    rw [hx, hy, M.add_numbers, Rat.cast_add]⟩

theorem subInQ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haQ : In a Q) (hbQ : In b Q) :
    In (sub a b (rationalToComplex a haQ) (rationalToComplex b hbQ)) Q := by
  obtain ⟨x, hx⟩ := (M.rational_members (denote a)).mp haQ
  obtain ⟨y, hy⟩ := (M.rational_members (denote b)).mp hbQ
  exact (M.rational_members _).mpr ⟨x - y, by
    change M.subValue (denote a) (denote b) = _
    rw [hx, hy, M.sub_numbers, Rat.cast_sub]⟩

theorem mulInQ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haQ : In a Q) (hbQ : In b Q) :
    In (mul a b (rationalToComplex a haQ) (rationalToComplex b hbQ)) Q := by
  obtain ⟨x, hx⟩ := (M.rational_members (denote a)).mp haQ
  obtain ⟨y, hy⟩ := (M.rational_members (denote b)).mp hbQ
  exact (M.rational_members _).mpr ⟨x * y, by
    change M.mulValue (denote a) (denote b) = _
    rw [hx, hy, M.mul_numbers, Rat.cast_mul]⟩

theorem negInQ {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haQ : In a Q) :
    In (neg a (rationalToComplex a haQ)) Q := by
  obtain ⟨q, hq⟩ := (M.rational_members (denote a)).mp haQ
  exact (M.rational_members _).mpr ⟨-q, by
    change M.negValue (denote a) = _
    rw [hq, M.neg_numbers, Rat.cast_neg]⟩

theorem divInQ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haQ : In a Q) (hbQ : In b Q) (hb0 : ¬ Same b (number 0)) :
    In (div a b (rationalToComplex a haQ) (rationalToComplex b hbQ) hb0) Q := by
  obtain ⟨x, hx⟩ := (M.rational_members (denote a)).mp haQ
  obtain ⟨y, hy⟩ := (M.rational_members (denote b)).mp hbQ
  have hy0 : (y : ℂ) ≠ 0 := fun h => hb0 (hy.trans (congrArg M.number h))
  exact (M.rational_members _).mpr ⟨x / y, by
    change M.divValue (denote a) (denote b) = _
    rw [hx, hy, M.div_numbers _ _ hy0, Rat.cast_div]⟩

theorem negInZ {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) : In (neg a (integerToComplex a haZ)) Z := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  exact (M.integer_members _).mpr ⟨-z, by
    change M.negValue (denote a) = _
    rw [hz, M.neg_numbers, Int.cast_neg]⟩

theorem powNatRealInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haR : In a R) (heN : In e N) (heValue : Same e (number (n : ℂ))) :
    In (powNatReal a e n haR heN heValue) R := by
  obtain ⟨x, hx⟩ := (M.real_members (denote a)).mp haR
  change denote e = M.number (n : ℂ) at heValue
  exact (M.real_members _).mpr ⟨x ^ n, by
    change M.powValue (denote a) (denote e) = _
    rw [hx, heValue, M.pow_numbers_nat, Complex.ofReal_pow]⟩

/-- Real closure consumes the owned power object's actual WD alternatives,
including their exact exponent witness and the integer branch's nonzero guard. -/
theorem powStructuralInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (haR : In p.val.base R) : In p R := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.base)).mp haR
  rcases p.wd with ⟨_haR, n, _heN, he⟩ | ⟨_haC, n, _heN, he⟩ |
    ⟨_haC, z, _heZ, ha0, he⟩
  · exact (M.real_members _).mpr ⟨r ^ n, by
      change denote p.val.exponent = M.number (n : ℂ) at he
      change M.powValue (denote p.val.base) (denote p.val.exponent) = _
      rw [hr, he, M.pow_numbers_nat, Complex.ofReal_pow]⟩
  · exact (M.real_members _).mpr ⟨r ^ n, by
      change denote p.val.exponent = M.number (n : ℂ) at he
      change M.powValue (denote p.val.base) (denote p.val.exponent) = _
      rw [hr, he, M.pow_numbers_nat, Complex.ofReal_pow]⟩
  · have hr0 : (r : ℂ) ≠ 0 := fun h => ha0 (hr.trans (congrArg M.number h))
    exact (M.real_members _).mpr ⟨r ^ z, by
      change denote p.val.exponent = M.number (z : ℂ) at he
      change M.powValue (denote p.val.base) (denote p.val.exponent) = _
      rw [hr, he, M.pow_numbers_int _ _ hr0, Complex.ofReal_zpow]⟩

theorem powStructuralInQ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (haQ : In p.val.base Q) : In p Q := by
  obtain ⟨q, hq⟩ := (M.rational_members (denote p.val.base)).mp haQ
  rcases p.wd with ⟨_haR, n, _heN, he⟩ | ⟨_haC, n, _heN, he⟩ |
    ⟨_haC, z, _heZ, ha0, he⟩
  · exact (M.rational_members _).mpr ⟨q ^ n, by
      change denote p.val.exponent = M.number (n : ℂ) at he
      change M.powValue (denote p.val.base) (denote p.val.exponent) = _
      rw [hq, he, M.pow_numbers_nat, Rat.cast_pow]⟩
  · exact (M.rational_members _).mpr ⟨q ^ n, by
      change denote p.val.exponent = M.number (n : ℂ) at he
      change M.powValue (denote p.val.base) (denote p.val.exponent) = _
      rw [hq, he, M.pow_numbers_nat, Rat.cast_pow]⟩
  · have hq0 : (q : ℂ) ≠ 0 := fun h => ha0 (hq.trans (congrArg M.number h))
    exact (M.rational_members _).mpr ⟨q ^ z, by
      change denote p.val.exponent = M.number (z : ℂ) at he
      change M.powValue (denote p.val.base) (denote p.val.exponent) = _
      rw [hq, he, M.pow_numbers_int _ _ hq0, Rat.cast_zpow]⟩

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

theorem denoteNumber (z : ℂ) : denote (number (M := M) z) = M.number z := rfl

theorem sameOfDenoteNumber {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y)
    (hxy : x = y) : Same a b :=
  ha.trans ((congrArg M.number hxy).trans hb.symm)

/-- Equality eliminates to native complex values only after both objects have
faithful numeric denotation witnesses. The objects' host carriers stay generic. -/
theorem nativeEqOfDenoteNumber {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y)
    (hSame : Same a b) : x = y :=
  M.number_injective (ha.symm.trans (hSame.trans hb))

theorem nativeNonzeroOfDenote {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (x : ℂ) (ha : denote a = M.number x)
    (ha0 : ¬ Same a (number 0)) : x ≠ 0 :=
  fun hx => ha0 (ha.trans (congrArg M.number hx))

theorem notSameOfNativeNonzero {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (x : ℂ) (ha : denote a = M.number x)
    (hx0 : x ≠ 0) : ¬ Same a (number 0) := by
  intro h
  exact hx0 (M.number_injective (ha.symm.trans h))

theorem notSameOfDenoteNumber {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y)
    (hxy : x ≠ y) : ¬ Same a b :=
  fun h => hxy (M.number_injective (ha.symm.trans (h.trans hb)))

theorem inOfDenoteNumber {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (x : ℂ) (A : Obj (M := M) β)
    (ha : denote a = M.number x) (hxA : In (number x) A) : In a A := by
  change M.mem (denote a) (denote A)
  rw [ha]
  exact hxA

def numberInR (r : ℝ) : In (number (M := M) (r : ℂ)) R :=
  (M.real_members (M.number (r : ℂ))).mpr ⟨r, rfl⟩

def numberInN (n : ℕ) : In (number (M := M) (n : ℂ)) N :=
  (M.natural_members (M.number (n : ℂ))).mpr ⟨n, rfl⟩

def numberInZ (z : ℤ) : In (number (M := M) (z : ℂ)) Z :=
  (M.integer_members (M.number (z : ℂ))).mpr ⟨z, rfl⟩

def numberInQ (q : ℚ) : In (number (M := M) (q : ℂ)) Q :=
  (M.rational_members (M.number (q : ℂ))).mpr ⟨q, rfl⟩

def numberInROfEq (z : ℂ) (r : ℝ) (hz : z = (r : ℂ)) : In (number (M := M) z) R :=
  (M.real_members (M.number z)).mpr ⟨r, congrArg M.number hz⟩

def numberInNOfEq (z : ℂ) (n : ℕ) (hz : z = (n : ℂ)) : In (number (M := M) z) N :=
  (M.natural_members (M.number z)).mpr ⟨n, congrArg M.number hz⟩

def numberInZOfEq (z : ℂ) (k : ℤ) (hz : z = (k : ℂ)) : In (number (M := M) z) Z :=
  (M.integer_members (M.number z)).mpr ⟨k, congrArg M.number hz⟩

def numberInQOfEq (z : ℂ) (q : ℚ) (hz : z = (q : ℂ)) : In (number (M := M) z) Q :=
  (M.rational_members (M.number z)).mpr ⟨q, congrArg M.number hz⟩

theorem numberRationalInQ (n d : ℤ) :
    In (number (M := M) ((n : ℂ) / (d : ℂ))) Q := by
  apply numberInQOfEq _ ((n : ℚ) / (d : ℚ))
  simp only [Rat.cast_div, Rat.cast_intCast]

theorem numberRationalInR (n d : ℤ) :
    In (number (M := M) ((n : ℂ) / (d : ℂ))) R := by
  apply numberInROfEq _ ((n : ℝ) / (d : ℝ))
  simp only [Complex.ofReal_div, Complex.ofReal_intCast]

theorem denoteAdd {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y) :
    denote (add a b haC hbC) = M.number (x + y) := by
  change M.addValue (denote a) (denote b) = _
  rw [ha, hb, M.add_numbers]

theorem denoteSub {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y) :
    denote (sub a b haC hbC) = M.number (x - y) := by
  change M.subValue (denote a) (denote b) = _
  rw [ha, hb, M.sub_numbers]

theorem denoteMul {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y) :
    denote (mul a b haC hbC) = M.number (x * y) := by
  change M.mulValue (denote a) (denote b) = _
  rw [ha, hb, M.mul_numbers]

theorem denoteNeg {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) (x : ℂ)
    (ha : denote a = M.number x) : denote (neg a haC) = M.number (-x) := by
  change M.negValue (denote a) = _
  rw [ha, M.neg_numbers]

theorem denoteDiv {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (hb0 : ¬ Same b (number 0)) (x y : ℂ)
    (ha : denote a = M.number x) (hb : denote b = M.number y) :
    denote (div a b haC hbC hb0) = M.number (x / y) := by
  change M.divValue (denote a) (denote b) = _
  rw [ha, hb, M.div_numbers x y (nativeNonzeroOfDenote b y hb hb0)]

theorem denotePowNatReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haR : In a R) (heN : In e N) (heValue : Same e (number (n : ℂ)))
    (x : ℂ) (ha : denote a = M.number x) :
    denote (powNatReal a e n haR heN heValue) = M.number (x ^ n) := by
  change denote e = M.number (n : ℂ) at heValue
  change M.powValue (denote a) (denote e) = _
  rw [ha, heValue, M.pow_numbers_nat]

theorem denotePowNat {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (n : ℕ)
    (haC : In a C) (heN : In e N) (heValue : Same e (number (n : ℂ)))
    (x : ℂ) (ha : denote a = M.number x) :
    denote (powNat a e n haC heN heValue) = M.number (x ^ n) := by
  change denote e = M.number (n : ℂ) at heValue
  change M.powValue (denote a) (denote e) = _
  rw [ha, heValue, M.pow_numbers_nat]

theorem denotePowInt {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β) (z : ℤ)
    (haC : In a C) (heZ : In e Z) (ha0 : ¬ Same a (number 0))
    (heValue : Same e (number (z : ℂ))) (x : ℂ) (ha : denote a = M.number x) :
    denote (powInt a e z haC heZ ha0 heValue) = M.number (x ^ z) := by
  change denote e = M.number (z : ℂ) at heValue
  change M.powValue (denote a) (denote e) = _
  rw [ha, heValue, M.pow_numbers_int x z (nativeNonzeroOfDenote a x ha ha0)]

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

noncomputable def asReal {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : ℝ :=
  Classical.choose ((M.real_members (denote a)).mp haR)

theorem asReal_spec {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) :
    denote a = M.number (asReal a haR : ℂ) :=
  Classical.choose_spec ((M.real_members (denote a)).mp haR)

theorem asReal_proofIndependent {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h₁ h₂ : In a R) :
    asReal a h₁ = asReal a h₂ :=
  Complex.ofReal_injective
    (M.number_injective ((asReal_spec a h₁).symm.trans (asReal_spec a h₂)))

theorem asComplex_eq_asReal {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) (haR : In a R) :
    asComplex a haC = (asReal a haR : ℂ) :=
  M.number_injective ((asComplex_spec a haC).symm.trans (asReal_spec a haR))

/-- A complex representative of a source-real object is its native real part.
The real-membership evidence is essential; this is not a global complex cast. -/
theorem denoteRealOfDenoteNumber {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (z : ℂ) (haR : In a R)
    (ha : denote a = M.number z) : denote a = M.number (z.re : ℂ) := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp haR
  have hz : z = (r : ℂ) := M.number_injective (ha.symm.trans hr)
  simpa only [hz, Complex.ofReal_re] using hr

theorem leOfDenoteReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (r s : ℝ)
    (ha : denote a = M.number (r : ℂ)) (hb : denote b = M.number (s : ℂ))
    (h : r ≤ s) : Le a b :=
  ⟨r, s, ha, hb, h⟩

theorem ltOfDenoteReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (r s : ℝ)
    (ha : denote a = M.number (r : ℂ)) (hb : denote b = M.number (s : ℂ))
    (h : r < s) : Lt a b :=
  ⟨r, s, ha, hb, h⟩

theorem le_iff_ofDenoteReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (r s : ℝ)
    (ha : denote a = M.number (r : ℂ)) (hb : denote b = M.number (s : ℂ)) :
    Le a b ↔ r ≤ s := by
  constructor
  · rintro ⟨r', s', ha', hb', h⟩
    have hr : r' = r := Complex.ofReal_injective (M.number_injective (ha'.symm.trans ha))
    have hs : s' = s := Complex.ofReal_injective (M.number_injective (hb'.symm.trans hb))
    simpa only [hr, hs] using h
  · exact leOfDenoteReal a b r s ha hb

theorem lt_iff_ofDenoteReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (r s : ℝ)
    (ha : denote a = M.number (r : ℂ)) (hb : denote b = M.number (s : ℂ)) :
    Lt a b ↔ r < s := by
  constructor
  · rintro ⟨r', s', ha', hb', h⟩
    have hr : r' = r := Complex.ofReal_injective (M.number_injective (ha'.symm.trans ha))
    have hs : s' = s := Complex.ofReal_injective (M.number_injective (hb'.symm.trans hb))
    simpa only [hr, hs] using h
  · exact ltOfDenoteReal a b r s ha hb

theorem le_iff_asReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haR : In a R) (hbR : In b R) :
    Le a b ↔ asReal a haR ≤ asReal b hbR :=
  le_iff_ofDenoteReal a b _ _ (asReal_spec a haR) (asReal_spec b hbR)

theorem lt_iff_asReal {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haR : In a R) (hbR : In b R) :
    Lt a b ↔ asReal a haR < asReal b hbR :=
  lt_iff_ofDenoteReal a b _ _ (asReal_spec a haR) (asReal_spec b hbR)

end Litex.NativeBridge

namespace Litex

theorem leOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (hab : Same a b) (hcd : Same c d) (hac : Le a c) : Le b d := by
  obtain ⟨r, s, hr, hs, h⟩ := hac
  exact ⟨r, s, hab.symm.trans hr, hcd.symm.trans hs, h⟩

theorem ltOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (hab : Same a b) (hcd : Same c d) (hac : Lt a c) : Lt b d := by
  obtain ⟨r, s, hr, hs, h⟩ := hac
  exact ⟨r, s, hab.symm.trans hr, hcd.symm.trans hs, h⟩

theorem leRefl {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : Le a a := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp haR
  exact ⟨r, r, hr, hr, le_refl r⟩

theorem naturalNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) : Le (number 0) a := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp haN
  refine ⟨0, (n : ℝ), ?_, ?_, Nat.cast_nonneg n⟩
  · simp only [denote, number, Representation.denote, Complex.ofReal_zero]
  · simpa only [Complex.ofReal_natCast] using hn

theorem ltToLe {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (hab : Lt a b) : Le a b := by
  obtain ⟨r, s, hr, hs, h⟩ := hab
  exact ⟨r, s, hr, hs, le_of_lt h⟩

theorem ltNotSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (hab : Lt a b) : ¬ Same a b := by
  obtain ⟨r, s, hr, hs, h⟩ := hab
  intro equal
  exact (ne_of_lt h)
    (Complex.ofReal_injective (M.number_injective (hr.symm.trans (equal.trans hs))))

theorem leTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Le a b) (hbc : Le b c) : Le a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, le_trans hrs (middle ▸ hst)⟩

theorem leAdd {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (haC : In a C) (hbC : In b C) (hcC : In c C) (hdC : In d C)
    (hab : Le a b) (hcd : Le c d) :
    Le (add a c haC hcC) (add b d hbC hdC) := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨t, v, ht, hv, htv⟩ := hcd
  refine ⟨r + t, s + v, ?_, ?_, add_le_add hrs htv⟩
  · change M.addValue (denote a) (denote c) = _
    rw [hr, ht, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote b) (denote d) = _
    rw [hs, hv, M.add_numbers, Complex.ofReal_add]

theorem leAddRight {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (haC : In a C) (hbC : In b C) (hcC : In c C) (hcR : In c R)
    (hab : Le a b) : Le (add a c haC hcC) (add b c hbC hcC) :=
  leAdd a b c c haC hbC hcC hcC hab (leRefl c hcR)

theorem leAddLeft {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (haC : In a C) (hbC : In b C) (hcC : In c C) (hcR : In c R)
    (hab : Le a b) : Le (add c a hcC haC) (add c b hcC hbC) :=
  leAdd c c a b hcC hcC haC hbC (leRefl c hcR) hab

theorem mulSelfNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) :
    Le (number 0) (mul a a (realToComplex a haR) (realToComplex a haR)) := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp haR
  refine ⟨0, r * r, ?_, ?_, mul_self_nonneg r⟩
  · simp only [denote, number, Representation.denote, Complex.ofReal_zero]
  · change M.mulValue (denote a) (denote a) = _
    rw [hr, M.mul_numbers, Complex.ofReal_mul]

/-- Replay the exact even natural exponent independently of which supported
power WD alternative certified the owned object. -/
theorem powStructuralNonnegativeOfEven {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (haR : In p.val.base R)
    (n : ℕ) (heValue : Same p.val.exponent (number (n : ℂ))) (hEven : Even n) :
    Le (number 0) p := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.base)).mp haR
  refine ⟨0, r ^ n, ?_, ?_, hEven.pow_nonneg r⟩
  · simp only [denote, number, Representation.denote, Complex.ofReal_zero]
  · change denote p.val.exponent = M.number (n : ℂ) at heValue
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [hr, heValue, M.pow_numbers_nat, Complex.ofReal_pow]

theorem mulNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C)
    (ha0 : ¬ Same a (number 0)) (hb0 : ¬ Same b (number 0)) :
    ¬ Same (mul a b haC hbC) (number 0) := by
  let x := NativeBridge.asComplex a haC
  let y := NativeBridge.asComplex b hbC
  have hx := NativeBridge.asComplex_spec a haC
  have hy := NativeBridge.asComplex_spec b hbC
  exact NativeBridge.notSameOfNativeNonzero _ (x * y)
    (NativeBridge.denoteMul a b haC hbC x y hx hy)
    (mul_ne_zero (NativeBridge.nativeNonzeroOfDenote a x hx ha0)
      (NativeBridge.nativeNonzeroOfDenote b y hy hb0))

end Litex

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

theorem natural_members (x : ZFSet.{0}) :
    x ∈ standardSet .natural ↔ ∃ n : ℕ, x = codeComplex (n : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩

theorem integer_members (x : ZFSet.{0}) :
    x ∈ standardSet .integer ↔ ∃ z : ℤ, x = codeComplex (z : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem rational_members (x : ZFSet.{0}) :
    x ∈ standardSet .rational ↔ ∃ q : ℚ, x = codeComplex (q : ℂ) := by
  simp only [standardSet, ZFSet.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩

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

noncomputable def subValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a - decodeComplex b)

noncomputable def mulValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a * decodeComplex b)

noncomputable def negValue (a : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (-decodeComplex a)

noncomputable def divValue (a b : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a / decodeComplex b)

/-- Totalization outside the certified integer-power domain belongs only to
this explicit candidate model. The public constructor retains the exponent
object and evidence identifying it with an exact integer. -/
noncomputable def powValue (a e : ZFSet.{0}) : ZFSet.{0} :=
  codeComplex (decodeComplex a ^ (⌊(decodeComplex e).re⌋ : ℤ))

theorem add_numbers (a b : ℂ) :
    addValue (codeComplex a) (codeComplex b) = codeComplex (a + b) := by
  simp only [addValue, decodeComplex_codeComplex]

theorem sub_numbers (a b : ℂ) :
    subValue (codeComplex a) (codeComplex b) = codeComplex (a - b) := by
  simp only [subValue, decodeComplex_codeComplex]

theorem mul_numbers (a b : ℂ) :
    mulValue (codeComplex a) (codeComplex b) = codeComplex (a * b) := by
  simp only [mulValue, decodeComplex_codeComplex]

theorem neg_numbers (a : ℂ) :
    negValue (codeComplex a) = codeComplex (-a) := by
  simp only [negValue, decodeComplex_codeComplex]

theorem div_numbers (a b : ℂ) (_hb : b ≠ 0) :
    divValue (codeComplex a) (codeComplex b) = codeComplex (a / b) := by
  simp only [divValue, decodeComplex_codeComplex]

theorem pow_numbers_nat (a : ℂ) (n : ℕ) :
    powValue (codeComplex a) (codeComplex (n : ℂ)) = codeComplex (a ^ n) := by
  simp only [powValue, decodeComplex_codeComplex, Complex.natCast_re, Int.floor_natCast,
    zpow_natCast]

theorem pow_numbers_int (a : ℂ) (z : ℤ) (_ha : a ≠ 0) :
    powValue (codeComplex a) (codeComplex (z : ℂ)) = codeComplex (a ^ z) := by
  simp only [powValue, decodeComplex_codeComplex, Complex.intCast_re, Int.floor_intCast]

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
  subValue := subValue
  mulValue := mulValue
  negValue := negValue
  divValue := divValue
  powValue := powValue
  number_injective := codeComplex_injective
  complex_members := complex_members
  natural_members := natural_members
  integer_members := integer_members
  rational_members := rational_members
  real_members := real_members
  real_subset_complex := real_subset_complex
  member_isSet := fun _ => True.intro
  standard_isSet := fun _ => True.intro
  add_numbers := add_numbers
  sub_numbers := sub_numbers
  mul_numbers := mul_numbers
  neg_numbers := neg_numbers
  div_numbers := div_numbers
  pow_numbers_nat := pow_numbers_nat
  pow_numbers_int := pow_numbers_int
  add_closed := add_closed
  div_closed := div_closed

end Litex.NumericModel
