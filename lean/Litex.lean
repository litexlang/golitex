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

theorem addInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haN : In a N) (hbN : In b N) :
    In (add a b (naturalToComplex a haN) (naturalToComplex b hbN)) N := by
  obtain ⟨x, hx⟩ := (M.natural_members (denote a)).mp haN
  obtain ⟨y, hy⟩ := (M.natural_members (denote b)).mp hbN
  exact (M.natural_members _).mpr ⟨x + y, by
    change M.addValue (denote a) (denote b) = _
    rw [hx, hy, M.add_numbers, Nat.cast_add]⟩

theorem mulInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haN : In a N) (hbN : In b N) :
    In (mul a b (naturalToComplex a haN) (naturalToComplex b hbN)) N := by
  obtain ⟨x, hx⟩ := (M.natural_members (denote a)).mp haN
  obtain ⟨y, hy⟩ := (M.natural_members (denote b)).mp hbN
  exact (M.natural_members _).mpr ⟨x * y, by
    change M.mulValue (denote a) (denote b) = _
    rw [hx, hy, M.mul_numbers, Nat.cast_mul]⟩

theorem addInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haZ : In a Z) (hbZ : In b Z) :
    In (add a b (integerToComplex a haZ) (integerToComplex b hbZ)) Z := by
  obtain ⟨x, hx⟩ := (M.integer_members (denote a)).mp haZ
  obtain ⟨y, hy⟩ := (M.integer_members (denote b)).mp hbZ
  exact (M.integer_members _).mpr ⟨x + y, by
    change M.addValue (denote a) (denote b) = _
    rw [hx, hy, M.add_numbers, Int.cast_add]⟩

theorem subInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haZ : In a Z) (hbZ : In b Z) :
    In (sub a b (integerToComplex a haZ) (integerToComplex b hbZ)) Z := by
  obtain ⟨x, hx⟩ := (M.integer_members (denote a)).mp haZ
  obtain ⟨y, hy⟩ := (M.integer_members (denote b)).mp hbZ
  exact (M.integer_members _).mpr ⟨x - y, by
    change M.subValue (denote a) (denote b) = _
    rw [hx, hy, M.sub_numbers, Int.cast_sub]⟩

theorem mulInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haZ : In a Z) (hbZ : In b Z) :
    In (mul a b (integerToComplex a haZ) (integerToComplex b hbZ)) Z := by
  obtain ⟨x, hx⟩ := (M.integer_members (denote a)).mp haZ
  obtain ⟨y, hy⟩ := (M.integer_members (denote b)).mp hbZ
  exact (M.integer_members _).mpr ⟨x * y, by
    change M.mulValue (denote a) (denote b) = _
    rw [hx, hy, M.mul_numbers, Int.cast_mul]⟩

theorem powStructuralInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (haN : In p.val.base N) (heN : In p.val.exponent N) : In p N := by
  obtain ⟨a, ha⟩ := (M.natural_members (denote p.val.base)).mp haN
  obtain ⟨n, he⟩ := (M.natural_members (denote p.val.exponent)).mp heN
  exact (M.natural_members _).mpr ⟨a ^ n, by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [ha, he, M.pow_numbers_nat, Nat.cast_pow]⟩

theorem powStructuralInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (haZ : In p.val.base Z) (heN : In p.val.exponent N) : In p Z := by
  obtain ⟨a, ha⟩ := (M.integer_members (denote p.val.base)).mp haZ
  obtain ⟨n, he⟩ := (M.natural_members (denote p.val.exponent)).mp heN
  exact (M.integer_members _).mpr ⟨a ^ n, by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [ha, he, M.pow_numbers_nat, Int.cast_pow]⟩

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

/-- Natural observation reads the fixed denotation. A source membership proof
justifies the observation; it does not choose a new host representation. -/
noncomputable def naturalValue (x : M.Value) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, x = M.number (n : ℂ) then Classical.choose h else 0

theorem naturalValue_spec (x : M.Value) (hx : M.mem x (M.standard .natural)) :
    x = M.number (naturalValue x : ℂ) := by
  classical
  have h := (M.natural_members x).mp hx
  unfold naturalValue
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem naturalValue_number (n : ℕ) : naturalValue (M.number (n : ℂ)) = n := by
  have h := M.number_injective
    (naturalValue_spec (M.number (n : ℂ)) (numberInN n))
  exact_mod_cast h.symm

noncomputable def asNat {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (_haN : In a N) : ℕ := naturalValue (denote a)

theorem asNat_spec {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) :
    Same a (number (asNat a haN : ℂ)) := naturalValue_spec (denote a) haN

theorem asNat_proofIndependent {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h₁ h₂ : In a N) : asNat a h₁ = asNat a h₂ := rfl

theorem asNat_ofDenote {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) (n : ℕ)
    (ha : denote a = M.number (n : ℂ)) : asNat a haN = n := by
  have hs : denote a = M.number (asNat a haN : ℂ) := asNat_spec a haN
  exact_mod_cast M.number_injective (hs.symm.trans ha)

theorem denotePowStructuralNat {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (n : ℕ)
    (heValue : Same p.val.exponent (number (n : ℂ))) (x : ℂ)
    (hBase : denote p.val.base = M.number x) : denote p = M.number (x ^ n) := by
  change M.powValue (denote p.val.base) (denote p.val.exponent) = _
  change denote p.val.exponent = M.number (n : ℂ) at heValue
  rw [hBase, heValue, M.pow_numbers_nat]

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

/-- A total raw interpretation is used only through an owned absolute-value
object whose original argument is certified real. -/
noncomputable def absValue {M : Semantics.{u}} (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, x = M.number (r : ℂ) then
    M.number ((|Classical.choose h| : ℝ) : ℂ) else M.number 0

theorem absValue_number {M : Semantics.{u}} (r : ℝ) :
    absValue (M.number (r : ℂ)) = M.number ((|r| : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold absValue
  rw [dif_pos h, hr]

structure AbsObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance absRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (AbsObj (M := M) α) where
  wd a := In a.arg R
  denote a := absValue (denote a.arg)
  wd_isSet {a} ha := by
    obtain ⟨r, hr⟩ := (M.real_members (denote a.arg)).mp ha
    exact M.member_isSet ((M.real_members _).mpr ⟨|r|, by
      rw [hr, absValue_number]⟩)

noncomputable def abs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : Obj (M := M) (AbsObj (M := M) α) :=
  ⟨⟨a⟩, haR⟩

namespace NativeBridge

theorem denoteAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (r : ℝ)
    (hr : denote a = M.number (r : ℂ)) :
    denote (abs a haR) = M.number ((|r| : ℝ) : ℂ) := by
  change absValue (denote a) = _
  rw [hr, absValue_number]

end NativeBridge

theorem absInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In (abs a haR) R :=
  (M.real_members _).mpr ⟨|NativeBridge.asReal a haR|,
    NativeBridge.denoteAbs a haR _ (NativeBridge.asReal_spec a haR)⟩

theorem absInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In (abs a haR) C :=
  realToComplex _ (absInR a haR)

theorem absNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : Le (number 0) (abs a haR) :=
  NativeBridge.leOfDenoteReal _ _ 0 |NativeBridge.asReal a haR| rfl
    (NativeBridge.denoteAbs a haR _ (NativeBridge.asReal_spec a haR)) (abs_nonneg _)

theorem absOfNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    Same (abs a haR) a := by
  have h := (NativeBridge.le_iff_ofDenoteReal (number 0) a 0
    (NativeBridge.asReal a haR) rfl (NativeBridge.asReal_spec a haR)).mp ha0
  exact (NativeBridge.denoteAbs a haR _ (NativeBridge.asReal_spec a haR)).trans
    ((congrArg (fun r : ℝ => M.number (r : ℂ)) (abs_of_nonneg h)).trans
      (NativeBridge.asReal_spec a haR).symm)

theorem addCancelRightRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add a k ha hk) (add b k hb hk)) : Same a b := by
  change M.addValue (denote a) (denote k) = M.addValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr
    (add_right_cancel (M.number_injective h))

theorem addCancelRightLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add a k ha hk) (add k b hk hb)) : Same a b := by
  change M.addValue (denote a) (denote k) = M.addValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  have he := M.number_injective h
  rw [add_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex b hb)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (add_right_cancel he)

theorem addCancelLeftRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add k a hk ha) (add b k hb hk)) : Same a b := by
  change M.addValue (denote k) (denote a) = M.addValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  have he := M.number_injective h
  rw [add_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex a ha)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (add_right_cancel he)

theorem addCancelLeftLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add k a hk ha) (add k b hk hb)) : Same a b := by
  change M.addValue (denote k) (denote a) = M.addValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr
    (add_left_cancel (M.number_injective h))

/-- Replay the selected unequal-operands rule for a nonzero difference. -/
theorem subNonzeroOfNotSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a C) (hb : In b C) (hab : ¬ Same a b) :
    ¬ Same (sub a b ha hb) (number 0) := by
  intro h
  apply hab
  change M.subValue (denote a) (denote b) = M.number 0 at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    M.sub_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr
    (sub_eq_zero.mp (M.number_injective h))

/-- Replay a known nonzero difference without searching for another inequality. -/
theorem notSameOfSubNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a C) (hb : In b C)
    (hsub : ¬ Same (sub a b ha hb) (number 0)) : ¬ Same a b := by
  intro hab
  apply hsub
  change M.subValue (denote a) (denote b) = M.number 0
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    M.sub_numbers, (NativeBridge.same_iff_asComplex a b ha hb).mp hab, sub_self]

/-- Replay the source's shared-subtrahend and shared-minuend cancellation rules. -/
theorem subCancelRightRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (sub a k ha hk) (sub b k hb hk)) : Same a b := by
  change M.subValue (denote a) (denote k) = M.subValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.sub_numbers, M.sub_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (sub_left_inj.mp (M.number_injective h))

theorem subCancelLeftLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (sub k a hk ha) (sub k b hk hb)) : Same a b := by
  change M.subValue (denote k) (denote a) = M.subValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.sub_numbers, M.sub_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (sub_right_inj.mp (M.number_injective h))

theorem mulCancelRightRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul a k ha hk) (mul b k hb hk)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote a) (denote k) =
    M.mulValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_right_cancel₀ hk0' (M.number_injective h))

theorem mulCancelRightLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul a k ha hk) (mul k b hk hb)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote a) (denote k) =
    M.mulValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  have he := M.number_injective h
  rw [mul_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex b hb)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_right_cancel₀ hk0' he)

theorem mulCancelLeftRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul k a hk ha) (mul b k hb hk)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote k) (denote a) =
    M.mulValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  have he := M.number_injective h
  rw [mul_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex a ha)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_right_cancel₀ hk0' he)

theorem mulCancelLeftLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul k a hk ha) (mul k b hk hb)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote k) (denote a) =
    M.mulValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_left_cancel₀ hk0' (M.number_injective h))

theorem divCancelCommonDenominator {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (div a k ha hk hk0) (div b k hb hk hk0)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.divValue (denote a) (denote k) = M.divValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.div_numbers _ _ hk0', M.div_numbers _ _ hk0'] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr ((div_left_inj' hk0').mp (M.number_injective h))

theorem divCancelNonzeroNumerator {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0)) (ha0 : ¬ Same a (number 0))
    (hb0 : ¬ Same b (number 0))
    (h : Same (div k a hk ha ha0) (div k b hk hb hb0)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  have ha0' := NativeBridge.nativeNonzeroOfDenote a (NativeBridge.asComplex a ha)
    (NativeBridge.asComplex_spec a ha) ha0
  have hb0' := NativeBridge.nativeNonzeroOfDenote b (NativeBridge.asComplex b hb)
    (NativeBridge.asComplex_spec b hb) hb0
  change M.divValue (denote k) (denote a) = M.divValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.div_numbers _ _ ha0', M.div_numbers _ _ hb0'] at h
  have he := (div_eq_div_iff ha0' hb0').mp (M.number_injective h)
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_left_cancel₀ hk0' he).symm


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

theorem leEqOrLt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (h : Le a b) : Same a b ∨ Lt a b := by
  obtain ⟨r, s, hr, hs, hrs⟩ := h
  rcases eq_or_lt_of_le hrs with equal | strict
  · exact Or.inl (hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ)) equal).trans hs.symm))
  · exact Or.inr ⟨r, s, hr, hs, strict⟩

/-- The selected integer-tail certificate retains both original integer
memberships even though the checked order alternative also holds for reals. -/
theorem integerSuccessorTail {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (subject : Obj (M := M) α) (base : Obj (M := M) β)
    (_hSubjectZ : In subject Z) (_hBaseZ : In base Z) (hLower : Le base subject) :
    Same subject base ∨ Lt base subject := by
  rcases leEqOrLt base subject hLower with equal | strict
  · exact Or.inl equal.symm
  · exact Or.inr strict

theorem ltNotSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (hab : Lt a b) : ¬ Same a b := by
  obtain ⟨r, s, hr, hs, h⟩ := hab
  intro equal
  exact (ne_of_lt h)
    (Complex.ofReal_injective (M.number_injective (hr.symm.trans (equal.trans hs))))

/-- Replay positivity of an owned sum using its original constructor evidence. -/
theorem addPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Lt (number 0) a) (hb : Lt (number 0) b) :
    Lt (number 0) (add a b haC hbC) := by
  obtain ⟨r₀, r, hzeroR, hr, hposR⟩ := ha
  obtain ⟨s₀, s, hzeroS, hs, hposS⟩ := hb
  change M.number 0 = M.number (r₀ : ℂ) at hzeroR
  change M.number 0 = M.number (s₀ : ℂ) at hzeroS
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroR).symm
  have hs₀ : s₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroS).symm
  subst r₀
  subst s₀
  refine NativeBridge.ltOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_pos hposR hposS)
  change M.addValue (denote a) (denote b) = M.number ((r + s : ℝ) : ℂ)
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

/-- Replay the selected positive/positive quotient rule. The semantic
denominator proof still comes from the original division constructor. -/
theorem divPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (hNonzero : ¬ Same b (number 0))
    (ha : Lt (number 0) a) (hb : Lt (number 0) b) :
    Lt (number 0) (div a b haC hbC hNonzero) := by
  obtain ⟨r₀, r, hzeroR, hr, hposR⟩ := ha
  obtain ⟨s₀, s, hzeroS, hs, hposS⟩ := hb
  change M.number 0 = M.number (r₀ : ℂ) at hzeroR
  change M.number 0 = M.number (s₀ : ℂ) at hzeroS
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroR).symm
  have hs₀ : s₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroS).symm
  subst r₀
  subst s₀
  have hsNonzero : (s : ℂ) ≠ 0 := fun h => hNonzero (hs.trans (congrArg M.number h))
  refine NativeBridge.ltOfDenoteReal (number 0) (div a b haC hbC hNonzero) 0 (r / s)
    rfl ?_ (div_pos hposR hposS)
  change M.divValue (denote a) (denote b) = M.number ((r / s : ℝ) : ℂ)
  rw [hr, hs, M.div_numbers _ _ hsNonzero, Complex.ofReal_div]

theorem mulPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Lt (number 0) a) (hb : Lt (number 0) b) :
    Lt (number 0) (mul a b haC hbC) := by
  obtain ⟨r₀, r, hzeroR, hr, hposR⟩ := ha
  obtain ⟨s₀, s, hzeroS, hs, hposS⟩ := hb
  change M.number 0 = M.number (r₀ : ℂ) at hzeroR
  change M.number 0 = M.number (s₀ : ℂ) at hzeroS
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroR).symm
  have hs₀ : s₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroS).symm
  subst r₀
  subst s₀
  refine NativeBridge.ltOfDenoteReal (number 0) (mul a b haC hbC) 0 (r * s)
    rfl ?_ (mul_pos hposR hposS)
  change M.mulValue (denote a) (denote b) = M.number ((r * s : ℝ) : ℂ)
  rw [hr, hs, M.mul_numbers, Complex.ofReal_mul]

theorem powStructuralPositiveOfPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hbase : Lt (number 0) p.val.base) : Lt (number 0) p := by
  obtain ⟨r₀, r, hzero, hr, hpos⟩ := hbase
  change M.number 0 = M.number (r₀ : ℂ) at hzero
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzero).symm
  subst r₀
  rcases p.wd with ⟨_haR, n, _heN, he⟩ | ⟨_haC, n, _heN, he⟩ |
    ⟨_haC, z, _heZ, ha0, he⟩
  · refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ n) rfl ?_ (pow_pos hpos n)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    change denote p.val.exponent = M.number (n : ℂ) at he
    rw [hr, he, M.pow_numbers_nat, Complex.ofReal_pow]
  · refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ n) rfl ?_ (pow_pos hpos n)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    change denote p.val.exponent = M.number (n : ℂ) at he
    rw [hr, he, M.pow_numbers_nat, Complex.ofReal_pow]
  · have hr0 : (r : ℂ) ≠ 0 := fun h => ha0 (hr.trans (congrArg M.number h))
    refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ z) rfl ?_ (zpow_pos hpos z)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    change denote p.val.exponent = M.number (z : ℂ) at he
    rw [hr, he, M.pow_numbers_int _ _ hr0, Complex.ofReal_zpow]

theorem powStructuralPositiveOfEven {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (haR : In p.val.base R)
    (n : ℕ) (heValue : Same p.val.exponent (number (n : ℂ)))
    (hEven : Even n) (_hPositive : 0 < n)
    (hBaseNonzero : ¬ Same p.val.base (number 0)) : Lt (number 0) p := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.base)).mp haR
  have hr0 : r ≠ 0 := by
    intro h
    apply hBaseNonzero
    change denote p.val.base = M.number 0
    rw [hr, h, Complex.ofReal_zero]
  refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ n) rfl ?_ (hEven.pow_pos hr0)
  change M.powValue (denote p.val.base) (denote p.val.exponent) = _
  change denote p.val.exponent = M.number (n : ℂ) at heValue
  rw [hr, heValue, M.pow_numbers_nat, Complex.ofReal_pow]

theorem absPowStructuralSame {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (left : Obj (M := M) (PowObj (M := M) (AbsObj (M := M) α) β))
    (right : Obj (M := M) (PowObj (M := M) α γ)) (n : ℕ)
    (hBase : Same left.val.base.val.arg right.val.base)
    (heL : Same left.val.exponent (number (n : ℂ)))
    (heR : Same right.val.exponent (number (n : ℂ))) (hEven : Even n) : Same left right := by
  obtain ⟨r, hr⟩ := (M.real_members (denote left.val.base.val.arg)).mp left.val.base.wd
  have hrRight : denote right.val.base = M.number (r : ℂ) := hBase.symm.trans hr
  change M.powValue (absValue (denote left.val.base.val.arg)) (denote left.val.exponent) =
    M.powValue (denote right.val.base) (denote right.val.exponent)
  change denote left.val.exponent = M.number (n : ℂ) at heL
  change denote right.val.exponent = M.number (n : ℂ) at heR
  rw [hr, hrRight, heL, heR, absValue_number, M.pow_numbers_nat, M.pow_numbers_nat,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow, hEven.pow_abs]

theorem leTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Le a b) (hbc : Le b c) : Le a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, le_trans hrs (middle ▸ hst)⟩

theorem ltTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Lt a b) (hbc : Lt b c) : Lt a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, lt_trans hrs (middle ▸ hst)⟩

theorem ltLeTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Lt a b) (hbc : Le b c) : Lt a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, lt_of_lt_of_le hrs (middle ▸ hst)⟩

theorem leLtTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Le a b) (hbc : Lt b c) : Lt a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, lt_of_le_of_lt hrs (middle ▸ hst)⟩

theorem integerToNaturalOfNonnegative {M : Semantics.{u}} {α : Type v}
    [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) (ha0 : Le (number 0) a) : In a N := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  obtain ⟨r, s, hr, hs, hrs⟩ := ha0
  change M.number 0 = M.number (r : ℂ) at hr
  have hr0 : r = 0 := Complex.ofReal_injective (M.number_injective hr).symm
  have hsz : s = (z : ℝ) := Complex.ofReal_injective (by
    have hcast : (s : ℂ) = (z : ℂ) := M.number_injective (hs.symm.trans hz)
    exact_mod_cast hcast)
  have nonnegative : (0 : ℝ) ≤ (z : ℝ) := by simpa only [hr0, hsz] using hrs
  have hz0 : 0 ≤ z := by exact_mod_cast nonnegative
  have castEq : (z.toNat : ℂ) = (z : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hz0
  exact (M.natural_members _).mpr ⟨z.toNat, hz.trans (congrArg M.number castEq.symm)⟩

theorem integerSuccessorLowerBound {M : Semantics.{u}} {α : Type v}
    [Representation M α] (a : Obj (M := M) α) (haZ : In a Z)
    (h0a : Lt (number 0) a) : Le (number 1) a := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  have hzReal : denote a = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  have hpos : (0 : ℝ) < (z : ℝ) :=
    (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 (z : ℝ) rfl hzReal).mp h0a
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hpos
  have hzOne : (1 : ℤ) ≤ z := Int.add_one_le_iff.mpr hzpos
  exact NativeBridge.leOfDenoteReal (number 1) a 1 (z : ℝ) rfl hzReal
    (by exact_mod_cast hzOne)

theorem subNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (hba : Le p.val.right p.val.left) : Le (number 0) p := by
  obtain ⟨s, r, hs, hr, hsr⟩ := hba
  refine NativeBridge.leOfDenoteReal (number 0) p 0 (r - s) rfl ?_ (sub_nonneg.mpr hsr)
  change M.subValue (denote p.val.left) (denote p.val.right) = _
  rw [hr, hs, M.sub_numbers, Complex.ofReal_sub]

theorem subtractOneLess {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β)) (haR : In p.val.left R)
    (hOne : Same p.val.right (number 1)) : Lt p p.val.left := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.left)).mp haR
  refine NativeBridge.ltOfDenoteReal p p.val.left (r - 1) r ?_ hr
    (sub_lt_self r zero_lt_one)
  change M.subValue (denote p.val.left) (denote p.val.right) = _
  change denote p.val.right = M.number 1 at hOne
  rw [hr, hOne, M.sub_numbers, Complex.ofReal_sub, Complex.ofReal_one]

theorem predecessorInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β)) (hn : In p.val.left N)
    (hPositive : Lt (number 0) p.val.left)
    (hOne : Same p.val.right (number 1)) : In p N := by
  let n := NativeBridge.asNat p.val.left hn
  have hs : denote p.val.left = M.number (n : ℂ) := NativeBridge.asNat_spec p.val.left hn
  have hr : denote p.val.left = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hs
  have hpos : (0 : ℝ) < (n : ℝ) :=
    (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.left 0 (n : ℝ) rfl hr).mp hPositive
  have hnpos : 0 < n := by exact_mod_cast hpos
  exact (M.natural_members _).mpr ⟨n - 1, by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    change denote p.val.right = M.number 1 at hOne
    rw [hs, hOne, M.sub_numbers,
      Nat.cast_sub (Nat.succ_le_of_lt hnpos), Nat.cast_one]⟩

theorem weakIntegerLowerBoundInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (bound : Obj (M := M) α) (a : Obj (M := M) β)
    (haZ : In a Z) (hbound : Le (number 0) bound) (h : Le bound a) : In a N :=
  integerToNaturalOfNonnegative a haZ (leTrans (number 0) bound a hbound h)

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

theorem divNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C)
    (ha0 : ¬ Same a (number 0)) (hb0 : ¬ Same b (number 0)) :
    ¬ Same (div a b haC hbC hb0) (number 0) := by
  let x := NativeBridge.asComplex a haC
  let y := NativeBridge.asComplex b hbC
  have hx := NativeBridge.asComplex_spec a haC
  have hy := NativeBridge.asComplex_spec b hbC
  exact NativeBridge.notSameOfNativeNonzero _ (x / y)
    (NativeBridge.denoteDiv a b haC hbC hb0 x y hx hy)
    (div_ne_zero (NativeBridge.nativeNonzeroOfDenote a x hx ha0)
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

/-- A concrete candidate for the numeric object interface. The supported set
and function contracts have separate instances below; this is not a complete
interpretation of all Litex objects and rules. Every Value is
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

namespace Litex

universe t

/-- This representation exists only for values of the chosen semantic model. -/
instance semanticValueRepresentation (M : Semantics.{u}) : Representation M M.Value where
  wd x := M.isSet x
  denote x := x
  wd_isSet h := h

def semanticObject {M : Semantics.{u}} (x : M.Value) (hx : M.isSet x) :
    Obj (M := M) M.Value := ⟨x, hx⟩

theorem semanticObject_denote {M : Semantics.{u}} (x : M.Value) (hx : M.isSet x) :
    denote (semanticObject x hx) = x := rfl

namespace NativeBridge

theorem naturalValue_lt_number {M : Semantics.{u}} (n : ℕ) (x : M.Value)
    (hx : M.mem x (M.standard .natural))
    (hLt : Lt (semanticObject x (M.member_isSet hx)) (number (n : ℂ))) :
    naturalValue x < n := by
  have h := (lt_iff_ofDenoteReal (semanticObject x (M.member_isSet hx))
    (number (n : ℂ)) (naturalValue x : ℝ) (n : ℝ)
    (by simpa only [semanticObject_denote, Complex.ofReal_natCast] using naturalValue_spec x hx)
    (by simp only [denoteNumber, Complex.ofReal_natCast])).mp hLt
  exact_mod_cast h

theorem naturalValue_pos {M : Semantics.{u}} (x : M.Value)
    (hx : M.mem x (M.standard .natural))
    (hLt : Lt (number 0) (semanticObject x (M.member_isSet hx))) :
    0 < naturalValue x := by
  have h := (lt_iff_ofDenoteReal (number 0) (semanticObject x (M.member_isSet hx))
    0 (naturalValue x : ℝ) rfl
    (by simpa only [semanticObject_denote, Complex.ofReal_natCast] using naturalValue_spec x hx)).mp hLt
  exact_mod_cast h

end NativeBridge

/-- The exported index keeps its original representation. Only the proof
interpretation observes a nonnegative integer as a natural number. -/
theorem integerInductionFromZero {M : Semantics.{u}}
    (P : M.Value → Prop) (h0 : P (M.number 0))
    (hstep : ∀ (k : M.Value) (hkZ : M.mem k (M.standard .integer)),
      Le (number 0) (semanticObject k (M.member_isSet hkZ)) →
      P k → P (M.addValue k (M.number 1)))
    {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) (ha0 : Le (number 0) a) : P (denote a) := by
  have hn := integerToNaturalOfNonnegative a haZ ha0
  have hall : ∀ n : ℕ, P (M.number (n : ℂ)) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero] using h0
    | succ n ih =>
      have hz : M.mem (M.number (n : ℂ)) (M.standard .integer) :=
        (M.integer_members _).mpr ⟨(n : ℤ), by simp only [Int.cast_natCast]⟩
      have hnonnegative := naturalNonnegative
        (semanticObject (M.number (n : ℂ)) (M.member_isSet hz))
        (NativeBridge.numberInN n)
      simpa only [M.add_numbers, Nat.cast_add, Nat.cast_one] using
        hstep (M.number (n : ℂ)) hz hnonnegative ih
  exact (NativeBridge.asNat_spec a hn).symm ▸ hall (NativeBridge.asNat a hn)

/-- The bounded set primitives are shared by set builders and function domains.
The laws are explicit model obligations, proved by the ZF model below. -/
class SetSemantics (M : Semantics.{u}) where
  emptyValue : M.Value
  empty_members : ∀ x, ¬ M.mem x emptyValue
  empty_isSet : M.isSet emptyValue
  insertValue : M.Value → M.Value → M.Value
  insert_members : ∀ a A x, M.mem x (insertValue a A) ↔ x = a ∨ M.mem x A
  insert_isSet : ∀ a A, M.isSet a → M.isSet A → M.isSet (insertValue a A)
  sepValue : M.Value → (M.Value → Prop) → M.Value
  sep_members : ∀ D p x, M.mem x (sepValue D p) ↔ M.mem x D ∧ p x
  sep_isSet : ∀ D p, M.isSet D → M.isSet (sepValue D p)
  unionValue : M.Value → M.Value → M.Value
  union_members : ∀ A B x, M.mem x (unionValue A B) ↔ M.mem x A ∨ M.mem x B
  union_isSet : ∀ A B, M.isSet A → M.isSet B → M.isSet (unionValue A B)
  powerValue : M.Value → M.Value
  power_members : ∀ A B, M.mem B (powerValue A) ↔
    M.isSet B ∧ ∀ x, M.mem x B → M.mem x A
  power_isSet : ∀ A, M.isSet A → M.isSet (powerValue A)
  ext : ∀ A B, M.isSet A → M.isSet B → (∀ x, M.mem x A ↔ M.mem x B) → A = B

noncomputable instance numericSetSemantics : SetSemantics NumericModel.model where
  emptyValue := (∅ : ZFSet.{0})
  empty_members := ZFSet.notMem_empty
  empty_isSet := True.intro
  insertValue := ZFSet.Insert
  insert_members _ _ _ := ZFSet.mem_insert_iff
  insert_isSet _ _ _ _ := True.intro
  sepValue D p := ZFSet.sep p D
  sep_members _ _ _ := ZFSet.mem_sep
  sep_isSet _ _ _ := True.intro
  unionValue := (· ∪ ·)
  union_members _ _ _ := ZFSet.mem_union
  union_isSet _ _ _ _ := True.intro
  powerValue := ZFSet.powerset
  power_members _ _ := by simp only [ZFSet.mem_powerset]; exact ⟨fun h => ⟨True.intro, h⟩, fun h => h.2⟩
  power_isSet _ _ := True.intro
  ext _ _ _ _ := ZFSet.ext

/-- Positivity is a faithful real denotation witness, including its carrier. -/
def positiveRealPredicate {M : Semantics.{u}} (x : M.Value) : Prop :=
  ∃ r : ℝ, x = M.number (r : ℂ) ∧ 0 < r

/-- Positive reals are a bounded separation of the existing real set. -/
def positiveReal {M : Semantics.{u}} [S : SetSemantics M] : M.Value :=
  S.sepValue (M.standard .real) positiveRealPredicate

theorem positiveReal_isSet {M : Semantics.{u}} [S : SetSemantics M] :
    M.isSet (positiveReal (M := M)) :=
  S.sep_isSet _ _ (M.standard_isSet .real)

def RPos {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  semanticObject positiveReal positiveReal_isSet

theorem positiveReal_members {M : Semantics.{u}} [S : SetSemantics M] (x : M.Value) :
    M.mem x positiveReal ↔ M.mem x (M.standard .real) ∧ positiveRealPredicate x :=
  S.sep_members _ _ _

theorem inRPos_iff {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a RPos ↔ In a R ∧ Lt (number 0) a := by
  rw [show In a RPos = M.mem (denote a) positiveReal from rfl, positiveReal_members]
  constructor
  · rintro ⟨ha, r, hr, hpos⟩
    exact ⟨ha, NativeBridge.ltOfDenoteReal (number 0) a 0 r rfl hr hpos⟩
  · rintro ⟨ha, hpos⟩
    obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp ha
    exact ⟨ha, r, hr,
      (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp hpos⟩

theorem inRPos_real {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RPos) :
    In a R := ((inRPos_iff a).mp ha).1

theorem positiveRealToComplex {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RPos) :
    In a C := realToComplex a (inRPos_real a ha)

theorem inRPos_positive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RPos) :
    Lt (number 0) a := ((inRPos_iff a).mp ha).2

theorem inRPos_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a R) (hpos : Lt (number 0) a) : In a RPos :=
  (inRPos_iff a).mpr ⟨ha, hpos⟩

theorem numberInRPos_iff {M : Semantics.{u}} [SetSemantics M] (r : ℝ) :
    In (number (r : ℂ)) (RPos (M := M)) ↔ 0 < r := by
  rw [inRPos_iff]
  have hr : In (number (r : ℂ)) (R (M := M)) :=
    (M.real_members _).mpr ⟨r, rfl⟩
  exact ⟨fun h => (NativeBridge.lt_iff_ofDenoteReal (number 0)
    (number (r : ℂ)) 0 r rfl rfl).mp h.2,
    fun h => ⟨hr, NativeBridge.ltOfDenoteReal (number 0) (number (r : ℂ))
      0 r rfl rfl h⟩⟩

theorem numberInRPos {M : Semantics.{u}} [SetSemantics M] (r : ℝ) (hr : 0 < r) :
    In (number (r : ℂ)) (RPos (M := M)) :=
  (numberInRPos_iff r).mpr hr

namespace NativeBridge

/-- A numeric observer may use a complex expression rather than the real
embedding itself. The explicit equality preserves the original endpoint. -/
theorem numberInRPosOfEq {M : Semantics.{u}} [SetSemantics M]
    (z : ℂ) (r : ℝ) (hz : z = (r : ℂ)) (hr : 0 < r) :
    In (number (M := M) z) RPos :=
  inOfDenoteNumber (number z) (r : ℂ) RPos (congrArg M.number hz) (numberInRPos r hr)

end NativeBridge

theorem rPosNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (RPos (M := M)) := by
  refine ⟨M.number (1 : ℂ), ?_⟩
  have h := numberInRPos (M := M) (1 : ℝ) zero_lt_one
  change M.mem (M.number ((1 : ℝ) : ℂ)) (denote (RPos (M := M))) at h
  simpa only [Complex.ofReal_one] using h

inductive EmptySetObj where
  | empty

instance emptySetRepresentation {M : Semantics.{u}} [S : SetSemantics M] :
    Representation M EmptySetObj where
  wd _ := True
  denote _ := S.emptyValue
  wd_isSet _ := S.empty_isSet

def emptySet {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) EmptySetObj :=
  ⟨.empty, True.intro⟩

/-- Heterogeneous certified children retain enumeration construction shape.
The stricter source WD requires a fresh element, even though set insertion
itself is defined for duplicates. -/
structure InsertObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  element : Obj (M := M) α
  tail : Obj (M := M) β

instance insertRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (InsertObj (M := M) α β) where
  wd s := ¬ In s.element s.tail
  denote s := S.insertValue (denote s.element) (denote s.tail)
  wd_isSet {s} _ := S.insert_isSet _ _ (isSet s.element) (isSet s.tail)

def insert {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (h : ¬ In a A) :
    Obj (M := M) (InsertObj (M := M) α β) := ⟨⟨a, A⟩, h⟩

theorem notInEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    ¬ In a (emptySet (M := M)) := S.empty_members (denote a)

theorem inInsert_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (x : Obj (M := M) α) (a : Obj (M := M) β) (A : Obj (M := M) γ)
    (h : ¬ In a A) : In x (insert a A h) ↔ Same x a ∨ In x A :=
  S.insert_members _ _ _

theorem notInInsert {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (x : Obj (M := M) α) (a : Obj (M := M) β) (A : Obj (M := M) γ)
    (h : ¬ In a A) (hxa : ¬ Same x a) (hxA : ¬ In x A) :
    ¬ In x (insert a A h) :=
  fun hx => ((inInsert_iff x a A h).mp hx).elim hxa hxA

def Subset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop :=
  ∀ x, M.mem x (denote A) → M.mem x (denote B)

theorem subsetRefl {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Subset A A := fun _ hx => hx

theorem subsetOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (C : Obj (M := M) γ) (D : Obj (M := M) δ)
    (hAC : Same A C) (hBD : Same B D) (hAB : Subset A B) : Subset C D := by
  intro z hz
  rw [← hBD]
  apply hAB z
  rw [hAC]
  exact hz

/-- Replay the source subset definition at the semantic-value representation.
The forall proof comes from the recorded definition child, not target search. -/
theorem subsetOfForall {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (h : ∀ {γ : Type u} [Representation M γ], (a : Obj (M := M) γ) → In a A → In a B) :
    Subset A B := fun z hz => h (semanticObject z (M.member_isSet hz)) hz

theorem emptySubset {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Subset (emptySet (M := M)) A := fun x hx => (S.empty_members x hx).elim

theorem insertSubset {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a A) (ha : In a B) (hA : Subset A B) : Subset (insert a A h) B := by
  intro x hx
  rcases (S.insert_members _ _ _).mp hx with hxa | hxA
  · exact hxa ▸ ha
  · exact hA x hxA

theorem setExt {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (hAB : Subset A B) (hBA : Subset B A) :
    Same A B := S.ext _ _ (isSet A) (isSet B) (fun x => ⟨hAB x, hBA x⟩)

/-- Predicate callbacks are well-typed only on certified members of the bound.
A membership proof certifies formation; it is not a mathematical argument. -/
structure SetBuilderObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  bound : Obj (M := M) α
  predicate : (x : Obj (M := M) M.Value) → In x bound → Prop

namespace SetBuilderObj

def condition {M : Semantics.{u}} {α : Type v} [Representation M α]
    (s : SetBuilderObj (M := M) α) (x : M.Value) : Prop :=
  ∃ hx : M.mem x (denote s.bound), s.predicate (semanticObject x (M.member_isSet hx)) hx

end SetBuilderObj

instance setBuilderRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] : Representation M (SetBuilderObj (M := M) α) where
  wd _ := True
  denote s := S.sepValue (denote s.bound) s.condition
  wd_isSet {s} _ := S.sep_isSet _ _ (isSet s.bound)

def setBuilder {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (D : Obj (M := M) α)
    (p : (x : Obj (M := M) M.Value) → In x D → Prop) :
    Obj (M := M) (SetBuilderObj (M := M) α) := ⟨⟨D, p⟩, True.intro⟩

theorem inSetBuilder_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (D : Obj (M := M) β)
    (p : (x : Obj (M := M) M.Value) → In x D → Prop) :
    In a (setBuilder D p) ↔
      ∃ ha : In a D, p (semanticObject (denote a) (M.member_isSet ha)) ha := by
  rw [In, show denote (setBuilder D p) = S.sepValue (denote D)
    (SetBuilderObj.condition ⟨D, p⟩) from rfl, S.sep_members]
  exact ⟨fun h => h.2, fun h => ⟨h.choose, h⟩⟩

theorem setBuilderSubset {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (D : Obj (M := M) α)
    (p : (x : Obj (M := M) M.Value) → In x D → Prop) : Subset (setBuilder D p) D :=
  fun _ hx => ((S.sep_members _ _ _).mp hx).1

namespace NativeSetBridge

/-- A numeric pullback observes only the numeric slice. A full numeric-set view
also needs the corresponding source subset witness, as in the completeness
lemmas below. Arbitrary objects keep their registered host representation. -/
def complexView {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Set ℂ := {z | In (number z) A}

def realView {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Set ℝ := {r | In (number (r : ℂ)) A}

theorem complexView_ofSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Same A B) :
    complexView A = complexView B :=
  Set.ext fun z => ⟨fun hz => Eq.mp (congrArg (M.mem (M.number z)) h) hz,
    fun hz => Eq.mpr (congrArg (M.mem (M.number z)) h) hz⟩

theorem complexView_subset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) :
    complexView A ⊆ complexView B := fun z hz => h (M.number z) hz

theorem realView_subset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) :
    realView A ⊆ realView B := fun r hr => h (M.number (r : ℂ)) hr

theorem complexView_complete {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : Subset A C) (x : M.Value) (hx : M.mem x (denote A)) :
    ∃ z : ℂ, x = M.number z ∧ z ∈ complexView A := by
  obtain ⟨z, hz⟩ := (M.complex_members x).mp (h x hx)
  exact ⟨z, hz, Eq.mp (congrArg (fun y => M.mem y (denote A)) hz) hx⟩

theorem realView_complete {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : Subset A R) (x : M.Value) (hx : M.mem x (denote A)) :
    ∃ r : ℝ, x = M.number (r : ℂ) ∧ r ∈ realView A := by
  obtain ⟨r, hr⟩ := (M.real_members x).mp (h x hx)
  exact ⟨r, hr, Eq.mp (congrArg (fun y => M.mem y (denote A)) hr) hx⟩

theorem complexView_empty {M : Semantics.{u}} [SetSemantics M] :
    complexView (emptySet (M := M)) = ∅ :=
  Set.ext fun z => ⟨fun hz => (notInEmpty (number z) hz).elim, fun h => h.elim⟩

theorem complexView_insert {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (z : ℂ) (A : Obj (M := M) α)
    (h : ¬ In (number z) A) : complexView (insert (number z) A h) =
      Insert.insert z (complexView A) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases (inInsert_iff (number x) (number z) A h).mp hx with eq | mem
    · exact Or.inl (M.number_injective eq)
    · exact Or.inr mem
  · intro hx
    rcases hx with eq | mem
    · exact (inInsert_iff (number x) (number z) A h).mpr (Or.inl (congrArg M.number eq))
    · exact (inInsert_iff (number x) (number z) A h).mpr (Or.inr mem)

end NativeSetBridge

/-- A graph has exactly its declared domain and one codomain value per input. -/
def IsFunctionGraph {M : Semantics.{u}} (pair : M.Value → M.Value → M.Value)
    (D B f : M.Value) : Prop :=
  (∀ p, M.mem p f → ∃ x, M.mem x D ∧ ∃ y, M.mem y B ∧ p = pair x y) ∧
    ∀ x, M.mem x D → ∃! y, M.mem (pair x y) f

/-- Additional set/function structure; the existing numeric model is not copied. -/
class FunctionSemantics (M : Semantics.{u}) extends SetSemantics M where
  pairValue : M.Value → M.Value → M.Value
  pair_injective : Function.Injective2 pairValue
  productValue : M.Value → M.Value → M.Value
  product_members : ∀ D E p,
    M.mem p (productValue D E) ↔ ∃ x, M.mem x D ∧ ∃ y, M.mem y E ∧ p = pairValue x y
  product_isSet : ∀ D E, M.isSet D → M.isSet E → M.isSet (productValue D E)
  fnSetValue : M.Value → M.Value → M.Value
  fnSet_members : ∀ D B f, M.mem f (fnSetValue D B) ↔ IsFunctionGraph pairValue D B f
  fnSet_isSet : ∀ D B, M.isSet D → M.isSet B → M.isSet (fnSetValue D B)
  graphValue : M.Value → M.Value → (M.Value → M.Value) → M.Value
  graph_members : ∀ D B body p,
    M.mem p (graphValue D B body) ↔
      ∃ x, M.mem x D ∧ ∃ y, M.mem y B ∧ p = pairValue x y ∧ y = body x
  callValue : M.Value → M.Value → M.Value
  call_graph : ∀ D B f x, IsFunctionGraph pairValue D B f → M.mem x D →
    M.mem (pairValue x (callValue f x)) f
  graph_ext : ∀ D B f g, IsFunctionGraph pairValue D B f →
    IsFunctionGraph pairValue D B g →
    (∀ x y, M.mem (pairValue x y) f ↔ M.mem (pairValue x y) g) → f = g

namespace FunctionSemantics

variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem pair_mem_graph (D B : M.Value) (body : M.Value → M.Value) (x y : M.Value) :
    M.mem (F.pairValue x y) (F.graphValue D B body) ↔
      M.mem x D ∧ M.mem y B ∧ y = body x := by
  rw [F.graph_members]
  constructor
  · rintro ⟨a, ha, b, hb, hp, hbody⟩
    obtain ⟨rfl, rfl⟩ := F.pair_injective hp
    exact ⟨ha, hb, hbody⟩
  · rintro ⟨hx, hy, hbody⟩
    exact ⟨x, hx, y, hy, rfl, hbody⟩

theorem graph_isFunction (D B : M.Value) (body : M.Value → M.Value)
    (hbody : ∀ x, M.mem x D → M.mem (body x) B) :
    IsFunctionGraph F.pairValue D B (F.graphValue D B body) := by
  constructor
  · intro p hp
    obtain ⟨x, hx, y, hy, hpair, _⟩ := (F.graph_members D B body p).mp hp
    exact ⟨x, hx, y, hy, hpair⟩
  · intro x hx
    refine ⟨body x, (pair_mem_graph D B body x (body x)).mpr ⟨hx, hbody x hx, rfl⟩, ?_⟩
    intro y hy
    exact ((pair_mem_graph D B body x y).mp hy).2.2

theorem graph_inFnSet (D B : M.Value) (body : M.Value → M.Value)
    (hbody : ∀ x, M.mem x D → M.mem (body x) B) :
    M.mem (F.graphValue D B body) (F.fnSetValue D B) :=
  (F.fnSet_members D B _).mpr (graph_isFunction D B body hbody)

theorem call_mem (D B f x : M.Value) (hf : M.mem f (F.fnSetValue D B))
    (hx : M.mem x D) : M.mem (F.callValue f x) B := by
  have hgraph := (F.fnSet_members D B f).mp hf
  obtain ⟨a, _, b, hb, hp⟩ := hgraph.1 _ (F.call_graph D B f x hgraph hx)
  obtain ⟨_, hresult⟩ := F.pair_injective hp
  exact hresult ▸ hb

theorem call_graphValue (D B : M.Value) (body : M.Value → M.Value)
    (hbody : ∀ x, M.mem x D → M.mem (body x) B) (x : M.Value) (hx : M.mem x D) :
    F.callValue (F.graphValue D B body) x = body x := by
  have hpoint := F.call_graph D B _ x (graph_isFunction D B body hbody) hx
  exact ((pair_mem_graph D B body x _).mp hpoint).2.2

end FunctionSemantics

namespace NumericFunctionModel

noncomputable def graph (D B : ZFSet.{0}) (body : ZFSet.{0} → ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pairSep (fun x y => y = body x) D B

noncomputable def call (f x : ZFSet.{0}) : ZFSet.{0} := by
  classical
  exact if h : ∃! y, ZFSet.pair x y ∈ f then Classical.choose h.exists
    else NumericModel.codeComplex 0

theorem call_graph (D B f x : ZFSet.{0}) (hf : ZFSet.IsFunc D B f) (hx : x ∈ D) :
    ZFSet.pair x (call f x) ∈ f := by
  classical
  have h := hf.2 x hx
  unfold call
  rw [dif_pos h]
  exact Classical.choose_spec h.exists

theorem function_iff (D B f : ZFSet.{0}) :
    IsFunctionGraph ZFSet.pair (M := NumericModel.model) D B f ↔ ZFSet.IsFunc D B f := by
  constructor
  · intro h
    exact ⟨fun p hp => (ZFSet.mem_prod).mpr (h.1 p hp), h.2⟩
  · intro h
    exact ⟨fun p hp => (ZFSet.mem_prod).mp (h.1 hp), h.2⟩

theorem function_ext (D B f g : ZFSet.{0}) (hf : ZFSet.IsFunc D B f)
    (hg : ZFSet.IsFunc D B g)
    (h : ∀ x y, ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ g) : f = g := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    exact (h x y).mp hp
  · intro hp
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.mp (hg.1 hp)
    exact (h x y).mpr hp

noncomputable instance numericFunctionSemantics : FunctionSemantics NumericModel.model where
  toSetSemantics := numericSetSemantics
  pairValue := ZFSet.pair
  pair_injective := ZFSet.pair_injective
  productValue := ZFSet.prod
  product_members _ _ _ := ZFSet.mem_prod
  product_isSet _ _ _ _ := True.intro
  fnSetValue := ZFSet.funs
  fnSet_members D B f := ZFSet.mem_funs.trans (function_iff D B f).symm
  fnSet_isSet _ _ _ _ := True.intro
  graphValue := graph
  graph_members _ _ _ _ := ZFSet.mem_pairSep
  callValue := call
  call_graph D B f x hf hx := call_graph D B f x ((function_iff D B f).mp hf) hx
  graph_ext D B f g hf hg h := function_ext D B f g
    ((function_iff D B f).mp hf) ((function_iff D B g).mp hg) h

end NumericFunctionModel


namespace FunctionSemantics

variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Decoding is only used internally to interpret a two-parameter formula graph. -/
noncomputable def unpairValue (p : M.Value) : M.Value × M.Value := by
  classical
  exact if h : ∃ v : M.Value × M.Value, p = F.pairValue v.1 v.2 then
    Classical.choose h else (M.number 0, M.number 0)

theorem unpair_pair (a b : M.Value) :
    unpairValue (F.pairValue a b) = (a, b) := by
  classical
  have h : ∃ v : M.Value × M.Value, F.pairValue a b = F.pairValue v.1 v.2 :=
    ⟨(a, b), rfl⟩
  unfold unpairValue
  rw [dif_pos h]
  obtain ⟨ha, hb⟩ := F.pair_injective (Classical.choose_spec h)
  exact Prod.ext ha.symm hb.symm

end FunctionSemantics

inductive NumericInputDomain where
  | one (input : StandardSetValue)
  | two (first second : StandardSetValue)

/-- Inputs retain the supported numeric domains. A codomain is a certified
semantic set, so derived sets keep their exact membership contract. -/
structure FunctionSignature (M : Semantics.{u}) where
  inputs : NumericInputDomain
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → Prop

namespace FunctionSignature

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def oneTarget (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) : FunctionSignature M :=
  ⟨.one A, B, hB, guard⟩

noncomputable def twoTarget (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) : FunctionSignature M :=
  ⟨.two A E, B, hB, fun p => guard (FunctionSemantics.unpairValue p).1
    (FunctionSemantics.unpairValue p).2⟩

def one (A B : StandardSetValue) (guard : M.Value → Prop) : FunctionSignature M :=
  oneTarget A (M.standard B) (M.standard_isSet B) guard

noncomputable def two (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop) :
    FunctionSignature M :=
  twoTarget A E (M.standard B) (M.standard_isSet B) guard

def baseDomain (s : FunctionSignature M) : M.Value :=
  match s.inputs with
  | .one A => M.standard A
  | .two A E => F.productValue (M.standard A) (M.standard E)

def domain (s : FunctionSignature M) : M.Value := F.sepValue s.baseDomain s.guard

def target (s : FunctionSignature M) : M.Value := s.output

theorem domain_isSet (s : FunctionSignature M) : M.isSet s.domain := by
  apply F.sep_isSet
  cases s with
  | mk inputs output output_isSet guard =>
    cases inputs with
    | one A => exact M.standard_isSet A
    | two A E => exact F.product_isSet _ _ (M.standard_isSet A) (M.standard_isSet E)

theorem oneTarget_domain (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (oneTarget A B hB guard).domain ↔ M.mem x (M.standard A) ∧ guard x :=
  F.sep_members _ _ _

theorem twoTarget_domain (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop)
    (a b : M.Value) :
    M.mem (F.pairValue a b) (twoTarget A E B hB guard).domain ↔
      M.mem a (M.standard A) ∧ M.mem b (M.standard E) ∧ guard a b := by
  change M.mem (F.pairValue a b)
    (F.sepValue (F.productValue (M.standard A) (M.standard E)) _) ↔ _
  rw [F.sep_members]
  simp only [twoTarget, FunctionSemantics.unpair_pair]
  constructor
  · rintro ⟨h, hg⟩
    obtain ⟨x, hx, y, hy, hp⟩ := (F.product_members _ _ _).mp h
    obtain ⟨rfl, rfl⟩ := F.pair_injective hp
    exact ⟨hx, hy, hg⟩
  · rintro ⟨ha, hb, hg⟩
    exact ⟨(F.product_members _ _ _).mpr ⟨a, ha, b, hb, rfl⟩, hg⟩

theorem one_domain (A B : StandardSetValue) (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (one A B guard).domain ↔ M.mem x (M.standard A) ∧ guard x :=
  oneTarget_domain A (M.standard B) (M.standard_isSet B) guard x

theorem two_domain (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (a b : M.Value) :
    M.mem (F.pairValue a b) (two A E B guard).domain ↔
      M.mem a (M.standard A) ∧ M.mem b (M.standard E) ∧ guard a b :=
  twoTarget_domain A E (M.standard B) (M.standard_isSet B) guard a b

end FunctionSignature

instance functionSignatureRepresentation {M : Semantics.{u}} [F : FunctionSemantics M] :
    Representation M (FunctionSignature M) where
  wd _ := True
  denote s := F.fnSetValue s.domain s.target
  wd_isSet {s} _ := F.fnSet_isSet _ _ s.domain_isSet s.output_isSet

def fnSet {M : Semantics.{u}} [FunctionSemantics M] (s : FunctionSignature M) :
    Obj (M := M) (FunctionSignature M) := ⟨s, True.intro⟩

/-- A formula object denotes a set-theoretic graph, not its interpretation callback.
The callback is the compiler's recursive interpretation of the source body AST. -/
structure FormulaFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  bodyValue : M.Value → M.Value

instance formulaFnRepresentation {M : Semantics.{u}} [F : FunctionSemantics M] :
    Representation M (FormulaFn M) where
  wd f := ∀ x, M.mem x f.signature.domain → M.mem (f.bodyValue x) f.signature.target
  denote f := F.graphValue f.signature.domain f.signature.target f.bodyValue
  wd_isSet h := M.member_isSet
    (FunctionSemantics.graph_inFnSet _ _ _ h)

def formulaFnTarget {M : Semantics.{u}} [FunctionSemantics M]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) B) :
    Obj (M := M) (FormulaFn M) :=
  ⟨⟨FunctionSignature.oneTarget A B hB guard, body⟩, fun x hx =>
    hReturn x ((FunctionSignature.oneTarget_domain A B hB guard x).mp hx).1
      ((FunctionSignature.oneTarget_domain A B hB guard x).mp hx).2⟩

noncomputable def formulaFn2Target {M : Semantics.{u}} [F : FunctionSemantics M]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) B) : Obj (M := M) (FormulaFn M) := by
  let s := FunctionSignature.twoTarget A E B hB guard
  let interpretation := fun p => body (FunctionSemantics.unpairValue p).1
    (FunctionSemantics.unpairValue p).2
  refine ⟨⟨s, interpretation⟩, ?_⟩
  intro p hp
  obtain ⟨hproduct, hg⟩ := (F.sep_members s.baseDomain s.guard p).mp hp
  obtain ⟨x, hx, y, hy, rfl⟩ := (F.product_members _ _ _).mp hproduct
  change M.mem (body _ _) B
  simpa only [FunctionSemantics.unpair_pair] using hReturn x y hx hy
    (by simpa only [s, FunctionSignature.twoTarget, FunctionSemantics.unpair_pair] using hg)

def formulaFn {M : Semantics.{u}} [FunctionSemantics M]
    (A B : StandardSetValue) (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) (M.standard B)) :
    Obj (M := M) (FormulaFn M) :=
  formulaFnTarget A (M.standard B) (M.standard_isSet B) guard body hReturn

noncomputable def formulaFn2 {M : Semantics.{u}} [FunctionSemantics M]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) (M.standard B)) : Obj (M := M) (FormulaFn M) :=
  formulaFn2Target A E (M.standard B) (M.standard_isSet B) guard body hReturn

theorem formulaFnInFnSet {M : Semantics.{u}} [FunctionSemantics M]
    (f : Obj (M := M) (FormulaFn M)) : In f (fnSet f.val.signature) :=
  FunctionSemantics.graph_inFnSet _ _ _ f.wd

structure CallObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  input : StandardSetValue
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → Prop
  function : Obj (M := M) α
  argument : Obj (M := M) β

instance callRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CallObj (M := M) α β) where
  wd c := In c.function
    (fnSet (FunctionSignature.oneTarget c.input c.output c.output_isSet c.guard)) ∧
    M.mem (denote c.argument) (M.standard c.input) ∧ c.guard (denote c.argument)
  denote c := F.callValue (denote c.function) (denote c.argument)
  wd_isSet {c} h := M.member_isSet (FunctionSemantics.call_mem _ _ _ _ h.1
    ((FunctionSignature.oneTarget_domain c.input c.output c.output_isSet c.guard _).mpr h.2))

def callTarget {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B) (guard : M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet (FunctionSignature.oneTarget A B hB guard)))
    (ha : In a (standardSet A)) (hg : guard (denote a)) :
    Obj (M := M) (CallObj (M := M) α β) := ⟨⟨A, B, hB, guard, f, a⟩, hf, ha, hg⟩

def call {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A B : StandardSetValue) (guard : M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet (FunctionSignature.one A B guard)))
    (ha : In a (standardSet A)) (hg : guard (denote a)) :
    Obj (M := M) (CallObj (M := M) α β) :=
  callTarget A (M.standard B) (M.standard_isSet B) guard f a hf ha hg

structure CallObj2 {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type t)
    [Representation M α] [Representation M β] [Representation M γ] where
  firstInput : StandardSetValue
  secondInput : StandardSetValue
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → M.Value → Prop
  function : Obj (M := M) α
  first : Obj (M := M) β
  second : Obj (M := M) γ

noncomputable instance call2Representation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (CallObj2 (M := M) α β γ) where
  wd c := In c.function (fnSet (FunctionSignature.twoTarget c.firstInput c.secondInput
    c.output c.output_isSet c.guard)) ∧ M.mem (denote c.first) (M.standard c.firstInput) ∧
    M.mem (denote c.second) (M.standard c.secondInput) ∧ c.guard (denote c.first) (denote c.second)
  denote c := F.callValue (denote c.function) (F.pairValue (denote c.first) (denote c.second))
  wd_isSet {c} h := M.member_isSet (FunctionSemantics.call_mem _ _ _ _ h.1
    ((FunctionSignature.twoTarget_domain c.firstInput c.secondInput c.output
      c.output_isSet c.guard _ _).mpr h.2))

noncomputable def call2Target {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β) (b : Obj (M := M) γ)
    (hf : In f (fnSet (FunctionSignature.twoTarget A E B hB guard)))
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    Obj (M := M) (CallObj2 (M := M) α β γ) :=
  ⟨⟨A, E, B, hB, guard, f, a, b⟩, hf, ha, hb, hg⟩

noncomputable def call2 {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β) (b : Obj (M := M) γ)
    (hf : In f (fnSet (FunctionSignature.two A E B guard)))
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    Obj (M := M) (CallObj2 (M := M) α β γ) :=
  call2Target A E (M.standard B) (M.standard_isSet B) guard f a b hf ha hb hg


section FunctionObjects

variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- These laws consume the WD proofs stored in the call object. -/
theorem callInOutput {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallObj (M := M) α β)) :
    In c (semanticObject c.val.output c.val.output_isSet) :=
  FunctionSemantics.call_mem _ _ _ _ c.wd.1
    ((FunctionSignature.oneTarget_domain c.val.input c.val.output
      c.val.output_isSet c.val.guard _).mpr c.wd.2)

theorem call2InOutput {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (c : Obj (M := M) (CallObj2 (M := M) α β γ)) :
    In c (semanticObject c.val.output c.val.output_isSet) :=
  FunctionSemantics.call_mem _ _ _ _ c.wd.1
    ((FunctionSignature.twoTarget_domain c.val.firstInput c.val.secondInput c.val.output
      c.val.output_isSet c.val.guard _ _).mpr c.wd.2)

omit F in
theorem functionObject_proofIndependent {α : Type v} [Representation M α]
    (a : α) (h₁ h₂ : WD (M := M) a) :
    denote (⟨a, h₁⟩ : Obj (M := M) α) = denote (⟨a, h₂⟩ : Obj (M := M) α) := rfl

theorem callCongr {α : Type v} {β : Type w} {γ : Type t} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (c : Obj (M := M) (CallObj (M := M) α β))
    (d : Obj (M := M) (CallObj (M := M) γ δ))
    (hf : Same c.val.function d.val.function) (ha : Same c.val.argument d.val.argument) :
    Same c d := congrArg₂ F.callValue hf ha

theorem call2Congr {α : Type v} {β : Type w} {γ : Type t}
    {δ : Type*} {ε : Type*} {ζ : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε] [Representation M ζ]
    (c : Obj (M := M) (CallObj2 (M := M) α β γ))
    (d : Obj (M := M) (CallObj2 (M := M) δ ε ζ))
    (hf : Same c.val.function d.val.function)
    (ha : Same c.val.first d.val.first) (hb : Same c.val.second d.val.second) :
    Same c d := congrArg₂ F.callValue hf (congrArg₂ F.pairValue ha hb)

theorem callFormulaTarget_denote {α : Type v} [Representation M α]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) B)
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a)) :
    denote (callTarget A B hB guard (formulaFnTarget A B hB guard body hReturn) a
      (formulaFnInFnSet _) ha hg) = body (denote a) :=
  FunctionSemantics.call_graphValue _ _ _ (formulaFnTarget A B hB guard body hReturn).wd _
    ((FunctionSignature.oneTarget_domain A B hB guard _).mpr ⟨ha, hg⟩)

theorem callFormulaTarget_same {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) B)
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a))
    (b : Obj (M := M) β) (hBody : body (denote a) = denote b) :
    Same (callTarget A B hB guard (formulaFnTarget A B hB guard body hReturn) a
      (formulaFnInFnSet _) ha hg) b :=
  (callFormulaTarget_denote A B hB guard body hReturn a ha hg).trans hBody

theorem callFormula2Target_denote {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) B)
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    denote (call2Target A E B hB guard (formulaFn2Target A E B hB guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) = body (denote a) (denote b) := by
  have h := FunctionSemantics.call_graphValue _ _ _
    (formulaFn2Target A E B hB guard body hReturn).wd
    (F.pairValue (denote a) (denote b))
    ((FunctionSignature.twoTarget_domain A E B hB guard _ _).mpr ⟨ha, hb, hg⟩)
  change F.callValue (F.graphValue (FunctionSignature.twoTarget A E B hB guard).domain
    (FunctionSignature.twoTarget A E B hB guard).target (fun p => body
      (FunctionSemantics.unpairValue p).1 (FunctionSemantics.unpairValue p).2))
    (F.pairValue (denote a) (denote b)) = body (denote a) (denote b)
  simpa only [formulaFn2Target, FunctionSemantics.unpair_pair] using h

theorem callFormula2Target_same {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) B)
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b))
    (c : Obj (M := M) γ) (hBody : body (denote a) (denote b) = denote c) :
    Same (call2Target A E B hB guard (formulaFn2Target A E B hB guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) c :=
  (callFormula2Target_denote A E B hB guard body hReturn a b ha hb hg).trans hBody

theorem callFormula_denote {α : Type v} [Representation M α]
    (A B : StandardSetValue) (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) (M.standard B))
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a)) :
    denote (call A B guard (formulaFn A B guard body hReturn) a
      (formulaFnInFnSet _) ha hg) = body (denote a) :=
  FunctionSemantics.call_graphValue _ _ _ (formulaFn A B guard body hReturn).wd _
    ((FunctionSignature.one_domain A B guard _).mpr ⟨ha, hg⟩)

/-- The source body's owned object supplies the correspondence to its template. -/
theorem callFormula_same {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A B : StandardSetValue) (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) (M.standard B))
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a))
    (b : Obj (M := M) β) (hBody : body (denote a) = denote b) :
    Same (call A B guard (formulaFn A B guard body hReturn) a
      (formulaFnInFnSet _) ha hg) b :=
  (callFormula_denote A B guard body hReturn a ha hg).trans hBody

theorem callFormula2_denote {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) (M.standard B))
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    denote (call2 A E B guard (formulaFn2 A E B guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) = body (denote a) (denote b) := by
  have h := FunctionSemantics.call_graphValue _ _ _ (formulaFn2 A E B guard body hReturn).wd
    (F.pairValue (denote a) (denote b))
    ((FunctionSignature.two_domain A E B guard _ _).mpr ⟨ha, hb, hg⟩)
  change F.callValue (F.graphValue (FunctionSignature.two A E B guard).domain
    (FunctionSignature.two A E B guard).target (fun p => body (FunctionSemantics.unpairValue p).1
      (FunctionSemantics.unpairValue p).2))
    (F.pairValue (denote a) (denote b)) = body (denote a) (denote b)
  simpa only [formulaFn2, formulaFn2Target, FunctionSignature.two,
    FunctionSemantics.unpair_pair] using h

theorem callFormula2_same {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) (M.standard B))
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b))
    (c : Obj (M := M) γ) (hBody : body (denote a) (denote b) = denote c) :
    Same (call2 A E B guard (formulaFn2 A E B guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) c :=
  (callFormula2_denote A E B guard body hReturn a b ha hb hg).trans hBody

end FunctionObjects

end Litex

namespace Litex

/-- An owned recursive declaration keeps both its source step interpretation
and the exact restricted guard used for recursive self calls. Its denotation
is a function graph; natural recursion is internal to that interpretation. -/
structure RecursiveNatFn (M : Semantics.{u}) where
  output : M.Value
  output_isSet : M.isSet output
  restrictedGuard : ℕ → M.Value → Prop
  baseValue : M.Value
  stepValue : ℕ → M.Value → M.Value

namespace RecursiveNatFn

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def signature (r : RecursiveNatFn M) : FunctionSignature M :=
  FunctionSignature.oneTarget .natural r.output r.output_isSet (fun _ => True)

def prefixSignature (r : RecursiveNatFn M) (n : ℕ) : FunctionSignature M :=
  FunctionSignature.oneTarget .natural r.output r.output_isSet (r.restrictedGuard n)

noncomputable def prefixGraph (r : RecursiveNatFn M) (n : ℕ) (values : ℕ → M.Value) :
    M.Value := F.graphValue (r.prefixSignature n).domain r.output
      (fun x => values (NativeBridge.naturalValue x))

/-- Every stage preserves its completed values. Values outside that stage are
extended with the certified base value, without exposing a native function as
an exported source object. -/
noncomputable def history (r : RecursiveNatFn M) : ℕ → ℕ → M.Value
  | 0 => fun _ => r.baseValue
  | n + 1 => fun k => if k = n + 1 then
      r.stepValue (n + 1) (r.prefixGraph (n + 1) (r.history n)) else r.history n k

noncomputable def value (r : RecursiveNatFn M) (n : ℕ) : M.Value := r.history n n

noncomputable def graph (r : RecursiveNatFn M) : M.Value :=
  F.graphValue r.signature.domain r.output (fun x => r.value (NativeBridge.naturalValue x))

/-- Each obligation is supplied by replaying the source declaration's retained
case guards, body WD, return proof, and recursive-call requirements. -/
structure Certified (r : RecursiveNatFn M) : Prop where
  guardSound : ∀ n x, M.mem x (M.standard .natural) → r.restrictedGuard n x →
    NativeBridge.naturalValue x < n
  baseReturn : M.mem r.baseValue r.output
  stepReturn : ∀ n prefixFn,
    M.mem prefixFn (F.fnSetValue (r.prefixSignature (n + 1)).domain r.output) →
      M.mem (r.stepValue (n + 1) prefixFn) r.output
  stepCongr : ∀ n f g,
    (∀ x, M.mem x (M.standard .natural) → r.restrictedGuard (n + 1) x →
      F.callValue f x = F.callValue g x) →
        r.stepValue (n + 1) f = r.stepValue (n + 1) g

theorem prefixGraph_mem (r : RecursiveNatFn M) (n : ℕ) (values : ℕ → M.Value)
    (hvalues : ∀ k, M.mem (values k) r.output) :
    M.mem (r.prefixGraph n values) (F.fnSetValue (r.prefixSignature n).domain r.output) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun x _ => hvalues (NativeBridge.naturalValue x))

theorem history_mem (r : RecursiveNatFn M) (h : r.Certified) (n k : ℕ) :
    M.mem (r.history n k) r.output := by
  induction n generalizing k with
  | zero => exact h.baseReturn
  | succ n ih =>
    change M.mem (if k = n + 1 then
      r.stepValue (n + 1) (r.prefixGraph (n + 1) (r.history n)) else r.history n k) r.output
    split
    · exact h.stepReturn n _ (r.prefixGraph_mem _ _ ih)
    · exact ih k

theorem history_completed (r : RecursiveNatFn M) (n k : ℕ) (hk : k ≤ n) :
    r.history n k = r.value k := by
  induction n with
  | zero =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    rfl
  | succ n ih =>
    by_cases he : k = n + 1
    · subst k
      rfl
    · have hkn : k ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hk he)
      change (if k = n + 1 then _ else r.history n k) = _
      rw [if_neg he]
      exact ih hkn

theorem graph_return (r : RecursiveNatFn M) (h : r.Certified) :
    ∀ x, M.mem x r.signature.domain →
      M.mem (r.value (NativeBridge.naturalValue x)) r.output :=
  fun _ _ => r.history_mem h _ _

theorem graph_mem (r : RecursiveNatFn M) (h : r.Certified) :
    M.mem r.graph (F.fnSetValue r.signature.domain r.output) :=
  FunctionSemantics.graph_inFnSet _ _ _ (r.graph_return h)

theorem call_graph (r : RecursiveNatFn M) (h : r.Certified)
    (x : M.Value) (hx : M.mem x (M.standard .natural)) :
    F.callValue r.graph x = r.value (NativeBridge.naturalValue x) :=
  FunctionSemantics.call_graphValue _ _ _ (r.graph_return h) x
    ((FunctionSignature.oneTarget_domain .natural r.output r.output_isSet
      (fun _ => True) x).mpr ⟨hx, True.intro⟩)

theorem prefix_call_agrees (r : RecursiveNatFn M) (h : r.Certified) (n : ℕ)
    (x : M.Value) (hx : M.mem x (M.standard .natural))
    (hg : r.restrictedGuard (n + 1) x) :
    F.callValue (r.prefixGraph (n + 1) (r.history n)) x = F.callValue r.graph x := by
  have hp := FunctionSemantics.call_graphValue (r.prefixSignature (n + 1)).domain
    r.output (fun x => r.history n (NativeBridge.naturalValue x))
    (fun x _ => r.history_mem h n (NativeBridge.naturalValue x)) x
    ((FunctionSignature.oneTarget_domain .natural r.output r.output_isSet
      (r.restrictedGuard (n + 1)) x).mpr ⟨hx, hg⟩)
  exact hp.trans ((r.history_completed n _ (Nat.le_of_lt_succ (h.guardSound _ _ hx hg))).trans
    (r.call_graph h x hx).symm)

theorem value_zero (r : RecursiveNatFn M) : r.value 0 = r.baseValue := rfl

theorem value_succ (r : RecursiveNatFn M) (h : r.Certified) (n : ℕ) :
    r.value (n + 1) = r.stepValue (n + 1) r.graph := by
  change (if n + 1 = n + 1 then _ else _) = _
  rw [if_pos rfl]
  exact h.stepCongr n _ _ (fun x hx hg => r.prefix_call_agrees h n x hx hg)

end RecursiveNatFn

noncomputable instance recursiveNatFnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] : Representation M (RecursiveNatFn M) where
  wd r := r.Certified
  denote r := r.graph
  wd_isSet {r} h := M.member_isSet (r.graph_mem h)

noncomputable def recursiveNatFnTarget {M : Semantics.{u}} [F : FunctionSemantics M]
    (B : M.Value) (hB : M.isSet B) (guard : ℕ → M.Value → Prop)
    (base : M.Value) (step : ℕ → M.Value → M.Value)
    (hGuard : ∀ n x, M.mem x (M.standard .natural) → guard n x →
      NativeBridge.naturalValue x < n)
    (hBase : M.mem base B)
    (hStep : ∀ n prefixFn,
      M.mem prefixFn (F.fnSetValue (FunctionSignature.oneTarget .natural B hB
        (guard (n + 1))).domain B) → M.mem (step (n + 1) prefixFn) B)
    (hCongr : ∀ n f g,
      (∀ x, M.mem x (M.standard .natural) → guard (n + 1) x →
        F.callValue f x = F.callValue g x) → step (n + 1) f = step (n + 1) g) :
    Obj (M := M) (RecursiveNatFn M) :=
  ⟨⟨B, hB, guard, base, step⟩, ⟨hGuard, hBase, hStep, hCongr⟩⟩

theorem recursiveNatFnInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveNatFn M)) : In f (fnSet f.val.signature) :=
  f.val.graph_mem f.wd

theorem recursiveNatFn_zero {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveNatFn M)) :
    F.callValue (denote f) (M.number 0) = f.val.baseValue := by
  have hx : M.mem (M.number 0) (M.standard .natural) :=
    (M.natural_members _).mpr ⟨0, by simp only [Nat.cast_zero]⟩
  have h := f.val.call_graph f.wd (M.number 0) hx
  have hn : NativeBridge.naturalValue (M.number 0) = 0 := by
    simpa only [Nat.cast_zero] using NativeBridge.naturalValue_number (M := M) 0
  change F.callValue (denote f) (M.number 0) = f.val.value _ at h
  simpa only [hn, RecursiveNatFn.value_zero] using h

theorem recursiveNatFn_succ {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveNatFn M)) (n : ℕ) :
    F.callValue (denote f) (M.number ((n + 1 : ℕ) : ℂ)) =
      f.val.stepValue (n + 1) (denote f) := by
  have hx : M.mem (M.number ((n + 1 : ℕ) : ℂ)) (M.standard .natural) :=
    (M.natural_members _).mpr ⟨n + 1, rfl⟩
  exact (f.val.call_graph f.wd _ hx).trans
    (by rw [NativeBridge.naturalValue_number]; exact f.val.value_succ f.wd n)

theorem callRecursiveNat_denote {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (f : Obj (M := M) (RecursiveNatFn M)) (a : Obj (M := M) α) (ha : In a N) :
    denote (callTarget .natural f.val.output f.val.output_isSet (fun _ => True)
      f a (recursiveNatFnInFnSet f) ha True.intro) =
      f.val.value (NativeBridge.asNat a ha) :=
  f.val.call_graph f.wd (denote a) ha

end Litex

namespace Litex.NativeBridge

variable {M : Semantics.{u}}

theorem realWitnessOfNonnegative {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : Le (number 0) a) :
    ∃ r : ℝ, denote a = M.number (r : ℂ) ∧ 0 ≤ r := by
  obtain ⟨r₀, r, hz, hr, hle⟩ := h
  change M.number 0 = M.number (r₀ : ℂ) at hz
  have h0 : r₀ = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  exact ⟨r, hr, h0 ▸ hle⟩

theorem realWitnessOfPositive {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : Lt (number 0) a) :
    ∃ r : ℝ, denote a = M.number (r : ℂ) ∧ 0 < r := by
  obtain ⟨r₀, r, hz, hr, hlt⟩ := h
  change M.number 0 = M.number (r₀ : ℂ) at hz
  have h0 : r₀ = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  exact ⟨r, hr, h0 ▸ hlt⟩

end Litex.NativeBridge

namespace Litex

theorem addNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Le (number 0) a) (hb : Le (number 0) b) : Le (number 0) (add a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfNonnegative a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfNonnegative b hb
  refine NativeBridge.leOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_nonneg hposR hposS)
  change M.addValue (denote a) (denote b) = _
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

theorem addPositiveRight {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Le (number 0) a) (hb : Lt (number 0) b) : Lt (number 0) (add a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfNonnegative a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfPositive b hb
  refine NativeBridge.ltOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_pos_of_nonneg_of_pos hposR hposS)
  change M.addValue (denote a) (denote b) = _
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

theorem mulNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Le (number 0) a) (hb : Le (number 0) b) : Le (number 0) (mul a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfNonnegative a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfNonnegative b hb
  refine NativeBridge.leOfDenoteReal (number 0) (mul a b haC hbC) 0 (r * s)
    rfl ?_ (mul_nonneg hposR hposS)
  change M.mulValue (denote a) (denote b) = _
  rw [hr, hs, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLeLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorNonnegative : Le (number 0) lhs.val.left)
    (hOperandsLe : Le lhs.val.right rhs.val.right)
    (hFactorSame : Same lhs.val.left rhs.val.left) : Le lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfNonnegative lhs.val.left hFactorNonnegative
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLe
  refine NativeBridge.leOfDenoteReal lhs rhs (c * a) (c * b) ?_ ?_ (mul_le_mul_of_nonneg_left hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hFactorSame.symm.trans hc, hb, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLeRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorNonnegative : Le (number 0) lhs.val.right)
    (hOperandsLe : Le lhs.val.left rhs.val.left)
    (hFactorSame : Same lhs.val.right rhs.val.right) : Le lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfNonnegative lhs.val.right hFactorNonnegative
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLe
  refine NativeBridge.leOfDenoteReal lhs rhs (a * c) (b * c) ?_ ?_ (mul_le_mul_of_nonneg_right hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [ha, hc, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hb, hFactorSame.symm.trans hc, M.mul_numbers, Complex.ofReal_mul]

theorem divStructuralLe {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (DivObj (M := M) α β))
    (rhs : Obj (M := M) (DivObj (M := M) γ δ))
    (hDivisorPos : Lt (number 0) lhs.val.right)
    (hNumeratorsLe : Le lhs.val.left rhs.val.left)
    (hDivisorSame : Same lhs.val.right rhs.val.right) : Le lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive lhs.val.right hDivisorPos
  obtain ⟨a, b, ha, hb, hab⟩ := hNumeratorsLe
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal lhs rhs (a / c) (b / c) ?_ ?_ (div_le_div_of_nonneg_right hab (le_of_lt hc0))
  · change M.divValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [ha, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]
  · change M.divValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hb, hDivisorSame.symm.trans hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]

theorem subNonnegativeToLe {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (haR : In p.val.left R) (hbR : In p.val.right R)
    (h : Le (number 0) p) : Le p.val.right p.val.left := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  have hp : denote p = M.number ((a - b : ℝ) : ℂ) := by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hb, M.sub_numbers, Complex.ofReal_sub]
  exact NativeBridge.leOfDenoteReal _ _ b a hb ha
    (sub_nonneg.mp ((NativeBridge.le_iff_ofDenoteReal (number 0) p 0 (a - b) rfl hp).mp h))

theorem subPositiveToLt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (haR : In p.val.left R) (hbR : In p.val.right R)
    (h : Lt (number 0) p) : Lt p.val.right p.val.left := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  have hp : denote p = M.number ((a - b : ℝ) : ℂ) := by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hb, M.sub_numbers, Complex.ofReal_sub]
  exact NativeBridge.ltOfDenoteReal _ _ b a hb ha
    (sub_pos.mp ((NativeBridge.lt_iff_ofDenoteReal (number 0) p 0 (a - b) rfl hp).mp h))

theorem leDivOfProductBound {M : Semantics.{u}} {α β γ δ ε : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (q : Obj (M := M) (DivObj (M := M) β γ))
    (p : Obj (M := M) (MulObj (M := M) δ ε)) (haR : In a R)
    (hDivisorPos : Lt (number 0) q.val.right) (hBound : Le p q.val.left)
    (hFactor : Same p.val.left q.val.right) (hArgument : Same p.val.right a) : Le a q := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive q.val.right hDivisorPos
  obtain ⟨r, hr⟩ := (M.real_members _).mp haR
  obtain ⟨s, b, hs, hb, hsb⟩ := hBound
  have hproduct : denote p = M.number ((c * r : ℝ) : ℂ) := by
    change M.mulValue (denote p.val.left) (denote p.val.right) = _
    rw [hFactor.trans hc, hArgument.trans hr, M.mul_numbers, Complex.ofReal_mul]
  have hsProduct : s = c * r :=
    Complex.ofReal_injective (M.number_injective (hs.symm.trans hproduct))
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal a q r (b / c) hr ?_ ?_
  · change M.divValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]
  · apply (le_div_iff₀ hc0).mpr
    simpa only [hsProduct, mul_comm] using hsb

end Litex

namespace Litex

/-- Literal-zero specialization of the selected shared positive divisor rule.
The original quotient and its constructor WD remain the subject. -/
theorem divStructuralNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (DivObj (M := M) α β))
    (hDivisorPos : Lt (number 0) q.val.right)
    (hNumeratorNonnegative : Le (number 0) q.val.left) : Le (number 0) q := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive q.val.right hDivisorPos
  obtain ⟨a, ha, ha0⟩ := NativeBridge.realWitnessOfNonnegative q.val.left hNumeratorNonnegative
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal (number 0) q 0 (a / c) rfl ?_
    (div_nonneg ha0 (le_of_lt hc0))
  change M.divValue (denote q.val.left) (denote q.val.right) = _
  rw [ha, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]

theorem divStructuralNonpositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (DivObj (M := M) α β))
    (hDivisorPos : Lt (number 0) q.val.right)
    (hNumeratorNonpositive : Le q.val.left (number 0)) : Le q (number 0) := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive q.val.right hDivisorPos
  obtain ⟨a, r₀, ha, hz, ha0⟩ := hNumeratorNonpositive
  change M.number 0 = M.number (r₀ : ℂ) at hz
  have hr0 : r₀ = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  subst r₀
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal q (number 0) (a / c) 0 ?_ rfl
    (div_nonpos_of_nonpos_of_nonneg ha0 (le_of_lt hc0))
  change M.divValue (denote q.val.left) (denote q.val.right) = _
  rw [ha, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]

end Litex
