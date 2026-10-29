import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Order.Zorn
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Litex object semantics, certified constructors, and native numeric bridges.

`Obj` always includes its well-definedness proof. Host representations remain
generic, and source equality and membership use their fixed denotations.
`NumericModel.model` is an explicit candidate for the numeric slice; it is not
a default model or a completed model of all Litex objects and rules.
-/

universe u v w x

namespace Litex

open Lean Meta Elab Tactic in
/-- Finish a generated proof without leaving unused local carrier levels open.
Applications first determine every constrained level. Only residual levels
absent from the public proposition receive zero; host types and the proposition
are not changed. The supplied proof must close every goal and is kernel checked.
This performs no proof search. -/
elab "litex_complete" " => " body:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let goals ← Tactic.run goal (evalTactic body)
  unless goals.isEmpty do
    throwError "The recorded Litex proof left open goals."
  let publicLevels := (collectLevelMVars {} (← instantiateMVars (← goal.getType))).result
  let value ← instantiateMVars (mkMVar goal)
  for level in (collectLevelMVars {} value).result do
    unless publicLevels.contains level do
      assignLevelMVar level .zero

open Lean Meta Elab Tactic in
/-- Reuse one already generated proof as a kernel-checked auxiliary theorem.
Local definitions are expanded when closing the theorem, preserving object
values and their WD evidence. This performs no proof search. -/
elab "litex_checked_step" " => " body:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let goals ← Tactic.run goal (evalTactic body)
  unless goals.isEmpty do
    throwError "The recorded Litex step left open goals."
  let value ← instantiateMVars (mkMVar goal)
  let checked ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign checked

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

theorem notInOfSame {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (A : Obj (M := M) γ)
    (hab : Same a b) (hb : ¬ In b A) : ¬ In a A :=
  fun ha => hb (inOfSame a b A A hab (sameRefl A) ha)

theorem notSameOfMembership {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (A : Obj (M := M) γ)
    (ha : In a A) (hb : ¬ In b A) : ¬ Same a b :=
  fun hab => hb (inOfSame a b A A hab (sameRefl A) ha)

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

/-- An already constructed power retains the domain proof used to build it. -/
theorem powObjInC {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) : In p C := by
  rcases p.wd with ⟨haR, n, _heN, he⟩ | ⟨haC, n, _heN, he⟩ | ⟨haC, z, _heZ, ha0, he⟩
  · exact pow_nat_closed _ _ n (realToComplex _ haR) he
  · exact pow_nat_closed _ _ n haC he
  · exact pow_int_closed _ _ z haC ha0 he

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

/-- An integer power of a nonzero base is nonzero. -/
theorem powNonzeroOfBase {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hz : In p.val.exponent Z) (ha : ¬ Same p.val.base (number 0)) :
    ¬ Same p (number 0) := by
  have hc : In p.val.base C := by
    rcases p.wd with ⟨hr, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩
    · exact realToComplex _ hr
    · exact hc
    · exact hc
  obtain ⟨x, hx⟩ := (M.complex_members (denote p.val.base)).mp hc
  obtain ⟨z, hzi⟩ := (M.integer_members (denote p.val.exponent)).mp hz
  have hx0 : x ≠ 0 := fun h => ha (hx.trans (congrArg M.number h))
  have hp : denote p = M.number (x ^ z) := by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [hx, hzi, M.pow_numbers_int x z hx0]
  intro hp0
  apply zpow_ne_zero z hx0
  exact M.number_injective (hp.symm.trans hp0)

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


theorem zeroAdd {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    Same (add (number 0) a (numberInC 0) haC) a := by
  obtain ⟨z, hz⟩ := (M.complex_members (denote a)).mp haC
  change M.addValue (M.number 0) (denote a) = denote a
  rw [hz, M.add_numbers, zero_add]

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

@[simp] theorem asComplex_number (z : ℂ) (h : In (number (M := M) z) C) :
    asComplex (number z) h = z :=
  M.number_injective (asComplex_spec (number z) h).symm

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

/-- The selected division/product conversion observes only its three operands. -/
theorem sameDivIffSameMul {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hc : In c C) (hb0 : ¬ Same b (number 0)) :
    Same (div a b ha hb hb0) c ↔ Same a (mul c b hc hb) := by
  have hb0' := NativeBridge.nativeNonzeroOfDenote b (NativeBridge.asComplex b hb)
    (NativeBridge.asComplex_spec b hb) hb0
  change M.divValue (denote a) (denote b) = denote c ↔
    denote a = M.mulValue (denote c) (denote b)
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec c hc, M.div_numbers _ _ hb0', M.mul_numbers,
    M.number_injective.eq_iff, M.number_injective.eq_iff]
  exact div_eq_iff hb0'

theorem sameMulComm {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a C) (hb : In b C) :
    Same (mul a b ha hb) (mul b a hb ha) := by
  change M.mulValue (denote a) (denote b) = M.mulValue (denote b) (denote a)
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    M.mul_numbers, M.mul_numbers, mul_comm]

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

/-- The absolute value of a nonzero real is nonzero. -/
theorem absNonzeroOfArg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α))
    (ha : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr : denote p.val.arg = M.number ((r : ℝ) : ℂ) := NativeBridge.asReal_spec p.val.arg p.wd
  have hr0 : r ≠ 0 := by
    intro h
    apply ha
    change denote p.val.arg = M.number 0
    have hcast : (r : ℂ) = 0 := by exact_mod_cast h
    exact hr.trans (congrArg M.number hcast)
  have hroot : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr hr0)
  have hp : denote p = M.number ((|r| : ℝ) : ℂ) :=
    NativeBridge.denoteAbs p.val.arg p.wd r hr
  intro h
  exact hroot (M.number_injective (hp.symm.trans h))

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

/-- Principal real square root. Its total raw denotation is independent of WD;
the owned constructor below requires a real, nonnegative argument. -/
noncomputable def sqrtValue {M : Semantics.{u}} (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, x = M.number (r : ℂ) then
    M.number ((Real.sqrt (Classical.choose h) : ℝ) : ℂ) else M.number 0

theorem sqrtValue_number {M : Semantics.{u}} (r : ℝ) :
    sqrtValue (M.number (r : ℂ)) = M.number ((Real.sqrt r : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold sqrtValue
  rw [dif_pos h, hr]

structure SqrtObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sqrtRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SqrtObj (M := M) α) where
  wd a := In a.arg R ∧ Le (number 0) a.arg
  denote a := sqrtValue (denote a.arg)
  wd_isSet {a} ha := by
    obtain ⟨r, hr⟩ := (M.real_members (denote a.arg)).mp ha.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sqrt r, by
      rw [hr, sqrtValue_number]⟩)

noncomputable def sqrt {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    Obj (M := M) (SqrtObj (M := M) α) := ⟨⟨a⟩, haR, ha0⟩

namespace NativeBridge

theorem denoteSqrt {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) (r : ℝ)
    (hr : denote a = M.number (r : ℂ)) :
    denote (sqrt a haR ha0) = M.number ((Real.sqrt r : ℝ) : ℂ) := by
  change sqrtValue (denote a) = _
  rw [hr, sqrtValue_number]

end NativeBridge

theorem sqrtInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    In (sqrt a haR ha0) R :=
  (M.real_members _).mpr ⟨Real.sqrt (NativeBridge.asReal a haR),
    NativeBridge.denoteSqrt a haR ha0 _ (NativeBridge.asReal_spec a haR)⟩

theorem sqrtInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    In (sqrt a haR ha0) C := realToComplex _ (sqrtInR a haR ha0)

theorem sqrtNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    Le (number 0) (sqrt a haR ha0) :=
  NativeBridge.leOfDenoteReal _ _ 0 (Real.sqrt (NativeBridge.asReal a haR)) rfl
    (NativeBridge.denoteSqrt a haR ha0 _ (NativeBridge.asReal_spec a haR))
    (Real.sqrt_nonneg _)

/-- Defined principal square roots preserve the order of their arguments. -/
theorem sqrtMonotone {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (q : Obj (M := M) (SqrtObj (M := M) β))
    (h : Le p.val.arg q.val.arg) : Le p q := by
  let x := NativeBridge.asReal p.val.arg p.wd.1
  let y := NativeBridge.asReal q.val.arg q.wd.1
  have hx := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hy := NativeBridge.asReal_spec q.val.arg q.wd.1
  have hxy : x ≤ y := (NativeBridge.le_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).mp h
  exact NativeBridge.leOfDenoteReal p q (Real.sqrt x) (Real.sqrt y)
    (NativeBridge.denoteSqrt p.val.arg p.wd.1 p.wd.2 x hx)
    (NativeBridge.denoteSqrt q.val.arg q.wd.1 q.wd.2 y hy)
    (Real.sqrt_le_sqrt hxy)

/-- The principal square root of a positive real number is nonzero. -/
theorem sqrtNonzeroOfPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (hpos : Lt (number 0) p.val.arg) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 r rfl hr).mp hpos
  have hroot : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hr0))
  have hp : denote p = M.number ((Real.sqrt r : ℝ) : ℂ) :=
    NativeBridge.denoteSqrt p.val.arg p.wd.1 p.wd.2 r hr
  intro h
  exact hroot (M.number_injective (hp.symm.trans h))

theorem sqrtSquareValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    M.powValue (denote (sqrt a haR ha0)) (M.number ((2 : ℕ) : ℂ)) = denote a := by
  let r := NativeBridge.asReal a haR
  have hr : denote a = M.number (r : ℂ) := NativeBridge.asReal_spec a haR
  have h0 : 0 ≤ r := (NativeBridge.le_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp ha0
  rw [NativeBridge.denoteSqrt a haR ha0 r hr, M.pow_numbers_nat, ← Complex.ofReal_pow,
    Real.sq_sqrt h0, ← hr]

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

/-- Replay a cited zero difference using the original operands' certificates. -/
theorem sameOfSubZero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a C) (hb : In b C)
    (hsub : Same (sub a b ha hb) (number 0)) : Same a b := by
  by_contra h
  exact (subNonzeroOfNotSame a b ha hb h) hsub

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

theorem notSameNegOfNonzeroSumLeft {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (q : Obj (M := M) γ)
    (hq : denote q = M.negValue (denote p.val.right))
    (h : ¬ Same p (number 0)) : ¬ Same p.val.left q := by
  intro he
  apply h
  change M.addValue (denote p.val.left) (denote p.val.right) = M.number 0
  change denote p.val.left = denote q at he
  rw [hq, NativeBridge.asComplex_spec p.val.right p.wd.2, M.neg_numbers] at he
  rw [he, NativeBridge.asComplex_spec p.val.right p.wd.2, M.add_numbers, neg_add_cancel]

theorem notSameNegOfNonzeroSumRight {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (q : Obj (M := M) γ)
    (hq : denote q = M.negValue (denote p.val.left))
    (h : ¬ Same p (number 0)) : ¬ Same p.val.right q := by
  intro he
  apply h
  change M.addValue (denote p.val.left) (denote p.val.right) = M.number 0
  change denote p.val.right = denote q at he
  rw [hq, NativeBridge.asComplex_spec p.val.left p.wd.1, M.neg_numbers] at he
  rw [he, NativeBridge.asComplex_spec p.val.left p.wd.1, M.add_numbers, add_neg_cancel]

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

theorem sameOfLeAntisymm {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (hab : Le a b) (hba : Le b a) : Same a b := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', r', hs', hr', hsr⟩ := hba
  have er : r = r' := Complex.ofReal_injective (M.number_injective (hr.symm.trans hr'))
  have es : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  have h : r = s := le_antisymm hrs (by simpa only [← er, ← es] using hsr)
  exact hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ)) h).trans hs.symm)

theorem leSelfAddRight {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (haR : In p.val.left R) (hb : Le (number 0) p.val.right) : Le p.val.left p := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨z, b, hz, hb, hzb⟩ := hb
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  refine ⟨a, a + b, ha, ?_, le_add_of_nonneg_right (by simpa only [hz0] using hzb)⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [ha, hb, M.add_numbers, Complex.ofReal_add]

theorem leSelfAddLeft {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (hbR : In p.val.right R) (ha : Le (number 0) p.val.left) : Le p.val.right p := by
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  obtain ⟨z, a, hz, ha, hza⟩ := ha
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  refine ⟨b, a + b, hb, ?_, le_add_of_nonneg_left (by simpa only [hz0] using hza)⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [ha, hb, M.add_numbers, Complex.ofReal_add]

theorem ltAddOfLeOfPos {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (AddObj (M := M) β γ))
    (ha : Le a p.val.left) (hb : Lt (number 0) p.val.right) : Lt a p := by
  obtain ⟨a', x', ha', hx', hax⟩ := ha
  obtain ⟨z', y', hz', hy', hzy⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨a', x' + y', ha', ?_, ?_⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [hx', hy', M.add_numbers, Complex.ofReal_add]
  · have hpos : (0 : ℝ) < y' := hz0 ▸ hzy
    exact lt_of_le_of_lt hax (lt_add_of_pos_right x' hpos)

theorem addLtAdd {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Lt p.val.left q.val.left) (h₂ : Lt p.val.right q.val.right) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_lt_add hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem addStructuralLtLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (AddObj (M := M) α β))
    (rhs : Obj (M := M) (AddObj (M := M) γ δ))
    (hSum : In lhs R)
    (hOrder : Lt lhs.val.right rhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hSum
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.1
  have hsum : z + (a : ℂ) = (r : ℂ) := by
    apply M.number_injective
    change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.add_numbers] using hr
  have hc : denote lhs.val.left = M.number ((r - a : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (eq_sub_iff_add_eq.mpr hsum)
  refine NativeBridge.ltOfDenoteReal lhs rhs ((r - a) + a) ((r - a) + b) ?_ ?_ (add_lt_add_right hab (r - a))
  · change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hSame.symm.trans hc, hb, M.add_numbers, Complex.ofReal_add]

theorem addStructuralLtRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (AddObj (M := M) α β))
    (rhs : Obj (M := M) (AddObj (M := M) γ δ))
    (hSum : In lhs R)
    (hOrder : Lt lhs.val.left rhs.val.left)
    (hSame : Same lhs.val.right rhs.val.right) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hSum
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.2
  have hsum : (a : ℂ) + z = (r : ℂ) := by
    apply M.number_injective
    change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.add_numbers] using hr
  have hc : denote lhs.val.right = M.number ((r - a : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (eq_sub_iff_add_eq.mpr ((add_comm z (a : ℂ)).trans hsum))
  refine NativeBridge.ltOfDenoteReal lhs rhs (a + (r - a)) (b + (r - a)) ?_ ?_ (add_lt_add_left hab (r - a))
  · change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hSame.symm.trans hc, hb, M.add_numbers, Complex.ofReal_add]

theorem addLtAddSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Lt p.val.left q.val.right) (h₂ : Lt p.val.right q.val.left) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, d + b, ?_, ?_, ?_⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hd, hb, M.add_numbers, Complex.ofReal_add]
  · simpa only [add_comm b d] using add_lt_add hab hcd

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

/-- Monotonicity consumes the captured nonnegative lower base and ordered bases. -/
theorem powStructuralLe {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (left : Obj (M := M) (PowObj (M := M) α β))
    (right : Obj (M := M) (PowObj (M := M) γ δ)) (n : ℕ)
    (heL : Same left.val.exponent (number (n : ℂ)))
    (heR : Same right.val.exponent (number (n : ℂ)))
    (h0 : Le (number 0) left.val.base)
    (hle : Le left.val.base right.val.base) : Le left right := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hle
  have hr0 : 0 ≤ r :=
    (NativeBridge.le_iff_ofDenoteReal (number 0) left.val.base 0 r rfl hr).mp h0
  refine NativeBridge.leOfDenoteReal left right (r ^ n) (s ^ n) ?_ ?_
    (pow_le_pow_left₀ hr0 hrs n)
  · change M.powValue (denote left.val.base) (denote left.val.exponent) = _
    change denote left.val.exponent = M.number (n : ℂ) at heL
    rw [hr, heL, M.pow_numbers_nat, Complex.ofReal_pow]
  · change M.powValue (denote right.val.base) (denote right.val.exponent) = _
    change denote right.val.exponent = M.number (n : ℂ) at heR
    rw [hs, heR, M.pow_numbers_nat, Complex.ofReal_pow]

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

/-- A nonzero product has two nonzero factors. -/
theorem productNonzeroFactors {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (h : ¬ Same p (number 0)) :
    (¬ Same p.val.left (number 0)) ∧ (¬ Same p.val.right (number 0)) := by
  obtain ⟨x, hx⟩ := (M.complex_members (denote p.val.left)).mp p.wd.1
  obtain ⟨y, hy⟩ := (M.complex_members (denote p.val.right)).mp p.wd.2
  constructor
  · intro ha
    have hx0 : x = 0 := M.number_injective (hx.symm.trans ha)
    apply h
    change M.mulValue (denote p.val.left) (denote p.val.right) = M.number 0
    rw [hx, hy, M.mul_numbers, hx0, zero_mul]
  · intro hb
    have hy0 : y = 0 := M.number_injective (hy.symm.trans hb)
    apply h
    change M.mulValue (denote p.val.left) (denote p.val.right) = M.number 0
    rw [hx, hy, M.mul_numbers, hy0, mul_zero]

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

/-- A singleton host carrier may represent a certified semantic value at any level. -/
structure ValueAtLevel {M : Semantics.{u}} (value : M.Value) (certified : M.isSet value) : Type v where

instance valueAtLevelRepresentation {M : Semantics.{u}} (value : M.Value) (certified : M.isSet value) :
    Representation M (ValueAtLevel.{u,v} value certified) where
  wd _ := True
  denote _ := value
  wd_isSet _ := certified

def objectAtLevel {M : Semantics.{u}} (value : M.Value) (certified : M.isSet value) :
    Obj (M := M) (ValueAtLevel.{u,v} value certified) := ⟨⟨⟩, True.intro⟩

theorem semanticObject_denote {M : Semantics.{u}} (x : M.Value) (hx : M.isSet x) :
    denote (semanticObject x hx) = x := rfl

/-- The real-line existence rule chooses a semantic real above its free operand. -/
theorem existsRealAbove {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    ∃ b : Obj (M := M) M.Value, In b R ∧ Lt a b := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp ha
  have hb := NativeBridge.numberInR (M := M) (r + 1)
  exact ⟨semanticObject (M.number ((r + 1 : ℝ) : ℂ)) (M.member_isSet hb),
    hb, r, r + 1, hr, rfl, lt_add_one r⟩

/-- The same rule chooses a semantic real below its free operand. -/
theorem existsRealBelow {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    ∃ b : Obj (M := M) M.Value, In b R ∧ Lt b a := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp ha
  have hb := NativeBridge.numberInR (M := M) (r - 1)
  exact ⟨semanticObject (M.number ((r - 1 : ℝ) : ℂ)) (M.member_isSet hb),
    hb, r - 1, r, rfl, hr, sub_one_lt r⟩

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

/-- Strong induction uses precisely the integer indices from zero through the
current predecessor. The exported object keeps its original representation. -/
theorem integerStrongInductionFromZero {M : Semantics.{u}}
    (P : M.Value → Prop) (h0 : P (M.number 0))
    (hstep : ∀ (k : M.Value) (hkZ : M.mem k (M.standard .integer)),
      Le (number 0) (semanticObject k (M.member_isSet hkZ)) →
      (∀ (m : M.Value) (hmZ : M.mem m (M.standard .integer)),
        Le (number 0) (semanticObject m (M.member_isSet hmZ)) →
        Le (semanticObject m (M.member_isSet hmZ))
          (semanticObject k (M.member_isSet hkZ)) → P m) →
      P (M.addValue k (M.number 1)))
    {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) (ha0 : Le (number 0) a) : P (denote a) := by
  have hn := integerToNaturalOfNonnegative a haZ ha0
  have hall : ∀ n : ℕ, P (M.number (n : ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [Nat.cast_zero] using h0
      | succ k =>
        have hkZ : M.mem (M.number (k : ℂ)) (M.standard .integer) :=
          (M.integer_members _).mpr ⟨(k : ℤ), by simp only [Int.cast_natCast]⟩
        have hk0 := naturalNonnegative
          (semanticObject (M.number (k : ℂ)) (M.member_isSet hkZ))
          (NativeBridge.numberInN k)
        have previous (m : M.Value) (hmZ : M.mem m (M.standard .integer))
            (hm0 : Le (number 0) (semanticObject m (M.member_isSet hmZ)))
            (hmk : Le (semanticObject m (M.member_isSet hmZ))
              (semanticObject (M.number (k : ℂ)) (M.member_isSet hkZ))) : P m := by
          have hmN := integerToNaturalOfNonnegative
            (semanticObject m (M.member_isSet hmZ)) hmZ hm0
          obtain ⟨j, hj⟩ := (M.natural_members m).mp hmN
          have hle := (NativeBridge.le_iff_ofDenoteReal
            (semanticObject m (M.member_isSet hmZ))
            (semanticObject (M.number (k : ℂ)) (M.member_isSet hkZ))
            (j : ℝ) (k : ℝ)
            (by simpa only [semanticObject_denote, Complex.ofReal_natCast] using hj)
            (by simp only [semanticObject_denote, Complex.ofReal_natCast])).mp hmk
          have hjk : j ≤ k := by exact_mod_cast hle
          exact hj.symm ▸ ih j (Nat.lt_succ_of_le hjk)
        simpa only [M.add_numbers, Nat.cast_add, Nat.cast_one] using
          hstep (M.number (k : ℂ)) hkZ hk0 previous
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
  unionValue := ZFSet.union
  union_members _ _ _ := ZFSet.mem_union
  union_isSet _ _ _ _ := True.intro
  powerValue := ZFSet.powerset
  power_members A B := by
    change B ∈ ZFSet.powerset A ↔ True ∧ ZFSet.Subset B A
    exact ⟨fun h => ⟨True.intro, ZFSet.mem_powerset.mp h⟩,
      fun h => ZFSet.mem_powerset.mpr h.2⟩
  power_isSet _ _ := True.intro
  ext _ _ _ _ := ZFSet.ext

/-- Optional indexed unions for dependent carriers. This does not strengthen
`SetSemantics`: a model supplies this interface when such constructions are used.
The index domain is a set, never a collection of all semantic values. -/
class IndexedUnionSemantics (M : Semantics.{u}) where
  indexedUnionValue : M.Value → (M.Value → M.Value) → M.Value
  indexedUnion_members : ∀ A B x, M.mem x (indexedUnionValue A B) ↔
    ∃ a, M.mem a A ∧ M.mem x (B a)
  indexedUnion_isSet : ∀ A B, M.isSet A →
    (∀ a, M.mem a A → M.isSet (B a)) → M.isSet (indexedUnionValue A B)

noncomputable instance numericIndexedUnionSemantics :
    IndexedUnionSemantics NumericModel.model where
  indexedUnionValue := fun (A : ZFSet.{0}) (B : ZFSet.{0} → ZFSet.{0}) =>
    ZFSet.iUnion (fun a : A => B a.val)
  indexedUnion_members := fun (A : ZFSet.{0}) (B : ZFSet.{0} → ZFSet.{0}) (x : ZFSet.{0}) => by
    change x ∈ ZFSet.iUnion (fun a : A => B a.val) ↔ ∃ a, a ∈ A ∧ x ∈ B a
    constructor
    · intro h
      obtain ⟨a, ha⟩ := ZFSet.mem_iUnion.mp h
      exact ⟨a.val, a.property, ha⟩
    · rintro ⟨a, ha, hx⟩
      exact ZFSet.mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩
  indexedUnion_isSet _ _ _ _ := True.intro

private noncomputable def replacementChoice {M : Semantics.{u}} [S : SetSemantics M]
    (P : M.Value → M.Value → Prop) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ y, M.isSet y ∧ P x y then Classical.choose h else S.emptyValue

private theorem replacementChoice_spec {M : Semantics.{u}} [SetSemantics M]
    (P : M.Value → M.Value → Prop) (x : M.Value) (h : ∃ y, M.isSet y ∧ P x y) :
    M.isSet (replacementChoice P x) ∧ P x (replacementChoice P x) := by
  rw [replacementChoice, dif_pos h]
  exact Classical.choose_spec h

structure ReplacementObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  domain : Obj (M := M) α
  relation : M.Value → M.Value → Prop

private noncomputable def replacementValue {M : Semantics.{u}}
    [S : SetSemantics M] [I : IndexedUnionSemantics M]
    (D : M.Value) (P : M.Value → M.Value → Prop) : M.Value :=
  I.indexedUnionValue (S.sepValue D (fun x => ∃ y, M.isSet y ∧ P x y))
    (fun x => S.insertValue (replacementChoice P x) S.emptyValue)

private theorem replacementValue_isSet {M : Semantics.{u}}
    [S : SetSemantics M] [I : IndexedUnionSemantics M]
    (D : M.Value) (P : M.Value → M.Value → Prop) (hD : M.isSet D) :
    M.isSet (replacementValue D P) := by
  apply I.indexedUnion_isSet _ _ (S.sep_isSet _ _ hD)
  intro x hx
  have exists_y := ((S.sep_members _ _ _).mp hx).2
  exact S.insert_isSet _ _ (replacementChoice_spec P x exists_y).1 S.empty_isSet

noncomputable instance replacementRepresentation {M : Semantics.{u}}
    [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] : Representation M (ReplacementObj (M := M) α) where
  wd p := ∀ x, M.mem x (denote p.domain) → ∀ y z,
    M.isSet y → p.relation x y → M.isSet z → p.relation x z → y = z
  denote p := replacementValue (denote p.domain) p.relation
  wd_isSet {p} _ := replacementValue_isSet _ _ (isSet p.domain)

noncomputable def replacement {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (D : Obj (M := M) α)
    (P : M.Value → M.Value → Prop)
    (h : ∀ x, M.mem x (denote D) → ∀ y z, M.isSet y → P x y → M.isSet z → P x z → y = z) :
    Obj (M := M) (ReplacementObj (M := M) α) := ⟨⟨D, P⟩, h⟩

theorem replacement_members {M : Semantics.{u}} [S : SetSemantics M] [I : IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (ReplacementObj (M := M) α))
    (y : M.Value) : M.mem y (denote p) ↔
      ∃ x, M.mem x (denote p.val.domain) ∧ M.isSet y ∧ p.val.relation x y := by
  change M.mem y (replacementValue _ _) ↔ _
  rw [replacementValue, I.indexedUnion_members]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨hxD, hex⟩ := (S.sep_members _ _ _).mp hx
    rcases (S.insert_members _ _ _).mp hy with hy | hy
    · subst y
      exact ⟨x, hxD, replacementChoice_spec _ _ hex⟩
    · exact False.elim (S.empty_members _ hy)
  · rintro ⟨x, hxD, hy, hP⟩
    have hex : ∃ z, M.isSet z ∧ p.val.relation x z := ⟨y, hy, hP⟩
    have hc := replacementChoice_spec p.val.relation x hex
    refine ⟨x, (S.sep_members _ _ _).mpr ⟨hxD, hex⟩, ?_⟩
    apply (S.insert_members _ _ _).mpr
    exact Or.inl (p.wd x hxD y _ hy hP hc.1 hc.2)

theorem replacementIntro {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (ReplacementObj (M := M) α)) (x : Obj (M := M) β) (y : Obj (M := M) γ)
    (hx : In x p.val.domain) (hP : p.val.relation (denote x) (denote y)) : In y p :=
  (replacement_members p (denote y)).mpr ⟨denote x, hx, isSet y, hP⟩

theorem replacementElim {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ReplacementObj (M := M) α)) (y : Obj (M := M) β) (hy : In y p) :
    ∃ x : Obj (M := M) M.Value, ∃ (_ : In x p.val.domain), p.val.relation (denote x) (denote y) := by
  obtain ⟨x, hx, _, hP⟩ := (replacement_members p (denote y)).mp hy
  exact ⟨semanticObject x (M.member_isSet hx), hx, hP⟩

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

/-- Positive naturals retain both natural membership and strict positivity. -/
def NPos {M : Semantics.{u}} [S : SetSemantics M] : Obj (M := M) M.Value :=
  semanticObject (S.sepValue (M.standard .natural) positiveRealPredicate)
    (S.sep_isSet _ _ (M.standard_isSet .natural))

theorem inNPos_natural {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a NPos) : In a N :=
  ((S.sep_members _ _ _).mp ha).1

theorem numberInNPosOfEq {M : Semantics.{u}} [S : SetSemantics M]
    (z : ℂ) (n : ℕ) (hz : z = (n : ℂ)) (hn : 0 < n) : In (number z) (NPos (M := M)) := by
  apply (S.sep_members _ _ _).mpr
  refine ⟨(M.natural_members _).mpr ⟨n, congrArg M.number hz⟩, (n : ℝ), ?_, ?_⟩
  · change M.number z = M.number ((n : ℝ) : ℂ)
    simpa only [Complex.ofReal_natCast] using congrArg M.number hz
  · exact_mod_cast hn

/-- A refined numeric carrier is bounded separation, using the existing model. -/
def refinedNumericSet {M : Semantics.{u}} [S : SetSemantics M]
    (base : StandardSetValue) (condition : M.Value → Prop) : Obj (M := M) M.Value :=
  semanticObject (S.sepValue (M.standard base) condition)
    (S.sep_isSet _ _ (M.standard_isSet base))

def negativeRealPredicate {M : Semantics.{u}} (x : M.Value) : Prop :=
  ∃ r : ℝ, x = M.number (r : ℂ) ∧ r < 0

theorem positiveRealPredicate_iff {M : Semantics.{u}}
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    positiveRealPredicate (denote a) ↔ Lt (number 0) a := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact NativeBridge.ltOfDenoteReal (number 0) a 0 r rfl hr h
  · rintro ⟨r, s, hr, hs, h⟩
    have hzero : r = 0 := Complex.ofReal_injective (M.number_injective hr).symm
    exact ⟨s, hs, hzero ▸ h⟩

theorem negativeRealPredicate_iff {M : Semantics.{u}}
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    negativeRealPredicate (denote a) ↔ Lt a (number 0) := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact NativeBridge.ltOfDenoteReal a (number 0) r 0 hr rfl h
  · rintro ⟨r, s, hr, hs, h⟩
    have hzero : s = 0 := Complex.ofReal_injective (M.number_injective hs).symm
    exact ⟨r, hr, hzero ▸ h⟩

def QPos {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .rational positiveRealPredicate

theorem inQPos_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a QPos ↔ In a Q ∧ Lt (number 0) a := by
  change M.mem (denote a) (S.sepValue (M.standard .rational) positiveRealPredicate) ↔ _
  rw [S.sep_members]
  rw [positiveRealPredicate_iff]
  rfl

theorem inQPos_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QPos) :
    In a Q := ((inQPos_iff a).mp ha).1

theorem inQPos_positive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QPos) :
    Lt (number 0) a := ((inQPos_iff a).mp ha).2

theorem inQPos_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Q) (h : Lt (number 0) a) : In a QPos :=
  (inQPos_iff a).mpr ⟨ha, h⟩

theorem qPosNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (QPos (M := M)) :=
  ⟨M.number (1), inQPos_intro (number (1)) (NativeBridge.numberInQOfEq (M := M) (1) (1 : ℚ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number 0) (number (1)) 0 (1) rfl rfl (by norm_num))⟩

def QNeg {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .rational negativeRealPredicate

theorem inQNeg_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a QNeg ↔ In a Q ∧ Lt a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .rational) negativeRealPredicate) ↔ _
  rw [S.sep_members]
  rw [negativeRealPredicate_iff]
  rfl

theorem inQNeg_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QNeg) :
    In a Q := ((inQNeg_iff a).mp ha).1

theorem inQNeg_negative {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QNeg) :
    Lt a (number 0) := ((inQNeg_iff a).mp ha).2

theorem inQNeg_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Q) (h : Lt a (number 0)) : In a QNeg :=
  (inQNeg_iff a).mpr ⟨ha, h⟩

theorem qNegNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (QNeg (M := M)) :=
  ⟨M.number (-1), inQNeg_intro (number (-1)) (NativeBridge.numberInQOfEq (M := M) (-1) (-1 : ℚ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number (-1)) (number 0) (-1) 0 (congrArg M.number (by norm_num [number])) rfl (by norm_num))⟩

def ZNeg {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .integer negativeRealPredicate

theorem inZNeg_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a ZNeg ↔ In a Z ∧ Lt a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .integer) negativeRealPredicate) ↔ _
  rw [S.sep_members]
  rw [negativeRealPredicate_iff]
  rfl

theorem inZNeg_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZNeg) :
    In a Z := ((inZNeg_iff a).mp ha).1

theorem inZNeg_negative {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZNeg) :
    Lt a (number 0) := ((inZNeg_iff a).mp ha).2

theorem inZNeg_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Z) (h : Lt a (number 0)) : In a ZNeg :=
  (inZNeg_iff a).mpr ⟨ha, h⟩

theorem zNegNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (ZNeg (M := M)) :=
  ⟨M.number (-1), inZNeg_intro (number (-1)) (NativeBridge.numberInZOfEq (M := M) (-1) (-1 : ℤ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number (-1)) (number 0) (-1) 0 (congrArg M.number (by norm_num [number])) rfl (by norm_num))⟩

def RNeg {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .real negativeRealPredicate

theorem inRNeg_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a RNeg ↔ In a R ∧ Lt a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .real) negativeRealPredicate) ↔ _
  rw [S.sep_members]
  rw [negativeRealPredicate_iff]
  rfl

theorem inRNeg_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RNeg) :
    In a R := ((inRNeg_iff a).mp ha).1

theorem inRNeg_negative {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RNeg) :
    Lt a (number 0) := ((inRNeg_iff a).mp ha).2

theorem inRNeg_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a R) (h : Lt a (number 0)) : In a RNeg :=
  (inRNeg_iff a).mpr ⟨ha, h⟩

theorem rNegNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (RNeg (M := M)) :=
  ⟨M.number (-1), inRNeg_intro (number (-1)) (NativeBridge.numberInROfEq (M := M) (-1) (-1 : ℝ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number (-1)) (number 0) (-1) 0 (congrArg M.number (by norm_num [number])) rfl (by norm_num))⟩

def QStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .rational (fun x => x ≠ M.number 0)

theorem inQStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a QStar ↔ In a Q ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .rational) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inQStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QStar) :
    In a Q := ((inQStar_iff a).mp ha).1

theorem inQStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QStar) :
    ¬ Same a (number 0) := ((inQStar_iff a).mp ha).2

theorem inQStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Q) (h : ¬ Same a (number 0)) : In a QStar :=
  (inQStar_iff a).mpr ⟨ha, h⟩

theorem qStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (QStar (M := M)) :=
  ⟨M.number (1), inQStar_intro (number (1)) (NativeBridge.numberInQOfEq (M := M) (1) (1 : ℚ) (by norm_num)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

def ZStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .integer (fun x => x ≠ M.number 0)

theorem inZStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a ZStar ↔ In a Z ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .integer) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inZStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZStar) :
    In a Z := ((inZStar_iff a).mp ha).1

theorem inZStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZStar) :
    ¬ Same a (number 0) := ((inZStar_iff a).mp ha).2

theorem inZStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Z) (h : ¬ Same a (number 0)) : In a ZStar :=
  (inZStar_iff a).mpr ⟨ha, h⟩

theorem zStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (ZStar (M := M)) :=
  ⟨M.number (1), inZStar_intro (number (1)) (NativeBridge.numberInZOfEq (M := M) (1) (1 : ℤ) (by norm_num)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

def RStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .real (fun x => x ≠ M.number 0)

theorem inRStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a RStar ↔ In a R ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .real) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inRStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RStar) :
    In a R := ((inRStar_iff a).mp ha).1

theorem inRStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RStar) :
    ¬ Same a (number 0) := ((inRStar_iff a).mp ha).2

theorem inRStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a R) (h : ¬ Same a (number 0)) : In a RStar :=
  (inRStar_iff a).mpr ⟨ha, h⟩

theorem rStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (RStar (M := M)) :=
  ⟨M.number (1), inRStar_intro (number (1)) (NativeBridge.numberInROfEq (M := M) (1) (1 : ℝ) (by norm_num)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

def CStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .complex (fun x => x ≠ M.number 0)

theorem inCStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a CStar ↔ In a C ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .complex) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inCStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a CStar) :
    In a C := ((inCStar_iff a).mp ha).1

theorem inCStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a CStar) :
    ¬ Same a (number 0) := ((inCStar_iff a).mp ha).2

theorem inCStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a C) (h : ¬ Same a (number 0)) : In a CStar :=
  (inCStar_iff a).mpr ⟨ha, h⟩

theorem cStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (CStar (M := M)) :=
  ⟨M.number (1), inCStar_intro (number (1)) (numberInC (M := M) (1)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

theorem sameBaseZeroOfPositivePowerZero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (ha : In p.val.base C) (he : In p.val.exponent NPos)
    (hz : Same p (number 0)) : Same p.val.base (number 0) := by
  obtain ⟨a, ha⟩ := (M.complex_members _).mp ha
  obtain ⟨n, hn⟩ := (M.natural_members _).mp (inNPos_natural _ he)
  change M.powValue (denote p.val.base) (denote p.val.exponent) = M.number 0 at hz
  rw [ha, hn, M.pow_numbers_nat] at hz
  have ha0 : a = 0 := eq_zero_of_pow_eq_zero (M.number_injective hz)
  exact ha.trans (congrArg M.number ha0)

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

/-- Replay the recorded operand memberships on the original mul constructor. -/
theorem mulInRPos {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (ha : In p.val.left RPos) (hb : In p.val.right RPos) : In p RPos := by
  apply inRPos_intro p
  · exact mulInR p.val.left p.val.right
      (inRPos_real _ ha) (inRPos_real _ hb)
  · exact mulPositive p.val.left p.val.right p.wd.1 p.wd.2
      (inRPos_positive _ ha) (inRPos_positive _ hb)

/-- Replay the recorded operand memberships on the original div constructor. -/
theorem divInRPos {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DivObj (M := M) α β))
    (ha : In p.val.left RPos) (hb : In p.val.right RPos) : In p RPos := by
  apply inRPos_intro p
  · exact divInR p.val.left p.val.right
      (inRPos_real _ ha) (inRPos_real _ hb) p.wd.2.2
  · exact divPositive p.val.left p.val.right p.wd.1 p.wd.2.1 p.wd.2.2
      (inRPos_positive _ ha) (inRPos_positive _ hb)

/-- Replay the recorded operand memberships on the original mul constructor. -/
theorem mulInQStar {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (ha : In p.val.left QStar) (hb : In p.val.right QStar) : In p QStar := by
  apply inQStar_intro p
  · exact mulInQ p.val.left p.val.right
      (inQStar_base _ ha) (inQStar_base _ hb)
  · exact mulNonzero p.val.left p.val.right p.wd.1 p.wd.2
      (inQStar_nonzero _ ha) (inQStar_nonzero _ hb)

/-- Replay the recorded operand memberships on the original div constructor. -/
theorem divInQStar {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DivObj (M := M) α β))
    (ha : In p.val.left QStar) (hb : In p.val.right QStar) : In p QStar := by
  apply inQStar_intro p
  · exact divInQ p.val.left p.val.right
      (inQStar_base _ ha) (inQStar_base _ hb) p.wd.2.2
  · exact divNonzero p.val.left p.val.right p.wd.1 p.wd.2.1
      (inQStar_nonzero _ ha) (inQStar_nonzero _ hb)

theorem numberNotInROfImaginary {M : Semantics.{u}} (z : ℂ) (hz : z.im ≠ 0) :
    ¬ In (number (M := M) z) R := by
  intro h
  obtain ⟨r, hr⟩ := (M.real_members _).mp h
  have heq : z = (r : ℂ) := M.number_injective hr
  exact hz (heq ▸ Complex.ofReal_im r)

theorem numberNotInZOfDenominator {M : Semantics.{u}} (q : ℚ) (hq : q.den ≠ 1) :
    ¬ In (number (M := M) (q : ℂ)) Z := by
  intro h
  obtain ⟨z, hz⟩ := (M.integer_members _).mp h
  have hc : (q : ℂ) = (z : ℂ) := M.number_injective hz
  have heq : q = (z : ℚ) := by exact_mod_cast hc
  apply hq
  rw [heq, Rat.den_intCast]

theorem numberNotInNOfNegative {M : Semantics.{u}} (q : ℚ) (hq : q < 0) :
    ¬ In (number (M := M) (q : ℂ)) N := by
  intro h
  have hnonneg := (NativeBridge.le_iff_ofDenoteReal (number 0)
    (number (q : ℂ)) 0 (q : ℝ) rfl rfl).mp (naturalNonnegative _ h)
  have hneg : (q : ℝ) < 0 := by exact_mod_cast hq
  exact (not_lt_of_ge hnonneg) hneg

theorem numberNotPositive {M : Semantics.{u}} (q : ℚ) (hq : q ≤ 0) :
    ¬ Lt (number (M := M) 0) (number (q : ℂ)) := by
  intro h
  have hpos := (NativeBridge.lt_iff_ofDenoteReal (number 0)
    (number (q : ℂ)) 0 (q : ℝ) rfl rfl).mp h
  have hnonpos : (q : ℝ) ≤ 0 := by exact_mod_cast hq
  exact (not_lt_of_ge hnonpos) hpos

theorem numberNotNegative {M : Semantics.{u}} (q : ℚ) (hq : 0 ≤ q) :
    ¬ Lt (number (M := M) (q : ℂ)) (number 0) := by
  intro h
  have hneg := (NativeBridge.lt_iff_ofDenoteReal (number (q : ℂ))
    (number 0) (q : ℝ) 0 rfl rfl).mp h
  have hnonneg : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  exact (not_lt_of_ge hnonneg) hneg

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

theorem nPosNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (NPos (M := M)) := by
  exact ⟨M.number 1, numberInNPosOfEq 1 1 (by norm_num) (by decide)⟩

theorem inNPos_positive {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a NPos) :
    Lt (number 0) a := by
  obtain ⟨r, hr, hpos⟩ := ((S.sep_members _ _ _).mp ha).2
  refine ⟨0, r, ?_, hr, hpos⟩
  change M.number (0 : ℂ) = M.number ((0 : ℝ) : ℂ)
  rw [Complex.ofReal_zero]

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

theorem insertNonempty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (InsertObj (M := M) α β)) : IsNonempty s :=
  ⟨denote s.val.element, (S.insert_members _ _ _).mpr (Or.inl rfl)⟩

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

/-- Decode the raw ordered-pair encoding used by graph edges. Source tuples
are finite indexed graphs and use `FiniteFunction.unpack2` below. -/
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

namespace FiniteFunction

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def finiteSetValue : List M.Value → M.Value
  | [] => F.emptyValue
  | a :: xs => F.insertValue a (finiteSetValue xs)

theorem finiteSet_members (xs : List M.Value) (x : M.Value) :
    M.mem x (finiteSetValue xs) ↔ x ∈ xs := by
  induction xs with
  | nil => exact ⟨fun h => (F.empty_members x h).elim, fun h => nomatch h⟩
  | cons a xs ih =>
    rw [finiteSetValue, F.insert_members, List.mem_cons, ih]

theorem finiteSet_isSet (xs : List M.Value) (h : ∀ x ∈ xs, M.isSet x) :
    M.isSet (finiteSetValue xs) := by
  induction xs with
  | nil => exact F.empty_isSet
  | cons a xs ih =>
    exact F.insert_isSet _ _ (h a (List.mem_cons_self))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

def index {n : ℕ} (i : Fin n) : M.Value := M.number ((i.val + 1 : ℕ) : ℂ)

omit F in
theorem index_injective {n : ℕ} : Function.Injective (index (M := M) (n := n)) := by
  intro i j h
  have hcast := M.number_injective h
  have hnat : i.val + 1 = j.val + 1 := by exact_mod_cast hcast
  exact Fin.ext (Nat.add_right_cancel hnat)

def indexSet (n : ℕ) : M.Value := finiteSetValue (List.ofFn (index (M := M) (n := n)))

theorem indexSet_members {n : ℕ} (x : M.Value) :
    M.mem x (indexSet n) ↔ ∃ i : Fin n, x = index i := by
  simp only [indexSet, finiteSet_members, List.mem_ofFn]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

theorem index_mem {n : ℕ} (i : Fin n) : M.mem (index (M := M) i) (indexSet n) :=
  (indexSet_members _).mpr ⟨i, rfl⟩

theorem indexSet_isSet (n : ℕ) : M.isSet (indexSet (M := M) n) := by
  apply finiteSet_isSet
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact isSet (number ((i.val + 1 : ℕ) : ℂ))

def tupleValue {n : ℕ} (a : Fin n → M.Value) : M.Value :=
  finiteSetValue (List.ofFn (fun i => F.pairValue (index i) (a i)))

theorem tuple_members {n : ℕ} (a : Fin n → M.Value) (p : M.Value) :
    M.mem p (tupleValue a) ↔ ∃ i : Fin n, p = F.pairValue (index i) (a i) := by
  simp only [tupleValue, finiteSet_members, List.mem_ofFn]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

theorem tuple_pair_mem {n : ℕ} (a : Fin n → M.Value) (x y : M.Value) :
    M.mem (F.pairValue x y) (tupleValue a) ↔
      ∃ i : Fin n, x = index i ∧ y = a i := by
  rw [tuple_members]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, F.pair_injective h⟩
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i, rfl⟩

theorem tuple_isFunction {n : ℕ} (a : Fin n → M.Value) :
    IsFunctionGraph F.pairValue (indexSet n) (finiteSetValue (List.ofFn a))
      (tupleValue a) := by
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := (tuple_members a p).mp hp
    exact ⟨index i, index_mem i, a i,
      (finiteSet_members _ _).mpr (List.mem_ofFn.mpr ⟨i, rfl⟩), rfl⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
    refine ⟨a i, (tuple_pair_mem a _ _).mpr ⟨i, rfl, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨j, hij, hy⟩ := (tuple_pair_mem a _ _).mp hy
    have hji : i = j := index_injective hij
    exact hy.trans (congrArg a hji.symm)

theorem tuple_isSet {n : ℕ} (a : Fin n → M.Value) : M.isSet (tupleValue a) :=
  M.member_isSet ((F.fnSet_members _ _ _).mpr (tuple_isFunction a))

theorem call_tuple {n : ℕ} (a : Fin n → M.Value) (i : Fin n) :
    F.callValue (tupleValue a) (index i) = a i := by
  have h := F.call_graph _ _ _ _ (tuple_isFunction a) (index_mem i)
  obtain ⟨j, hij, hy⟩ := (tuple_pair_mem a _ _).mp h
  exact hy.trans (congrArg a (index_injective hij).symm)

def finiteUnionValue : List M.Value → M.Value
  | [] => F.emptyValue
  | A :: As => F.unionValue A (finiteUnionValue As)

theorem finiteUnion_members (As : List M.Value) (x : M.Value) :
    M.mem x (finiteUnionValue As) ↔ ∃ A ∈ As, M.mem x A := by
  induction As with
  | nil =>
    exact ⟨fun h => (F.empty_members x h).elim, fun ⟨A, hA, _⟩ => nomatch hA⟩
  | cons A As ih =>
    rw [finiteUnionValue, F.union_members, ih]
    constructor
    · rintro (hx | ⟨B, hB, hx⟩)
      · exact ⟨A, List.mem_cons_self, hx⟩
      · exact ⟨B, List.mem_cons_of_mem A hB, hx⟩
    · rintro ⟨B, hB, hx⟩
      rcases List.mem_cons.mp hB with rfl | hB
      · exact Or.inl hx
      · exact Or.inr ⟨B, hB, hx⟩

theorem finiteUnion_isSet (As : List M.Value) (h : ∀ A ∈ As, M.isSet A) :
    M.isSet (finiteUnionValue As) := by
  induction As with
  | nil => exact F.empty_isSet
  | cons A As ih =>
    exact F.union_isSet _ _ (h A List.mem_cons_self)
      (ih (fun B hB => h B (List.mem_cons_of_mem A hB)))

def cartValue {n : ℕ} (A : Fin n → M.Value) : M.Value :=
  F.sepValue (F.fnSetValue (indexSet n) (finiteUnionValue (List.ofFn A)))
    (fun p => ∀ i, M.mem (F.callValue p (index i)) (A i))

theorem cart_members {n : ℕ} (A : Fin n → M.Value) (p : M.Value) :
    M.mem p (cartValue A) ↔
      IsFunctionGraph F.pairValue (indexSet n) (finiteUnionValue (List.ofFn A)) p ∧
      ∀ i, M.mem (F.callValue p (index i)) (A i) := by
  rw [cartValue, F.sep_members, F.fnSet_members]

theorem cart_isSet {n : ℕ} (A : Fin n → M.Value) (hA : ∀ i, M.isSet (A i)) :
    M.isSet (cartValue A) := by
  apply F.sep_isSet
  apply F.fnSet_isSet _ _ (indexSet_isSet n)
  apply finiteUnion_isSet
  intro B hB
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
  exact hA i

theorem tuple_inCart {n : ℕ} (a A : Fin n → M.Value) (h : ∀ i, M.mem (a i) (A i)) :
    M.mem (tupleValue a) (cartValue A) := by
  apply (cart_members A _).mpr
  constructor
  · constructor
    · intro p hp
      obtain ⟨i, rfl⟩ := (tuple_members a p).mp hp
      refine ⟨index i, index_mem i, a i, ?_, rfl⟩
      exact (finiteUnion_members _ _).mpr ⟨A i, List.mem_ofFn.mpr ⟨i, rfl⟩, h i⟩
    · exact (tuple_isFunction a).2
  · intro i
    rw [call_tuple]
    exact h i

theorem coordinate_mem {n : ℕ} {A : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A)) (i : Fin n) : M.mem (F.callValue p (index i)) (A i) :=
  ((cart_members A p).mp hp).2 i

theorem coordinate_mem_number {n : ℕ} {A : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A)) (i : Fin n) (z : ℂ)
    (hz : z = ((i.val + 1 : ℕ) : ℂ)) :
    M.mem (F.callValue p (M.number z)) (A i) := by
  rw [hz]
  exact coordinate_mem hp i

theorem graph_pair_value {D B f x y : M.Value}
    (hf : IsFunctionGraph F.pairValue D B f) (hxy : M.mem (F.pairValue x y) f) :
    M.mem x D ∧ y = F.callValue f x := by
  obtain ⟨a, ha, b, _, hab⟩ := hf.1 _ hxy
  obtain ⟨rfl, rfl⟩ := F.pair_injective hab
  have hcall := F.call_graph D B f x hf ha
  obtain ⟨z, _, hz⟩ := hf.2 x ha
  exact ⟨ha, (hz y hxy).trans (hz _ hcall).symm⟩

/-- A complete finite function belongs to new factors when each coordinate does. -/
theorem cart_of_coordinates {n : ℕ} {A B : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A))
    (h : ∀ i : Fin n, M.mem (F.callValue p (index i)) (B i)) :
    M.mem p (cartValue B) := by
  have hf := ((cart_members A p).mp hp).1
  apply (cart_members B p).mpr
  refine ⟨⟨?_, hf.2⟩, h⟩
  intro edge he
  obtain ⟨x, hx, y, _, rfl⟩ := hf.1 edge he
  obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
  refine ⟨index i, index_mem i, y, ?_, rfl⟩
  rw [(graph_pair_value hf he).2]
  exact (finiteUnion_members _ _).mpr ⟨B i, List.mem_ofFn.mpr ⟨i, rfl⟩, h i⟩

theorem cart_ext {n : ℕ} {A B : Fin n → M.Value} {p q : M.Value}
    (hp : M.mem p (cartValue A)) (hq : M.mem q (cartValue B))
    (h : ∀ i : Fin n, F.callValue p (index i) = F.callValue q (index i)) : p = q := by
  apply F.ext p q (M.member_isSet hp) (M.member_isSet hq)
  intro edge
  constructor
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := ((cart_members A p).mp hp).1.1 edge he
    obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
    have hy := (graph_pair_value ((cart_members A p).mp hp).1 he).2
    rw [hy, h i]
    exact F.call_graph _ _ _ _ ((cart_members B q).mp hq).1 (index_mem i)
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := ((cart_members B q).mp hq).1.1 edge he
    obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
    have hy := (graph_pair_value ((cart_members B q).mp hq).1 he).2
    rw [hy, ← h i]
    exact F.call_graph _ _ _ _ ((cart_members A p).mp hp).1 (index_mem i)

theorem reconstruct {n : ℕ} {A : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A)) :
    p = tupleValue (fun i : Fin n => F.callValue p (index i)) := by
  apply cart_ext hp (tuple_inCart _ A (coordinate_mem hp))
  intro i
  rw [call_tuple]

def pack2 (a b : M.Value) : M.Value := tupleValue ![a, b]

def unpack2 (p : M.Value) : M.Value × M.Value :=
  (F.callValue p (M.number 1), F.callValue p (M.number 2))

theorem unpack_pack2 (a b : M.Value) : unpack2 (pack2 a b) = (a, b) := by
  apply Prod.ext
  · simpa [unpack2, pack2, index] using call_tuple ![a, b] (0 : Fin 2)
  · simpa [unpack2, pack2, index] using call_tuple ![a, b] (1 : Fin 2)

theorem pack2_injective : Function.Injective2 (pack2 (M := M)) := by
  intro a b c d h
  have hp := congrArg (unpack2 (M := M)) h
  rw [unpack_pack2, unpack_pack2] at hp
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

theorem cart2_members (A B p : M.Value) :
    M.mem p (cartValue ![A, B]) ↔
      ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧ p = pack2 a b := by
  constructor
  · intro hp
    refine ⟨F.callValue p (M.number 1), by simpa [index] using coordinate_mem hp (0 : Fin 2),
      F.callValue p (M.number 2), by simpa [index] using coordinate_mem hp (1 : Fin 2), ?_⟩
    refine (reconstruct hp).trans (congrArg tupleValue ?_)
    funext i
    fin_cases i <;> simp [index]
  · rintro ⟨a, ha, b, hb, rfl⟩
    apply tuple_inCart
    intro i
    fin_cases i
    · exact ha
    · exact hb

end FiniteFunction

namespace FunctionSemantics

/-- Change a function's return bound while retaining its complete input domain. -/
theorem fnSet_of_returns {M : Semantics.{u}} [F : FunctionSemantics M]
    {D B E f : M.Value} (hf : M.mem f (F.fnSetValue D B))
    (h : ∀ x, M.mem x D → M.mem (F.callValue f x) E) :
    M.mem f (F.fnSetValue D E) := by
  have hg := (F.fnSet_members D B f).mp hf
  apply (F.fnSet_members D E f).mpr
  refine ⟨?_, hg.2⟩
  intro edge he
  obtain ⟨x, hx, y, _, rfl⟩ := hg.1 edge he
  refine ⟨x, hx, y, ?_, rfl⟩
  rw [(FiniteFunction.graph_pair_value hg he).2]
  exact h x hx

end FunctionSemantics

structure TupleObj (M : Semantics.{u}) (n : ℕ) where
  values : Fin n → M.Value

instance tupleRepresentation {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ} :
    Representation M (TupleObj M n) where
  wd t := ∀ i, M.isSet (t.values i)
  denote t := FiniteFunction.tupleValue t.values
  wd_isSet {t} _ := FiniteFunction.tuple_isSet t.values

def tuple {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (values : Fin n → M.Value) (hSets : ∀ i, M.isSet (values i)) :
    Obj (M := M) (TupleObj M n) := ⟨⟨values⟩, hSets⟩

/-- Internal call packing preserves both certified source argument objects. -/
structure CallArguments2 {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  first : Obj (M := M) α
  second : Obj (M := M) β

instance callArguments2Representation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CallArguments2 (M := M) α β) where
  wd _ := True
  denote args := FiniteFunction.tupleValue ![denote args.first, denote args.second]
  wd_isSet {args} _ := FiniteFunction.tuple_isSet ![denote args.first, denote args.second]

def callArguments2 {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) :
    Obj (M := M) (CallArguments2 (M := M) α β) := ⟨⟨a, b⟩, True.intro⟩

theorem callArguments2_denote {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) :
    denote (callArguments2 a b) = FiniteFunction.tupleValue ![denote a, denote b] := rfl

theorem callArguments2_mem_cart {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) {A B : M.Value}
    (ha : M.mem (denote a) A) (hb : M.mem (denote b) B) :
    M.mem (denote (callArguments2 a b)) (FiniteFunction.cartValue ![A, B]) :=
  FiniteFunction.tuple_inCart ![denote a, denote b] ![A, B]
    (Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i)))

structure CartObj (M : Semantics.{u}) (n : ℕ) where
  factors : Fin n → M.Value

instance cartRepresentation {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ} :
    Representation M (CartObj M n) where
  wd c := ∀ i, M.isSet (c.factors i)
  denote c := FiniteFunction.cartValue c.factors
  wd_isSet {c} h := FiniteFunction.cart_isSet c.factors h

def cart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (factors : Fin n → M.Value) (hSets : ∀ i, M.isSet (factors i)) :
    Obj (M := M) (CartObj M n) := ⟨⟨factors⟩, hSets⟩

theorem cartNonemptyOfFactors {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (c : Obj (M := M) (CartObj M n))
    (h : ∀ i, ∃ x, M.mem x (c.val.factors i)) : IsNonempty c := by
  classical
  refine ⟨FiniteFunction.tupleValue (fun i => Classical.choose (h i)), ?_⟩
  exact FiniteFunction.tuple_inCart _ _ (fun i => Classical.choose_spec (h i))

/-- The return bound can contain the factors in any association/order of unions;
the complete domain and every coordinate condition remain explicit. -/
theorem cartMembersWithReturnBound {M : Semantics.{u}} [F : FunctionSemantics M]
    {n : ℕ} (A : Fin n → M.Value) (B : M.Value)
    (hB : ∀ i x, M.mem x (A i) → M.mem x B) (p : M.Value) :
    M.mem p (FiniteFunction.cartValue A) ↔
      M.mem p (F.fnSetValue (FiniteFunction.indexSet n) B) ∧
      ∀ i, M.mem (F.callValue p (FiniteFunction.index i)) (A i) := by
  constructor
  · intro hp
    obtain ⟨hg, hc⟩ := (F.sep_members _ _ _).mp hp
    refine ⟨F.fnSet_of_returns hg ?_, hc⟩
    intro x hx
    obtain ⟨i, rfl⟩ := (FiniteFunction.indexSet_members (M := M) x).mp hx
    exact hB i _ (hc i)
  · rintro ⟨hg, hc⟩
    apply (F.sep_members _ _ _).mpr
    refine ⟨F.fnSet_of_returns hg ?_, hc⟩
    intro x hx
    obtain ⟨i, rfl⟩ := (FiniteFunction.indexSet_members (M := M) x).mp hx
    exact (FiniteFunction.finiteUnion_members _ _).mpr
      ⟨A i, List.mem_ofFn.mpr ⟨i, rfl⟩, hc i⟩

theorem cartSameSetBuilder {M : Semantics.{u}} [F : FunctionSemantics M]
    {n : ℕ} {β : Type v} [Representation M β]
    (c : Obj (M := M) (CartObj M n)) (D : Obj (M := M) β)
    (P : (x : Obj (M := M) M.Value) → In x D → Prop) (B : M.Value)
    (hD : denote D = F.fnSetValue (FiniteFunction.indexSet n) B)
    (hB : ∀ i x, M.mem x (c.val.factors i) → M.mem x B)
    (hP : ∀ x hx, P x hx ↔
      ∀ i, M.mem (F.callValue (denote x) (FiniteFunction.index i)) (c.val.factors i)) :
    Same c (setBuilder D P) := by
  apply F.ext _ _ (isSet c) (isSet (setBuilder D P))
  intro raw
  change M.mem raw (FiniteFunction.cartValue c.val.factors) ↔
    M.mem raw (F.sepValue (denote D) (SetBuilderObj.condition ⟨D, P⟩))
  rw [F.sep_members]
  constructor
  · intro hc
    obtain ⟨hg, hp⟩ := (cartMembersWithReturnBound _ B hB raw).mp hc
    have hx : M.mem raw (denote D) := by rw [hD]; exact hg
    exact ⟨hx, hx, (hP (semanticObject raw (M.member_isSet hx)) hx).mpr hp⟩
  · rintro ⟨hx, hx', hp⟩
    apply (cartMembersWithReturnBound _ B hB raw).mpr
    exact ⟨by rw [← hD]; exact hx,
      (hP (semanticObject raw (M.member_isSet hx')) hx').mp hp⟩

theorem cartZeroSame {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type v} [Representation M β]
    (c : Obj (M := M) (CartObj M 0)) (D : Obj (M := M) β)
    (hD : denote D = F.fnSetValue (FiniteFunction.indexSet 0) F.emptyValue) :
    Same c D := by
  apply F.ext _ _ (isSet c) (isSet D)
  intro raw
  rw [hD]
  exact (cartMembersWithReturnBound c.val.factors F.emptyValue
    (fun i => Fin.elim0 i) raw).trans
      ⟨And.left, fun h => ⟨h, fun i => Fin.elim0 i⟩⟩

theorem tupleInCart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (c : Obj (M := M) (CartObj M n))
    (h : ∀ i, M.mem (t.val.values i) (c.val.factors i)) : In t c :=
  FiniteFunction.tuple_inCart _ _ h


/-- An ordered finite family of field carriers. Each tail can depend only on
members selected for the preceding fields. -/
inductive DependentFields (M : Semantics.{u}) : ℕ → Type u where
  | nil : DependentFields M 0
  | cons {n : ℕ} (carrier : M.Value) (rest : M.Value → DependentFields M n) :
      DependentFields M (n + 1)

namespace DependentFields

variable {M : Semantics.{u}}

def WellFormed : {n : ℕ} → DependentFields M n → Prop
  | _, .nil => True
  | _, .cons A rest => M.isSet A ∧ ∀ x, M.mem x A → WellFormed (rest x)

def Accepts : {n : ℕ} → DependentFields M n → (Fin n → M.Value) → Prop
  | _, .nil, _ => True
  | _, .cons A rest, v => M.mem (v 0) A ∧ Accepts (rest (v 0)) (Fin.tail v)

def factors : {n : ℕ} → DependentFields M n → (Fin n → M.Value) → Fin n → M.Value
  | _, .nil, _ => fun i => Fin.elim0 i
  | _, .cons A rest, v => Fin.cons A (factors (rest (v 0)) (Fin.tail v))

theorem accepts_iff {n : ℕ} (t : DependentFields M n) (v : Fin n → M.Value) :
    t.Accepts v ↔ ∀ i, M.mem (v i) (t.factors v i) := by
  induction t with
  | nil => exact ⟨fun _ i => Fin.elim0 i, fun _ => True.intro⟩
  | cons A rest ih =>
    constructor
    · rintro ⟨h, hs⟩ i
      exact Fin.cases h (fun j => (ih (v 0) (Fin.tail v)).mp hs j) i
    · intro h
      exact ⟨h 0, (ih (v 0) (Fin.tail v)).mpr (fun j => h j.succ)⟩

theorem factors_isSet {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed)
    (v : Fin n → M.Value) (hv : t.Accepts v) : ∀ i, M.isSet (t.factors v i) := by
  induction t with
  | nil => exact fun i => Fin.elim0 i
  | cons A rest ih =>
    exact Fin.cases ht.1 (ih (v 0) (ht.2 _ hv.1) (Fin.tail v) hv.2)

variable [F : FunctionSemantics M] [I : IndexedUnionSemantics M]

/-- Enumerate a finite telescope using set-indexed unions. The callback keeps
the existing flat tuple graph representation, including for more than two fields. -/
noncomputable def collect : {n : ℕ} → DependentFields M n →
    ((Fin n → M.Value) → M.Value) → M.Value
  | _, .nil, emit => F.insertValue (emit (fun i => Fin.elim0 i)) F.emptyValue
  | _, .cons A rest, emit => I.indexedUnionValue A
      (fun x => collect (rest x) (fun v => emit (Fin.cons x v)))

theorem collect_members {n : ℕ} (t : DependentFields M n) :
    ∀ (emit : (Fin n → M.Value) → M.Value) (p : M.Value),
      M.mem p (t.collect emit) ↔ ∃ v, t.Accepts v ∧ p = emit v := by
  induction t with
  | nil =>
    intro emit p
    constructor
    · intro hp
      rcases (F.insert_members _ _ _).mp hp with hp | hp
      · exact ⟨fun i => Fin.elim0 i, True.intro, hp⟩
      · exact (F.empty_members p hp).elim
    · rintro ⟨v, _, hp⟩
      have hv : v = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
      subst v
      exact (F.insert_members _ _ _).mpr (Or.inl hp)
  | cons A rest ih =>
    intro emit p
    change M.mem p (I.indexedUnionValue A _) ↔ _
    rw [I.indexedUnion_members]
    constructor
    · rintro ⟨x, hx, hp⟩
      obtain ⟨v, hv, hp⟩ := (ih x _ p).mp hp
      refine ⟨Fin.cons x v, ?_, hp⟩
      simpa only [Accepts, Fin.cons_zero, Fin.tail_cons] using And.intro hx hv
    · rintro ⟨v, hv, hp⟩
      refine ⟨v 0, hv.1, (ih (v 0) _ p).mpr ⟨Fin.tail v, hv.2, ?_⟩⟩
      simpa only [Fin.cons_self_tail] using hp

theorem collect_isSet {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed)
    (emit : (Fin n → M.Value) → M.Value)
    (he : ∀ v, t.Accepts v → M.isSet (emit v)) : M.isSet (t.collect emit) := by
  induction t with
  | nil => exact F.insert_isSet _ _ (he _ True.intro) F.empty_isSet
  | cons A rest ih =>
    apply I.indexedUnion_isSet _ _ ht.1
    intro x hx
    apply ih x (ht.2 x hx)
    intro v hv
    apply he (Fin.cons x v)
    simpa only [Accepts, Fin.cons_zero, Fin.tail_cons] using And.intro hx hv

noncomputable def value {n : ℕ} (t : DependentFields M n) : M.Value :=
  t.collect FiniteFunction.tupleValue

theorem value_isSet {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed) :
    M.isSet t.value :=
  t.collect_isSet ht _ (fun v _ => FiniteFunction.tuple_isSet v)

def coordinates {n : ℕ} (p : M.Value) : Fin n → M.Value :=
  fun i => F.callValue p (FiniteFunction.index i)

/-- Source coordinate literals and canonical finite indices have the same values.
The compiler supplies this finite certificate once for each dependent structure. -/
def numberedCoordinates {n : ℕ} (p : M.Value) (indices : Fin n → ℂ) : Fin n → M.Value :=
  fun i => F.callValue p (M.number (indices i))

omit I in
theorem numberedCoordinates_eq {n : ℕ} (p : M.Value) (indices : Fin n → ℂ)
    (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) :
    numberedCoordinates p indices = coordinates p := by
  funext i
  change F.callValue p (M.number (indices i)) = _
  rw [hi i]
  rfl

omit I in
theorem coordinates_tuple {n : ℕ} (v : Fin n → M.Value) :
    coordinates (FiniteFunction.tupleValue v) = v := by
  funext i
  exact FiniteFunction.call_tuple v i

theorem members_iff_cart {n : ℕ} (t : DependentFields M n) (p : M.Value) :
    M.mem p t.value ↔
      M.mem p (FiniteFunction.cartValue (t.factors (coordinates p))) := by
  constructor
  · intro hp
    obtain ⟨v, hv, rfl⟩ := (t.collect_members _ _).mp hp
    rw [coordinates_tuple]
    exact FiniteFunction.tuple_inCart v _ ((t.accepts_iff v).mp hv)
  · intro hp
    exact (t.collect_members _ _).mpr ⟨coordinates p,
      (t.accepts_iff _).mpr (FiniteFunction.coordinate_mem hp),
      FiniteFunction.reconstruct hp⟩

end DependentFields

structure DependentCartObj (M : Semantics.{u}) (n : ℕ) where
  fields : DependentFields M n

noncomputable instance dependentCartRepresentation {M : Semantics.{u}}
    [FunctionSemantics M] [IndexedUnionSemantics M] {n : ℕ} :
    Representation M (DependentCartObj M n) where
  wd c := c.fields.WellFormed
  denote c := c.fields.value
  wd_isSet {c} h := c.fields.value_isSet h

def dependentCart {M : Semantics.{u}} [FunctionSemantics M] [IndexedUnionSemantics M]
    {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed) :
    Obj (M := M) (DependentCartObj M n) := ⟨⟨t⟩, ht⟩

theorem tupleInDependentCart {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} (t : Obj (M := M) (TupleObj M n))
    (c : Obj (M := M) (DependentCartObj M n)) (h : c.val.fields.Accepts t.val.values) :
    In t c :=
  (c.val.fields.collect_members _ _).mpr ⟨t.val.values, h, rfl⟩

theorem inDependentCart_iff {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) :
    In p c ↔ M.mem (denote p) (FiniteFunction.cartValue
      (c.val.fields.factors (DependentFields.numberedCoordinates (denote p) indices))) := by
  rw [DependentFields.numberedCoordinates_eq _ _ hi]
  exact c.val.fields.members_iff_cart (denote p)

def dependentCartAt {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) (h : In p c) :
    Obj (M := M) (CartObj M n) :=
  cart (c.val.fields.factors (DependentFields.numberedCoordinates (denote p) indices))
    (c.val.fields.factors_isSet c.wd _ ((c.val.fields.accepts_iff _).mpr
      (by
        rw [DependentFields.numberedCoordinates_eq _ _ hi]
        exact FiniteFunction.coordinate_mem ((c.val.fields.members_iff_cart (denote p)).mp h))))

theorem inDependentCartAt {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) (h : In p c) :
    In p (dependentCartAt p c indices hi h) :=
  (inDependentCart_iff p c indices hi).mp h

/-- Reuse a carrier whose formation was checked by the structure declaration.
This is a projection of that certified family, not a fresh source constructor. -/
def dependentFieldCarrier {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) (h : In p c)
    (i : Fin n) : Obj (M := M) M.Value :=
  let bound := dependentCartAt p c indices hi h
  semanticObject (bound.val.factors i) (bound.wd i)

theorem tuple_coordinate_mem {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (c : Obj (M := M) (CartObj M n))
    (h : In t c) (i : Fin n) : M.mem (t.val.values i) (c.val.factors i) := by
  have hc : M.mem (FunctionSemantics.callValue (FiniteFunction.tupleValue t.val.values)
    (FiniteFunction.index i)) (c.val.factors i) := FiniteFunction.coordinate_mem h i
  simpa only [FiniteFunction.call_tuple] using hc

/-- A tuple's own values provide the singleton factors of its finite contract. -/
def tupleSingletonCart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) : Obj (M := M) (CartObj M n) :=
  cart (fun i => FiniteFunction.finiteSetValue [t.val.values i]) (by
    intro i
    apply FiniteFunction.finiteSet_isSet
    intro x hx
    have hx' : x = t.val.values i := List.mem_singleton.mp hx
    subst x
    exact t.wd i)

theorem tupleInSingletonCart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) : In t (tupleSingletonCart t) :=
  FiniteFunction.tuple_inCart _ _ (fun _ =>
    (FiniteFunction.finiteSet_members _ _).mpr (List.mem_singleton.mpr rfl))

theorem tuple_coordinate {M : Semantics.{u}} [F : FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (i : Fin n) :
    F.callValue (denote t) (FiniteFunction.index i) = t.val.values i :=
  FiniteFunction.call_tuple _ i

structure ClosedRangeObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  start : Obj (M := M) α
  finish : Obj (M := M) β

def ClosedRangeObj.condition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (r : ClosedRangeObj (M := M) α β) (value : M.Value) : Prop :=
  ∃ lower upper k : ℤ, denote r.start = M.number (lower : ℂ) ∧
    denote r.finish = M.number (upper : ℂ) ∧ value = M.number (k : ℂ) ∧
    lower ≤ k ∧ k ≤ upper

instance closedRangeRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (ClosedRangeObj (M := M) α β) where
  wd r := In r.start Z ∧ In r.finish Z
  denote r := S.sepValue (M.standard .integer) r.condition
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .integer)

def closedRange {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a Z) (hb : In b Z) :
    Obj (M := M) (ClosedRangeObj (M := M) α β) := ⟨⟨a, b⟩, ⟨ha, hb⟩⟩

theorem inClosedRange_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) :
    In p (closedRange a b ha hb) ↔
      ∃ lower upper k : ℤ, denote a = M.number (lower : ℂ) ∧
        denote b = M.number (upper : ℂ) ∧ denote p = M.number (k : ℂ) ∧
        lower ≤ k ∧ k ≤ upper := by
  change M.mem (denote p) (S.sepValue (M.standard .integer) _) ↔ _
  rw [S.sep_members]
  constructor
  · exact fun h => h.2
  · rintro ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩
    exact ⟨(M.integer_members _).mpr ⟨k, hp⟩, lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem inClosedRangeOfDenote {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) (lower upper k : ℤ)
    (hl : denote a = M.number (lower : ℂ))
    (hu : denote b = M.number (upper : ℂ))
    (hp : denote p = M.number (k : ℂ)) (hlo : lower ≤ k) (hhi : k ≤ upper) :
    In p (closedRange a b ha hb) :=
  (inClosedRange_iff a b p ha hb).mpr ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem numberInClosedRange {M : Semantics.{u}} [SetSemantics M]
    (lower upper k : ℤ) (hlo : lower ≤ k) (hhi : k ≤ upper) :
    In (number (M := M) (k : ℂ))
      (closedRange (number (lower : ℂ)) (number (upper : ℂ))
        (NativeBridge.numberInZ lower) (NativeBridge.numberInZ upper)) :=
  inClosedRangeOfDenote _ _ _ _ _ lower upper k rfl rfl rfl hlo hhi

theorem numberInClosedRangeOfEq {M : Semantics.{u}} [SetSemantics M]
    (a b p : ℂ) (lower upper k : ℤ)
    (ha : a = (lower : ℂ)) (hb : b = (upper : ℂ)) (hp : p = (k : ℂ))
    (hlo : lower ≤ k) (hhi : k ≤ upper) :
    In (number (M := M) p)
      (closedRange (number a) (number b)
        (NativeBridge.numberInZOfEq a lower ha) (NativeBridge.numberInZOfEq b upper hb)) :=
  inClosedRangeOfDenote _ _ _ _ _ lower upper k
    (congrArg M.number ha) (congrArg M.number hb) (congrArg M.number hp) hlo hhi

theorem closedRange_indexSet {M : Semantics.{u}} [F : FunctionSemantics M] (n : ℕ)
    (ha : In (number (M := M) 1) Z) (hb : In (number (M := M) (n : ℂ)) Z) :
    denote (closedRange (number (M := M) 1) (number (n : ℂ)) ha hb) =
      FiniteFunction.indexSet (M := M) n := by
  apply F.ext _ _ (isSet _) (FiniteFunction.indexSet_isSet n)
  intro value
  change M.mem value (F.sepValue (M.standard .integer) _) ↔ _
  rw [F.sep_members, FiniteFunction.indexSet_members]
  constructor
  · rintro ⟨_, lower, upper, k, hl, hu, hv, hlo, hhi⟩
    have hl' : lower = 1 := by
      change M.number 1 = M.number (lower : ℂ) at hl
      have h := M.number_injective hl
      exact_mod_cast h.symm
    have hu' : upper = (n : ℤ) := by
      change M.number (n : ℂ) = M.number (upper : ℂ) at hu
      have h := M.number_injective hu
      exact_mod_cast h.symm
    subst lower
    subst upper
    have hk0 : 0 ≤ k := le_trans (by norm_num) hlo
    have hk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    have hkn : k.toNat ≤ n := by exact_mod_cast (hk.symm ▸ hhi)
    have hkpos : 1 ≤ k.toNat := by exact_mod_cast (hk.symm ▸ hlo)
    let i : Fin n := ⟨k.toNat - 1, by omega⟩
    refine ⟨i, hv.trans ?_⟩
    unfold FiniteFunction.index
    apply congrArg M.number
    have hi : i.val + 1 = k.toNat := by dsimp [i]; omega
    rw [hi]
    exact_mod_cast hk.symm
  · rintro ⟨i, rfl⟩
    have hk : M.mem (FiniteFunction.index (M := M) i) (M.standard .integer) := by
      apply (M.integer_members _).mpr
      refine ⟨(i.val + 1 : ℕ), ?_⟩
      simp [FiniteFunction.index]
    refine ⟨hk, 1, (n : ℤ), ((i.val + 1 : ℕ) : ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · change M.number 1 = M.number ((1 : ℤ) : ℂ)
      norm_num
    · change M.number (n : ℂ) = M.number ((n : ℤ) : ℂ)
      norm_num
    · simp [FiniteFunction.index]
    · exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i.val))
    · exact_mod_cast (Nat.succ_le_of_lt i.isLt)


theorem indexSetMemberOfClosedRange {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] {p : Obj (M := M) α} {n : ℕ}
    {ha : In (number (M := M) 1) Z} {hb : In (number (M := M) (n : ℂ)) Z}
    (h : In p (closedRange (number (M := M) 1) (number (n : ℂ)) ha hb)) :
    M.mem (denote p) (FiniteFunction.indexSet n) := by
  change M.mem (denote p) (denote (closedRange _ _ ha hb)) at h
  rwa [closedRange_indexSet] at h

theorem indexSetMemberOfClosedRangeOfEq {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] {p : Obj (M := M) α} {n : ℕ}
    (z : ℂ) (hz : z = (n : ℂ))
    {ha : In (number (M := M) 1) Z} {hb : In (number (M := M) z) Z}
    (h : In p (closedRange (number (M := M) 1) (number z) ha hb)) :
    M.mem (denote p) (FiniteFunction.indexSet n) := by
  subst z
  exact indexSetMemberOfClosedRange h

structure UnionObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance unionRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (UnionObj (M := M) α β) where
  wd _ := True
  denote p := S.unionValue (denote p.left) (denote p.right)
  wd_isSet {p} _ := S.union_isSet _ _ (isSet p.left) (isSet p.right)

def union {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (UnionObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem inUnion_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ) :
    In a (union A B) ↔ In a A ∨ In a B := S.union_members _ _ _

structure PowerSetObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  bound : Obj (M := M) α

instance powerSetRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] : Representation M (PowerSetObj (M := M) α) where
  wd _ := True
  denote p := S.powerValue (denote p.bound)
  wd_isSet {p} _ := S.power_isSet _ (isSet p.bound)

def powerSet {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Obj (M := M) (PowerSetObj (M := M) α) := ⟨⟨A⟩, True.intro⟩

theorem inPowerSet_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : In A (powerSet B) ↔ Subset A B := by
  change M.mem (denote A) (S.powerValue (denote B)) ↔ _
  rw [S.power_members]
  exact ⟨fun h => h.2, fun h => ⟨isSet A, h⟩⟩


/-- A function signature records its exact checked domain and return set. -/
structure FunctionSignature (M : Semantics.{u}) where
  domain : M.Value
  domain_isSet : M.isSet domain
  output : M.Value
  output_isSet : M.isSet output

namespace FunctionSignature

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def ofDomain (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B) : FunctionSignature M :=
  ⟨D, hD, B, hB⟩

def withGuard (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B)
    (guard : M.Value → Prop) : FunctionSignature M :=
  ⟨F.sepValue D guard, F.sep_isSet D guard hD, B, hB⟩

theorem withGuard_domain (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B)
    (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (withGuard D B hD hB guard).domain ↔ M.mem x D ∧ guard x :=
  F.sep_members D guard x

def oneTarget (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) : FunctionSignature M :=
  withGuard (M.standard A) B (M.standard_isSet A) hB guard

noncomputable def twoTarget (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) : FunctionSignature M :=
  withGuard (FiniteFunction.cartValue ![M.standard A, M.standard E]) B
    (FiniteFunction.cart_isSet _ (by intro i; fin_cases i <;> exact M.standard_isSet _))
    hB (fun p => guard (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2)

def one (A B : StandardSetValue) (guard : M.Value → Prop) : FunctionSignature M :=
  oneTarget A (M.standard B) (M.standard_isSet B) guard

noncomputable def two (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop) :
    FunctionSignature M := twoTarget A E (M.standard B) (M.standard_isSet B) guard

def target (s : FunctionSignature M) : M.Value := s.output

theorem oneTarget_domain (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (oneTarget A B hB guard).domain ↔ M.mem x (M.standard A) ∧ guard x :=
  F.sep_members _ _ _

theorem twoTarget_domain (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) (a b : M.Value) :
    M.mem (FiniteFunction.pack2 a b) (twoTarget A E B hB guard).domain ↔
      M.mem a (M.standard A) ∧ M.mem b (M.standard E) ∧ guard a b := by
  change M.mem (FiniteFunction.pack2 a b)
    (F.sepValue (FiniteFunction.cartValue ![M.standard A, M.standard E]) _) ↔ _
  rw [F.sep_members]
  simp only [FiniteFunction.unpack_pack2]
  constructor
  · rintro ⟨h, hg⟩
    obtain ⟨x, hx, y, hy, hp⟩ := (FiniteFunction.cart2_members _ _ _).mp h
    obtain ⟨rfl, rfl⟩ := FiniteFunction.pack2_injective hp
    exact ⟨hx, hy, hg⟩
  · rintro ⟨ha, hb, hg⟩
    exact ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨a, ha, b, hb, rfl⟩, hg⟩

theorem one_domain (A B : StandardSetValue) (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (one A B guard).domain ↔ M.mem x (M.standard A) ∧ guard x :=
  oneTarget_domain A (M.standard B) (M.standard_isSet B) guard x

theorem two_domain (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (a b : M.Value) :
    M.mem (FiniteFunction.pack2 a b) (two A E B guard).domain ↔
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

/-- Finite sequences retain the source carrier and length objects. Their
complete domain is the one-based integer interval, with no extra guard. -/
structure FiniteSeqSetObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  carrier : Obj (M := M) α
  length : Obj (M := M) β

def finiteSeqDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (length : Obj (M := M) β) : M.Value :=
  F.sepValue (F.sepValue (M.standard .integer)
    (ClosedRangeObj.condition ⟨number 1, length⟩)) (fun _ => True)

theorem finiteSeqDomain_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (length : Obj (M := M) β) :
    M.isSet (finiteSeqDomain length) :=
  F.sep_isSet _ _ (F.sep_isSet _ _ (M.standard_isSet .integer))

instance finiteSeqSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (FiniteSeqSetObj (M := M) α β) where
  wd s := IsSet s.carrier ∧ In s.length N
  denote s := F.fnSetValue (finiteSeqDomain s.length) (denote s.carrier)
  wd_isSet {s} h := F.fnSet_isSet _ _ (finiteSeqDomain_isSet s.length) h.1

def finiteSeq {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (n : Obj (M := M) β) (hA : IsSet A) (hn : In n N) :
    Obj (M := M) (FiniteSeqSetObj (M := M) α β) := ⟨⟨A, n⟩, hA, hn⟩

def finiteSeqSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β)) : FunctionSignature M :=
  ⟨finiteSeqDomain s.val.length, finiteSeqDomain_isSet s.val.length,
    denote s.val.carrier, s.wd.1⟩

theorem finiteSeq_eq_fnSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β)) :
    Same s (fnSet (finiteSeqSignature s)) := rfl

/-- Injectivity compares semantic values on the requested domain. Callability
and the codomain are checked by the source fact's separate WD evidence. -/
def injectiveValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (A _B f : M.Value) : Prop :=
  ∀ x, M.mem x A → ∀ y, M.mem y A → F.callValue f x = F.callValue f y → x = y

def surjectiveValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f : M.Value) : Prop :=
  ∀ y, M.mem y B → ∃ x, M.mem x A ∧ y = F.callValue f x

def bijectiveValue {M : Semantics.{u}} [FunctionSemantics M]
    (A B f : M.Value) : Prop := injectiveValue A B f ∧ surjectiveValue A B f

theorem injectiveValue_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f : M.Value) : injectiveValue A B f ↔
    (∀ (x : Obj (M := M) M.Value), M.mem (denote x) A →
     ∀ (y : Obj (M := M) M.Value), M.mem (denote y) A →
       F.callValue f (denote x) = F.callValue f (denote y) → denote x = denote y) := by
  constructor
  · intro h x hx y hy eq
    exact h (denote x) hx (denote y) hy eq
  · intro h x hx y hy eq
    exact h (semanticObject x (M.member_isSet hx)) hx
      (semanticObject y (M.member_isSet hy)) hy eq

theorem surjectiveValue_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f : M.Value) : surjectiveValue A B f ↔
    (∀ (y : Obj (M := M) M.Value), M.mem (denote y) B →
      ∃ x : Obj (M := M) M.Value, ∃ (_hx : M.mem (denote x) A), denote y = F.callValue f (denote x)) := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, eq⟩ := h (denote y) hy
    exact ⟨semanticObject x (M.member_isSet hx), hx, eq⟩
  · intro h y hy
    obtain ⟨x, hx, eq⟩ := h (semanticObject y (M.member_isSet hy)) hy
    exact ⟨denote x, hx, eq⟩

theorem bijectiveValue_preimage {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f y : M.Value) (h : bijectiveValue A B f) (hy : M.mem y B) :
    (∃ x : Obj (M := M) M.Value, ∃ (_hx : M.mem (denote x) A), F.callValue f (denote x) = y) ∧
    (∀ (x : Obj (M := M) M.Value), M.mem (denote x) A →
     ∀ (z : Obj (M := M) M.Value), M.mem (denote z) A →
       F.callValue f (denote x) = y → F.callValue f (denote z) = y → denote x = denote z) := by
  constructor
  · obtain ⟨x, hx, eq⟩ := h.2 y hy
    exact ⟨semanticObject x (M.member_isSet hx), hx, eq.symm⟩
  · intro x hx z hz ex ez
    exact h.1 (denote x) hx (denote z) hz (ex.trans ez.symm)

/-- A checked Cartesian member retains its complete finite domain when its
return bound is changed using the supplied return proof. -/
theorem cartMemberInFnSetOfReturns {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] {n : ℕ}
    (f : Obj (M := M) α) (A : Obj (M := M) (CartObj M n))
    (s : FunctionSignature M) (hf : In f A)
    (hd : s.domain = FiniteFunction.indexSet n)
    (hr : ∀ x, M.mem x s.domain → M.mem (F.callValue (denote f) x) s.output) :
    In f (fnSet s) := by
  have graph : M.mem (denote f) (F.fnSetValue (FiniteFunction.indexSet n)
      (FiniteFunction.finiteUnionValue (List.ofFn A.val.factors))) :=
    ((F.sep_members _ _ _).mp hf).1
  rw [← hd] at graph
  exact F.fnSet_of_returns graph hr

theorem finiteSeqDomain_number {M : Semantics.{u}} [F : FunctionSemantics M] (n : ℕ) :
    finiteSeqDomain (number (M := M) (n : ℂ)) = FiniteFunction.indexSet n := by
  let interval := closedRange (number (M := M) 1) (number (n : ℂ))
    (NativeBridge.numberInZOfEq 1 1 (by norm_num)) (naturalToInteger _ (NativeBridge.numberInN n))
  have h : F.sepValue (denote interval) (fun _ => True) = denote interval := by
    apply F.ext _ _ (F.sep_isSet _ _ (isSet interval)) (isSet interval)
    intro x
    exact (F.sep_members _ _ x).trans ⟨And.left, fun h => ⟨h, True.intro⟩⟩
  exact h.trans (closedRange_indexSet n _ _)

theorem finiteSeqDomain_ofDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (length : Obj (M := M) β) (n : ℕ)
    (hn : denote length = M.number (n : ℂ)) :
    finiteSeqDomain length = FiniteFunction.indexSet n := by
  change F.sepValue (F.sepValue (M.standard .integer)
    (fun value => ∃ lower upper k : ℤ, M.number 1 = M.number (lower : ℂ) ∧
      denote length = M.number (upper : ℂ) ∧ value = M.number (k : ℂ) ∧
      lower ≤ k ∧ k ≤ upper)) (fun _ => True) = _
  rw [hn]
  exact finiteSeqDomain_number n

theorem denoteFiniteSeq {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β)) (n : ℕ)
    (hn : Same s.val.length (number (n : ℂ))) :
    denote s = F.fnSetValue (FiniteFunction.indexSet n) (denote s.val.carrier) :=
  congrArg (fun D => F.fnSetValue D (denote s.val.carrier))
    (finiteSeqDomain_ofDenote s.val.length n hn)

structure FunctionBranch (M : Semantics.{u}) where
  guard : M.Value → Prop
  body : M.Value → M.Value

noncomputable def piecewiseValue {M : Semantics.{u}} : List (FunctionBranch M) → M.Value → M.Value
  | [], _ => M.number 0
  | branch :: rest, x => by
      classical
      exact if branch.guard x then branch.body x else piecewiseValue rest x

theorem piecewiseValue_eq {M : Semantics.{u}} (branches : List (FunctionBranch M))
    (D : M.Value)
    (disjoint : branches.Pairwise (fun a b => ∀ x, M.mem x D → ¬ (a.guard x ∧ b.guard x)))
    (branch : FunctionBranch M) (member : branch ∈ branches)
    (x : M.Value) (hx : M.mem x D) (guard : branch.guard x) :
    piecewiseValue branches x = branch.body x := by
  classical
  induction branches with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨apart, tail⟩ := List.pairwise_cons.mp disjoint
      rcases List.mem_cons.mp member with rfl | member
      · exact if_pos guard
      · have no_first : ¬ first.guard x := fun h => apart branch member x hx ⟨h, guard⟩
        change (if first.guard x then first.body x else piecewiseValue rest x) = _
        rw [if_neg no_first]
        exact ih tail member

structure PiecewiseFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  branches : List (FunctionBranch M)

def PiecewiseFn.Valid {M : Semantics.{u}} (f : PiecewiseFn M) : Prop :=
  (∀ x, M.mem x f.signature.domain → ∃ b ∈ f.branches, b.guard x) ∧
  f.branches.Pairwise (fun a b => ∀ x, M.mem x f.signature.domain → ¬ (a.guard x ∧ b.guard x)) ∧
  (∀ b ∈ f.branches, ∀ x, M.mem x f.signature.domain → b.guard x → M.mem (b.body x) f.signature.output)

theorem PiecewiseFn.value_mem {M : Semantics.{u}} (f : PiecewiseFn M) (h : f.Valid)
    (x : M.Value) (hx : M.mem x f.signature.domain) :
    M.mem (piecewiseValue f.branches x) f.signature.output := by
  obtain ⟨b, hb, hg⟩ := h.1 x hx
  rw [piecewiseValue_eq f.branches f.signature.domain h.2.1 b hb x hx hg]
  exact h.2.2 b hb x hx hg

noncomputable instance piecewiseFnRepresentation {M : Semantics.{u}} [F : FunctionSemantics M] :
    Representation M (PiecewiseFn M) where
  wd := PiecewiseFn.Valid
  denote f := F.graphValue f.signature.domain f.signature.output (piecewiseValue f.branches)
  wd_isSet {f} h := M.member_isSet
    (FunctionSemantics.graph_inFnSet _ _ _ (f.value_mem h))

noncomputable def piecewiseFn {M : Semantics.{u}} [FunctionSemantics M]
    (signature : FunctionSignature M) (branches : List (FunctionBranch M))
    (h : (PiecewiseFn.mk signature branches).Valid) : Obj (M := M) (PiecewiseFn M) :=
  ⟨⟨signature, branches⟩, h⟩

theorem piecewiseFnInFnSet {M : Semantics.{u}} [FunctionSemantics M]
    (f : Obj (M := M) (PiecewiseFn M)) : In f (fnSet f.val.signature) :=
  FunctionSemantics.graph_inFnSet _ _ _ (f.val.value_mem f.wd)

theorem piecewiseFn_call_eq {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (PiecewiseFn M)) (branch : FunctionBranch M)
    (member : branch ∈ f.val.branches) (x : M.Value)
    (hx : M.mem x f.val.signature.domain) (guard : branch.guard x) :
    F.callValue (denote f) x = branch.body x := by
  have h := FunctionSemantics.call_graphValue f.val.signature.domain f.val.signature.output
    (piecewiseValue f.val.branches) (f.val.value_mem f.wd) x hx
  exact h.trans (piecewiseValue_eq _ _ f.wd.2.1 branch member x hx guard)

/-- A function specified by a unique output, with no formula body to unfold. -/
structure SelectedFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  property : M.Value → M.Value → Prop

/-- Move canonical Litex witnesses to semantic values; uniqueness still compares
denotations, never arbitrary host payloads. -/
theorem existsUniqueValueOfObjects {M : Semantics.{u}} (B : M.Value)
    (P : M.Value → Prop)
    (existsObject : ∃ y : Obj (M := M) M.Value, M.mem (denote y) B ∧ P (denote y))
    (uniqueObject : ∀ a b : Obj (M := M) M.Value,
      M.mem (denote a) B → M.mem (denote b) B → P (denote a) → P (denote b) → Same a b) :
    ∃! y, M.mem y B ∧ P y := by
  obtain ⟨y, hy, hp⟩ := existsObject
  refine ⟨denote y, ⟨hy, hp⟩, ?_⟩
  intro z hz
  exact uniqueObject (semanticObject z (M.member_isSet hz.1)) y hz.1 hy hz.2 hp

noncomputable def SelectedFn.value {M : Semantics.{u}}
    (f : SelectedFn M) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ y, M.mem y f.signature.output ∧ f.property x y then
    Classical.choose h
  else M.number 0

theorem SelectedFn.value_spec {M : Semantics.{u}} (f : SelectedFn M) (x : M.Value)
    (h : ∃! y, M.mem y f.signature.output ∧ f.property x y) :
    M.mem (f.value x) f.signature.output ∧ f.property x (f.value x) := by
  rw [SelectedFn.value, dif_pos h.exists]
  exact Classical.choose_spec h.exists

noncomputable instance selectedFnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] : Representation M (SelectedFn M) where
  wd f := ∀ x, M.mem x f.signature.domain →
    ∃! y, M.mem y f.signature.output ∧ f.property x y
  denote f := F.graphValue f.signature.domain f.signature.output f.value
  wd_isSet h := M.member_isSet
    (FunctionSemantics.graph_inFnSet _ _ _ (fun x hx =>
      (SelectedFn.value_spec _ x (h x hx)).1))

noncomputable def selectedFn {M : Semantics.{u}} [FunctionSemantics M]
    (s : FunctionSignature M) (property : M.Value → M.Value → Prop)
    (h : ∀ x, M.mem x s.domain → ∃! y, M.mem y s.output ∧ property x y) :
    Obj (M := M) (SelectedFn M) := ⟨⟨s, property⟩, h⟩

theorem selectedFnInFnSet {M : Semantics.{u}} [FunctionSemantics M]
    (f : Obj (M := M) (SelectedFn M)) : In f (fnSet f.val.signature) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun x hx =>
    (SelectedFn.value_spec f.val x (f.wd x hx)).1)

theorem selectedFn_call_spec {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (SelectedFn M)) (x : M.Value)
    (hx : M.mem x f.val.signature.domain) :
    M.mem (F.callValue (denote f) x) f.val.signature.output ∧
      f.val.property x (F.callValue (denote f) x) := by
  have value_eq : F.callValue (denote f) x = f.val.value x :=
    FunctionSemantics.call_graphValue _ _ _
      (fun x hx => (SelectedFn.value_spec f.val x (f.wd x hx)).1) x hx
  rw [value_eq]
  exact SelectedFn.value_spec f.val x (f.wd x hx)

theorem selectedFn_unique {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (SelectedFn M)) (x y : M.Value)
    (hx : M.mem x f.val.signature.domain)
    (hy : M.mem y f.val.signature.output ∧ f.val.property x y) :
    y = F.callValue (denote f) x :=
  (f.wd x hx).unique hy (selectedFn_call_spec f x hx)

theorem selectedFn_proofIndependent {M : Semantics.{u}} [FunctionSemantics M]
    (s : FunctionSignature M) (property : M.Value → M.Value → Prop)
    (h k : ∀ x, M.mem x s.domain → ∃! y, M.mem y s.output ∧ property x y) :
    Same (selectedFn s property h) (selectedFn s property k) := rfl

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
  let interpretation := fun p => body (FiniteFunction.unpack2 p).1
    (FiniteFunction.unpack2 p).2
  refine ⟨⟨s, interpretation⟩, ?_⟩
  intro p hp
  obtain ⟨hproduct, hg⟩ := (F.sep_members
    (FiniteFunction.cartValue ![M.standard A, M.standard E])
    (fun p => guard (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2) p).mp hp
  obtain ⟨x, hx, y, hy, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp hproduct
  change M.mem (body _ _) B
  simpa only [FiniteFunction.unpack_pack2] using hReturn x y hx hy
    (by simpa only [s, FunctionSignature.twoTarget, FiniteFunction.unpack_pack2] using hg)

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

def formulaFnOn {M : Semantics.{u}} [FunctionSemantics M]
    (signature : FunctionSignature M) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x signature.domain → M.mem (body x) signature.output) :
    Obj (M := M) (FormulaFn M) := ⟨⟨signature, body⟩, hReturn⟩

structure FamilyUnionObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  family : Obj (M := M) α

instance familyUnionRepresentation {M : Semantics.{u}} [I : IndexedUnionSemantics M]
    {α : Type v} [Representation M α] : Representation M (FamilyUnionObj (M := M) α) where
  wd _ := True
  denote p := I.indexedUnionValue (denote p.family) id
  wd_isSet {p} _ := I.indexedUnion_isSet _ _ (isSet p.family) (fun _ h => M.member_isSet h)

def familyUnion {M : Semantics.{u}} [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Obj (M := M) (FamilyUnionObj (M := M) α) := ⟨⟨A⟩, True.intro⟩

theorem familyUnion_members {M : Semantics.{u}} [I : IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (x : M.Value) :
    M.mem x (denote (familyUnion A)) ↔ ∃ a, M.mem a (denote A) ∧ M.mem x a :=
  I.indexedUnion_members _ _ _

def IsChoiceFunctionFor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (index : Obj (M := M) α) (_set : Obj (M := M) β)
    (family : Obj (M := M) γ) (choice : Obj (M := M) δ) : Prop :=
  ∀ x, M.mem x (denote index) →
    M.mem (F.callValue (denote choice) x) (F.callValue (denote family) x)

theorem choiceForIdentity {M : Semantics.{u}} [F : FunctionSemantics M] [IndexedUnionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (S : Obj (M := M) α) (g : Obj (M := M) β)
    (hg : ∀ x, M.mem x (denote S) → F.callValue (denote g) x = x)
    (hS : ∀ a : Obj (M := M) M.Value, In a S → IsNonempty a) :
    ∃ f : Obj (M := M) M.Value,
      ∃ (_ : In f (fnSet (FunctionSignature.withGuard (denote S) (denote (familyUnion S))
        (isSet S) (isSet (familyUnion S)) (fun _ => True)))), IsChoiceFunctionFor S S g f := by
  classical
  let select := fun x : M.Value => if h : ∃ y, M.mem y x then Classical.choose h else F.emptyValue
  have selected : ∀ x, M.mem x (denote S) → M.mem (select x) x := by
    intro x hx
    have h := hS (semanticObject x (M.member_isSet hx)) hx
    change ∃ y, M.mem y x at h
    dsimp only [select]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hreturn : ∀ x, M.mem x (denote S) → M.mem (select x) (denote (familyUnion S)) := by
    intro x hx
    exact (familyUnion_members S _).mpr ⟨x, hx, selected x hx⟩
  let D := F.sepValue (denote S) (fun _ => True)
  have hreturnD : ∀ x, M.mem x D → M.mem (select x) (denote (familyUnion S)) := by
    intro x hx
    exact hreturn x ((F.sep_members _ _ _).mp hx).1
  let value := F.graphValue D (denote (familyUnion S)) select
  have hvalue := FunctionSemantics.graph_inFnSet _ _ _ hreturnD
  let f := semanticObject value (M.member_isSet hvalue)
  refine ⟨f, hvalue, ?_⟩
  intro x hx
  change M.mem (F.callValue value x) (F.callValue (denote g) x)
  have hxD : M.mem x D := (F.sep_members _ _ _).mpr ⟨hx, True.intro⟩
  rw [hg x hx, FunctionSemantics.call_graphValue _ _ _ hreturnD x hxD]
  exact selected x hx

theorem formulaIdentityCall {M : Semantics.{u}} [F : FunctionSemantics M]
    (g : Obj (M := M) (FormulaFn M)) (hg : ∀ x, g.val.bodyValue x = x)
    (x : M.Value) (hx : M.mem x g.val.signature.domain) : F.callValue (denote g) x = x :=
  (FunctionSemantics.call_graphValue _ _ _ g.wd x hx).trans (hg x)


theorem zornMaximal {M : Semantics.{u}} [F : SetSemantics M]
    {α : Type v} [Representation M α] (S : Obj (M := M) α) (r : M.Value → M.Value → Prop)
    (hrefl : ∀ x, M.mem x (denote S) → r x x)
    (htrans : ∀ x y z, M.mem x (denote S) → M.mem y (denote S) → M.mem z (denote S) → r x y → r y z → r x z)
    (hanti : ∀ x y, M.mem x (denote S) → M.mem y (denote S) → r x y → r y x → x = y)
    (hbound : ∀ c : Obj (M := M) M.Value, In c (powerSet S) →
      (∀ x y, M.mem x (denote c) → M.mem y (denote c) → r x y ∨ r y x) →
      ∃ b, M.mem b (denote S) ∧ ∀ x, M.mem x (denote c) → r x b) :
    ∃ m : Obj (M := M) M.Value, ∃ (_ : In m S),
      ∀ x, M.mem x (denote S) → r (denote m) x → x = denote m := by
  classical
  let A := {x : M.Value // M.mem x (denote S)}
  have bounded : ∀ c : Set A, IsChain (fun x y : A => r x.val y.val) c →
      ∃ b : A, ∀ a ∈ c, r a.val b.val := by
    intro c hc
    let C := F.sepValue (denote S) (fun x => ∃ hx, (⟨x, hx⟩ : A) ∈ c)
    let Cobj := semanticObject C (F.sep_isSet _ _ (isSet S))
    have cmem : In Cobj (powerSet S) := by
      apply (F.power_members _ _).mpr
      exact ⟨isSet Cobj, fun x hx => ((F.sep_members _ _ _).mp hx).1⟩
    obtain ⟨b, hb, hub⟩ := hbound Cobj cmem (by
      intro x y hx hy
      obtain ⟨hxS, hxC⟩ := (F.sep_members _ _ _).mp hx
      obtain ⟨hyS, hyC⟩ := (F.sep_members _ _ _).mp hy
      obtain ⟨_, hxC⟩ := hxC
      obtain ⟨_, hyC⟩ := hyC
      by_cases heq : x = y
      · exact Or.inl (heq ▸ hrefl x hxS)
      · exact hc hxC hyC (fun h => heq (congrArg Subtype.val h)))
    refine ⟨⟨b, hb⟩, ?_⟩
    intro a ha
    apply hub a.val
    exact (F.sep_members _ _ _).mpr ⟨a.property, a.property, ha⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded bounded
    (fun {a b c : A} hab hbc => htrans a.val b.val c.val a.property b.property c.property hab hbc)
  refine ⟨semanticObject m.val (M.member_isSet m.property), m.property, ?_⟩
  intro x hx hmx
  exact hanti x m.val hx m.property (hm ⟨x, hx⟩ hmx) hmx


structure CallOnObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  signature : FunctionSignature M
  function : Obj (M := M) α
  argument : Obj (M := M) β

instance callOnRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CallOnObj (M := M) α β) where
  wd c := In c.function (fnSet c.signature) ∧ M.mem (denote c.argument) c.signature.domain
  denote c := F.callValue (denote c.function) (denote c.argument)
  wd_isSet h := M.member_isSet (FunctionSemantics.call_mem _ _ _ _ h.1 h.2)

def callOn {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (signature : FunctionSignature M) (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet signature)) (ha : M.mem (denote a) signature.domain) :
    Obj (M := M) (CallOnObj (M := M) α β) := ⟨⟨signature, f, a⟩, hf, ha⟩

/-- Use the original base-domain and guard proofs for the same guarded call. -/
def callOnDomain {M : Semantics.{u}} [FunctionSemantics M]
    {δ : Type v} {ε : Type w} {α : Type x} {β : Type t}
    [Representation M δ] [Representation M ε]
    [Representation M α] [Representation M β]
    (D : Obj (M := M) δ) (O : Obj (M := M) ε)
    (guard : M.Value → Prop) (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet (FunctionSignature.withGuard
      (denote D) (denote O) (isSet D) (isSet O) guard)))
    (ha : In a D) (hg : guard (denote a)) :
    Obj (M := M) (CallOnObj (M := M) α β) :=
  callOn (FunctionSignature.withGuard
    (denote D) (denote O) (isSet D) (isSet O) guard) f a hf
    ((FunctionSignature.withGuard_domain
      (denote D) (denote O) (isSet D) (isSet O) guard (denote a)).mpr ⟨ha, hg⟩)

theorem callOnInOutput {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallOnObj (M := M) α β)) :
    In c (semanticObject c.val.signature.output c.val.signature.output_isSet) :=
  FunctionSemantics.call_mem _ _ _ _ c.wd.1 c.wd.2

/-- Complete equal domains and equal calls identify the graphs. Return upper
bounds may differ, so they are retained independently for the two functions. -/
theorem functionExtOnDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (g : Obj (M := M) β)
    (s t : FunctionSignature M) (hf : In f (fnSet s)) (hg : In g (fnSet t))
    (hD : s.domain = t.domain)
    (h : ∀ x, M.mem x s.domain → F.callValue (denote f) x = F.callValue (denote g) x) :
    Same f g := by
  have hfg := (F.fnSet_members _ _ _).mp hf
  have hgg := (F.fnSet_members _ _ _).mp hg
  apply F.ext _ _ (isSet f) (isSet g)
  intro edge
  constructor
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := hfg.1 edge he
    have hy := (FiniteFunction.graph_pair_value hfg he).2
    rw [hy, h x hx]
    exact F.call_graph _ _ _ _ hgg (hD ▸ hx)
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := hgg.1 edge he
    have hy := (FiniteFunction.graph_pair_value hgg he).2
    have hx' : M.mem x s.domain := hD.symm ▸ hx
    rw [hy, ← h x hx']
    exact F.call_graph _ _ _ _ hfg hx'

/-- A Cartesian membership supplies the complete finite function contract. -/
def cartCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] {n : ℕ}
    (p : Obj (M := M) α) (c : Obj (M := M) (CartObj M n)) (a : Obj (M := M) β)
    (hp : In p c) (ha : M.mem (denote a) (FiniteFunction.indexSet n)) :
    Obj (M := M) (CallOnObj (M := M) α β) :=
  let signature := FunctionSignature.ofDomain (FiniteFunction.indexSet n)
    (FiniteFunction.finiteUnionValue (List.ofFn c.val.factors))
    (FiniteFunction.indexSet_isSet n)
    (FiniteFunction.finiteUnion_isSet _ (by
      intro A hA
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      exact c.wd i))
  callOn signature p a ((F.fnSet_members _ _ _).mpr
    ((FiniteFunction.cart_members _ _).mp hp).1) ha

theorem callOnCongr {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (c : Obj (M := M) (CallOnObj (M := M) α β))
    (d : Obj (M := M) (CallOnObj (M := M) γ δ))
    (hf : Same c.val.function d.val.function) (ha : Same c.val.argument d.val.argument) :
    Same c d := congrArg₂ F.callValue hf ha

theorem callFormulaOn_denote {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (signature : FunctionSignature M) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x signature.domain → M.mem (body x) signature.output)
    (a : Obj (M := M) α) (ha : M.mem (denote a) signature.domain) :
    denote (callOn signature (formulaFnOn signature body hReturn) a
      (formulaFnInFnSet _) ha) = body (denote a) :=
  FunctionSemantics.call_graphValue _ _ _ hReturn _ ha

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
  denote c := F.callValue (denote c.function) (FiniteFunction.pack2 (denote c.first) (denote c.second))
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
    Same c d := congrArg₂ F.callValue hf (congrArg₂ FiniteFunction.pack2 ha hb)

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
    (FiniteFunction.pack2 (denote a) (denote b))
    ((FunctionSignature.twoTarget_domain A E B hB guard _ _).mpr ⟨ha, hb, hg⟩)
  change F.callValue (F.graphValue (FunctionSignature.twoTarget A E B hB guard).domain
    (FunctionSignature.twoTarget A E B hB guard).target (fun p => body
      (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))
    (FiniteFunction.pack2 (denote a) (denote b)) = body (denote a) (denote b)
  simpa only [formulaFn2Target, FiniteFunction.unpack_pack2] using h

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
    (FiniteFunction.pack2 (denote a) (denote b))
    ((FunctionSignature.two_domain A E B guard _ _).mpr ⟨ha, hb, hg⟩)
  change F.callValue (F.graphValue (FunctionSignature.two A E B guard).domain
    (FunctionSignature.two A E B guard).target (fun p => body (FiniteFunction.unpack2 p).1
      (FiniteFunction.unpack2 p).2))
    (FiniteFunction.pack2 (denote a) (denote b)) = body (denote a) (denote b)
  simpa only [formulaFn2, formulaFn2Target, FunctionSignature.two,
    FiniteFunction.unpack_pack2] using h

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

theorem addPositiveLeft {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Lt (number 0) a) (hb : Le (number 0) b) : Lt (number 0) (add a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfPositive a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfNonnegative b hb
  refine NativeBridge.ltOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_pos_of_pos_of_nonneg hposR hposS)
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

theorem mulStructuralLtLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorPositive : Lt (number 0) lhs.val.left)
    (hOperandsLt : Lt lhs.val.right rhs.val.right)
    (hFactorSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive lhs.val.left hFactorPositive
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLt
  refine NativeBridge.ltOfDenoteReal lhs rhs (c * a) (c * b) ?_ ?_ (mul_lt_mul_of_pos_left hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hFactorSame.symm.trans hc, hb, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLtRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorPositive : Lt (number 0) lhs.val.right)
    (hOperandsLt : Lt lhs.val.left rhs.val.left)
    (hFactorSame : Same lhs.val.right rhs.val.right) : Lt lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive lhs.val.right hFactorPositive
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLt
  refine NativeBridge.ltOfDenoteReal lhs rhs (a * c) (b * c) ?_ ?_ (mul_lt_mul_of_pos_right hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [ha, hc, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hb, hFactorSame.symm.trans hc, M.mul_numbers, Complex.ofReal_mul]

theorem mulMinusOneNegativeLeft {M : Semantics.{u}} {α β : Type*}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (hFactor : denote p.val.left = M.number (-1))
    (hPositive : Lt (number 0) p.val.right) : Lt p (number 0) := by
  obtain ⟨a, ha, ha0⟩ := NativeBridge.realWitnessOfPositive p.val.right hPositive
  refine NativeBridge.ltOfDenoteReal p (number 0) ((-1) * a) 0 ?_ rfl ?_
  · change M.mulValue (denote p.val.left) (denote p.val.right) = _
    rw [hFactor, ha, M.mul_numbers, Complex.ofReal_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
  · simpa only [neg_one_mul] using neg_neg_of_pos ha0

theorem mulMinusOneNegativeRight {M : Semantics.{u}} {α β : Type*}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (hFactor : denote p.val.right = M.number (-1))
    (hPositive : Lt (number 0) p.val.left) : Lt p (number 0) := by
  obtain ⟨a, ha, ha0⟩ := NativeBridge.realWitnessOfPositive p.val.left hPositive
  refine NativeBridge.ltOfDenoteReal p (number 0) (a * (-1)) 0 ?_ rfl ?_
  · change M.mulValue (denote p.val.left) (denote p.val.right) = _
    rw [hFactor, ha, M.mul_numbers, Complex.ofReal_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
  · simpa only [mul_neg_one] using neg_neg_of_pos ha0

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

namespace Litex

/-- The denotation chooses one original value; WD does not choose the meaning. -/
noncomputable def minMaxValue {M : Semantics.{u}} (maximum : Bool)
    (a b : M.Value) : M.Value := by
  classical
  exact if (∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s)
    then (if maximum then b else a) else (if maximum then a else b)

theorem minMaxValue_number {M : Semantics.{u}} (maximum : Bool) (r s : ℝ) :
    minMaxValue maximum (M.number (r : ℂ)) (M.number (s : ℂ)) =
      M.number ((if maximum then Max.max r s else Min.min r s : ℝ) : ℂ) := by
  classical
  have iff_le : (∃ x y : ℝ, M.number (r : ℂ) = M.number (x : ℂ) ∧
      M.number (s : ℂ) = M.number (y : ℂ) ∧ x ≤ y) ↔ r ≤ s := by
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      have hr := Complex.ofReal_injective (M.number_injective hx)
      have hs := Complex.ofReal_injective (M.number_injective hy)
      exact hr.symm ▸ hs.symm ▸ hxy
    · intro h; exact ⟨r, s, rfl, rfl, h⟩
  unfold minMaxValue
  simp only [iff_le]
  cases maximum <;> by_cases h : r ≤ s
  · simp only [h, if_true, Bool.false_eq_true, if_false, min_eq_left h]
  · simp only [h, if_false, Bool.false_eq_true, min_eq_right (le_of_not_ge h)]
  · simp only [h, if_true, max_eq_right h]
  · simp only [h, if_false, if_true, max_eq_left (le_of_not_ge h)]

structure MinMaxObj {M : Semantics.{u}} (maximum : Bool)
    (α : Type v) (β : Type w) [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

noncomputable instance minMaxRepresentation {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MinMaxObj (M := M) maximum α β) where
  wd p := In p.left R ∧ In p.right R
  denote p := minMaxValue maximum (denote p.left) (denote p.right)
  wd_isSet {p} _ := by
    classical
    unfold minMaxValue
    split <;> cases maximum <;> first | exact isSet p.left | exact isSet p.right

noncomputable def min {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) : Obj (M := M) (MinMaxObj (M := M) false α β) :=
  ⟨⟨a, b⟩, ha, hb⟩

noncomputable def max {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) : Obj (M := M) (MinMaxObj (M := M) true α β) :=
  ⟨⟨a, b⟩, ha, hb⟩

theorem minMaxMember {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β)) (A : Obj (M := M) γ)
    (ha : In p.val.left A) (hb : In p.val.right A) : In p A := by
  classical
  change M.mem (minMaxValue maximum (denote p.val.left) (denote p.val.right)) (denote A)
  unfold minMaxValue
  split <;> cases maximum <;> first | exact ha | exact hb

theorem minMaxIdempotent {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β))
    (h : Same p.val.left p.val.right) : Same p p.val.left := by
  classical
  change minMaxValue maximum (denote p.val.left) (denote p.val.right) = denote p.val.left
  change denote p.val.left = denote p.val.right at h
  rw [← h]
  unfold minMaxValue
  split <;> cases maximum <;> rfl

theorem minMaxCommutative {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β))
    (q : Obj (M := M) (MinMaxObj (M := M) maximum γ δ))
    (h₁ : Same p.val.left q.val.right) (h₂ : Same p.val.right q.val.left) : Same p q := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2
  change denote p.val.left = denote q.val.right at h₁
  change denote p.val.right = denote q.val.left at h₂
  change minMaxValue maximum (denote p.val.left) (denote p.val.right) =
    minMaxValue maximum (denote q.val.left) (denote q.val.right)
  rw [← h₁, ← h₂, hr, hs, minMaxValue_number, minMaxValue_number]
  cases maximum
  · exact congrArg (fun x : ℝ => M.number (x : ℂ)) (min_comm r s)
  · exact congrArg (fun x : ℝ => M.number (x : ℂ)) (max_comm r s)

end Litex

namespace Litex

theorem minMaxDenoteReal {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β)) (r s : ℝ)
    (hr : denote p.val.left = M.number (r : ℂ))
    (hs : denote p.val.right = M.number (s : ℂ)) :
    denote p = M.number ((if maximum then Max.max r s else Min.min r s : ℝ) : ℂ) := by
  change minMaxValue maximum (denote p.val.left) (denote p.val.right) = _
  rw [hr, hs, minMaxValue_number]

theorem minLeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) false α β)) :
    Le p p.val.left ∧ Le p p.val.right := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2
  have hp : denote p = M.number ((Min.min r s : ℝ) : ℂ) := minMaxDenoteReal p r s hr hs
  exact ⟨⟨_, _, hp, hr, min_le_left r s⟩, ⟨_, _, hp, hs, min_le_right r s⟩⟩

theorem operandsLeMax {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) true α β)) :
    Le p.val.left p ∧ Le p.val.right p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2
  have hp : denote p = M.number ((Max.max r s : ℝ) : ℂ) := minMaxDenoteReal p r s hr hs
  exact ⟨⟨_, _, hr, hp, le_max_left r s⟩, ⟨_, _, hs, hp, le_max_right r s⟩⟩

theorem minOfLeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) false α β))
    (h : Le p.val.left p.val.right) : Same p p.val.left := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  change minMaxValue false (denote p.val.left) (denote p.val.right) = denote p.val.left
  rw [ha, hb, minMaxValue_number]
  simp only [Bool.false_eq_true, if_false, min_eq_left hab]

theorem minOfGeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) false α β))
    (h : Le p.val.right p.val.left) : Same p p.val.right := by
  obtain ⟨b, a, hb, ha, hba⟩ := h
  change minMaxValue false (denote p.val.left) (denote p.val.right) = denote p.val.right
  rw [ha, hb, minMaxValue_number]
  simp only [Bool.false_eq_true, if_false, min_eq_right hba]

theorem maxOfLeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) true α β))
    (h : Le p.val.left p.val.right) : Same p p.val.right := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  change minMaxValue true (denote p.val.left) (denote p.val.right) = denote p.val.right
  rw [ha, hb, minMaxValue_number]
  simp only [if_true, max_eq_right hab]

theorem maxOfGeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) true α β))
    (h : Le p.val.right p.val.left) : Same p p.val.left := by
  obtain ⟨b, a, hb, ha, hba⟩ := h
  change minMaxValue true (denote p.val.left) (denote p.val.right) = denote p.val.left
  rw [ha, hb, minMaxValue_number]
  simp only [if_true, max_eq_left hba]

theorem minMaxMonotone {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β))
    (q : Obj (M := M) (MinMaxObj (M := M) maximum γ δ))
    (ha : Le p.val.left q.val.left) (hb : Le p.val.right q.val.right) : Le p q := by
  obtain ⟨a, c, ha, hc, hac⟩ := ha
  obtain ⟨b, d, hb, hd, hbd⟩ := hb
  refine ⟨_, _, minMaxDenoteReal p a b ha hb, minMaxDenoteReal q c d hc hd, ?_⟩
  cases maximum
  · exact min_le_min hac hbd
  · exact max_le_max hac hbd

end Litex

namespace Litex

/-- The native real sign, observed through the fixed numeric embedding. -/
noncomputable def signValue {M : Semantics.{u}} (a : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, a = M.number (r : ℂ)
    then M.number ((Real.sign (Classical.choose h) : ℝ) : ℂ)
    else M.number 0

theorem signValue_number {M : Semantics.{u}} (r : ℝ) :
    signValue (M.number (r : ℂ)) = M.number ((Real.sign r : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold signValue
  rw [dif_pos h, hr]

structure SignObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance signRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SignObj (M := M) α) where
  wd p := In p.arg R
  denote p := signValue (denote p.arg)
  wd_isSet {p} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sign r, by
      rw [hr, signValue_number]⟩)

noncomputable def sign {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a R) : Obj (M := M) (SignObj (M := M) α) :=
  ⟨⟨a⟩, h⟩

theorem signDenoteReal {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.sign r : ℝ) : ℂ) := by
  change signValue (denote p.val.arg) = _
  rw [hr, signValue_number]

/-- A real number and its sign vanish together. -/
theorem signZeroIffArgZero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (haR : In p.val.arg R) :
    Same p (number 0) ↔ Same p.val.arg (number 0) := by
  let r := NativeBridge.asReal p.val.arg haR
  have hr : denote p.val.arg = M.number ((r : ℝ) : ℂ) := NativeBridge.asReal_spec p.val.arg haR
  have hp : denote p = M.number ((Real.sign r : ℝ) : ℂ) := signDenoteReal p r hr
  constructor
  · intro h
    have hs : Real.sign r = 0 := by
      have hc : ((Real.sign r : ℝ) : ℂ) = 0 := M.number_injective (hp.symm.trans h)
      exact_mod_cast hc
    have h0 : r = 0 := Real.sign_eq_zero_iff.mp hs
    change denote p.val.arg = M.number 0
    exact hr.trans (congrArg M.number (by exact_mod_cast h0))
  · intro h
    have h0 : r = 0 := by
      have hc : (r : ℂ) = 0 := M.number_injective (hr.symm.trans h)
      exact_mod_cast hc
    have hs : Real.sign r = 0 := Real.sign_eq_zero_iff.mpr h0
    change denote p = M.number 0
    exact hp.trans (congrArg M.number (by exact_mod_cast hs))

theorem signInZ {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) : In p Z := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  have hp := signDenoteReal p r hr
  rcases Real.sign_apply_eq r with hn | hz | ho
  · exact (M.integer_members _).mpr ⟨-1, by rw [hp, hn]; norm_num⟩
  · exact (M.integer_members _).mpr ⟨0, by rw [hp, hz]; norm_num⟩
  · exact (M.integer_members _).mpr ⟨1, by rw [hp, ho]; norm_num⟩

theorem signOfPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α))
    (h : Lt (number 0) p.val.arg) : Same p (number 1) := by
  obtain ⟨r, hr, hpos⟩ := NativeBridge.realWitnessOfPositive p.val.arg h
  change denote p = M.number 1
  rw [signDenoteReal p r hr, Real.sign_of_pos hpos, Complex.ofReal_one]

theorem signOfNegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α))
    (h : Lt p.val.arg (number 0)) : Same p (number (-1)) := by
  obtain ⟨r, z, hr, hz, hneg⟩ := h
  change M.number 0 = M.number (z : ℂ) at hz
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  subst z
  change denote p = M.number (-1)
  rw [signDenoteReal p r hr, Real.sign_of_neg hneg, Complex.ofReal_neg, Complex.ofReal_one]

theorem realSignMul (a b : ℝ) : Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · rw [Real.sign_of_neg ha, Real.sign_of_neg hb,
        Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb)]
      norm_num
    · rw [mul_zero, Real.sign_zero, mul_zero]
    · rw [Real.sign_of_neg ha, Real.sign_of_pos hb,
        Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb), mul_one]
  · rw [zero_mul, Real.sign_zero, zero_mul]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · rw [Real.sign_of_pos ha, Real.sign_of_neg hb,
        Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb), one_mul]
    · rw [mul_zero, Real.sign_zero, mul_zero]
    · rw [Real.sign_of_pos ha, Real.sign_of_pos hb,
        Real.sign_of_pos (mul_pos ha hb), one_mul]

theorem realSignMulAbs (a : ℝ) : Real.sign a * |a| = a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha, neg_one_mul, neg_neg]
  · rw [Real.sign_zero, zero_mul]
  · rw [Real.sign_of_pos ha, abs_of_pos ha, one_mul]

theorem realAbsEqSignMul (a : ℝ) : |a| = Real.sign a * a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha, neg_one_mul]
  · rw [Real.sign_zero, zero_mul, abs_zero]
  · rw [Real.sign_of_pos ha, abs_of_pos ha, one_mul]

theorem signNegation {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) :
    signValue (M.negValue (denote p.val.arg)) = M.negValue (denote p) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  simp only [signDenoteReal p r hr, hr, M.neg_numbers, ← Complex.ofReal_neg,
    signValue_number, Real.sign_neg]

theorem signProduct {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SignObj (M := M) α))
    (q : Obj (M := M) (SignObj (M := M) β)) (reverseArgs : Bool) :
    signValue (if reverseArgs then M.mulValue (denote q.val.arg) (denote p.val.arg)
      else M.mulValue (denote p.val.arg) (denote q.val.arg)) =
      M.mulValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd
  rw [signDenoteReal p a ha, signDenoteReal q b hb, ha, hb]
  cases reverseArgs <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, signValue_number, realSignMul, mul_comm]

theorem signTimesAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (signFirst : Bool) :
    (if signFirst then M.mulValue (denote p) (absValue (denote p.val.arg))
      else M.mulValue (absValue (denote p.val.arg)) (denote p)) = denote p.val.arg := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  rw [signDenoteReal p a ha, ha, absValue_number]
  cases signFirst <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, mul_comm (|a|) (Real.sign a), realSignMulAbs]

theorem absEqualsSignTimes {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (signFirst : Bool) :
    absValue (denote p.val.arg) =
      (if signFirst then M.mulValue (denote p) (denote p.val.arg)
        else M.mulValue (denote p.val.arg) (denote p)) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  rw [signDenoteReal p a ha, ha, absValue_number]
  cases signFirst <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, mul_comm a (Real.sign a), ← realAbsEqSignMul]

theorem zeroSubValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) :
    M.subValue (M.number 0) (denote a) = M.negValue (denote a) := by
  obtain ⟨z, hz⟩ := (M.complex_members _).mp ha
  rw [hz, M.sub_numbers, M.neg_numbers, zero_sub]

theorem negOneMulValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) :
    M.mulValue (M.number (-1)) (denote a) = M.negValue (denote a) := by
  obtain ⟨z, hz⟩ := (M.complex_members _).mp ha
  rw [hz, M.mul_numbers, M.neg_numbers, neg_one_mul]

theorem mulNegOneValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) :
    M.mulValue (denote a) (M.number (-1)) = M.negValue (denote a) := by
  obtain ⟨z, hz⟩ := (M.complex_members _).mp ha
  rw [hz, M.mul_numbers, M.neg_numbers, mul_neg_one]

end Litex

namespace Litex

noncomputable def roundingValue {M : Semantics.{u}} (ceiling : Bool)
    (a : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, a = M.number (r : ℂ)
    then M.number ((if ceiling then Int.ceil (Classical.choose h)
      else Int.floor (Classical.choose h) : ℤ) : ℂ)
    else M.number 0

theorem roundingValue_number {M : Semantics.{u}} (ceiling : Bool) (r : ℝ) :
    roundingValue ceiling (M.number (r : ℂ)) =
      M.number ((if ceiling then Int.ceil r else Int.floor r : ℤ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold roundingValue
  rw [dif_pos h, hr]

structure RoundingObj {M : Semantics.{u}} (ceiling : Bool)
    (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance roundingRepresentation {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α] :
    Representation M (RoundingObj (M := M) ceiling α) where
  wd p := In p.arg R
  denote p := roundingValue ceiling (denote p.arg)
  wd_isSet {p} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.integer_members _).mpr
      ⟨if ceiling then Int.ceil r else Int.floor r, by rw [hr, roundingValue_number]⟩)

noncomputable def floor {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a R) : Obj (M := M) (RoundingObj (M := M) false α) :=
  ⟨⟨a⟩, h⟩

noncomputable def ceil {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a R) : Obj (M := M) (RoundingObj (M := M) true α) :=
  ⟨⟨a⟩, h⟩

theorem roundingDenoteReal {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((if ceiling then Int.ceil r else Int.floor r : ℤ) : ℂ) := by
  change roundingValue ceiling (denote p.val.arg) = _
  rw [hr, roundingValue_number]

theorem roundingInZ {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α)) : In p Z := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact (M.integer_members _).mpr ⟨_, roundingDenoteReal p r hr⟩

theorem roundingOfInteger {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α))
    (h : In p.val.arg Z) : Same p p.val.arg := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp h
  have hr : denote p.val.arg = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  change denote p = denote p.val.arg
  rw [roundingDenoteReal p (z : ℝ) hr, Int.ceil_intCast, Int.floor_intCast, ite_self, hz]

theorem floorLeArgument {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) false α)) : Le p p.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact ⟨(Int.floor r : ℝ), r, by
    simpa only [Complex.ofReal_intCast, Bool.false_eq_true, if_false] using roundingDenoteReal p r hr,
    hr, Int.floor_le r⟩

theorem argumentLeCeil {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) true α)) : Le p.val.arg p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact ⟨r, (Int.ceil r : ℝ), hr, by
    simpa only [Complex.ofReal_intCast, if_true] using roundingDenoteReal p r hr,
    Int.le_ceil r⟩

theorem floorStrictUpper {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (AddObj (M := M) (RoundingObj (M := M) false α) β))
    (h : Same q.val.right (number 1)) : Lt q.val.left.val.arg q := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp q.val.left.wd
  change denote q.val.right = M.number 1 at h
  refine ⟨r, (Int.floor r : ℝ) + 1, hr, ?_, Int.lt_floor_add_one r⟩
  change M.addValue (denote q.val.left) (denote q.val.right) = _
  rw [roundingDenoteReal q.val.left r hr, h, M.add_numbers,
    Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_one]
  rfl

theorem ceilStrictLower {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (SubObj (M := M) (RoundingObj (M := M) true α) β))
    (h : Same q.val.right (number 1)) : Lt q q.val.left.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp q.val.left.wd
  change denote q.val.right = M.number 1 at h
  refine ⟨(Int.ceil r : ℝ) - 1, r, ?_, hr,
    (sub_lt_iff_lt_add).mpr (Int.ceil_lt_add_one r)⟩
  change M.subValue (denote q.val.left) (denote q.val.right) = _
  rw [roundingDenoteReal q.val.left r hr, h, M.sub_numbers,
    Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_one]
  rfl

theorem roundingMonotone {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α))
    (q : Obj (M := M) (RoundingObj (M := M) ceiling β))
    (h : Le p.val.arg q.val.arg) : Le p q := by
  obtain ⟨r, s, hr, hs, hrs⟩ := h
  refine ⟨((if ceiling then Int.ceil r else Int.floor r : ℤ) : ℝ),
    ((if ceiling then Int.ceil s else Int.floor s : ℤ) : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_intCast] using roundingDenoteReal p r hr
  · simpa only [Complex.ofReal_intCast] using roundingDenoteReal q s hs
  · cases ceiling
    · exact_mod_cast Int.floor_mono hrs
    · exact_mod_cast Int.ceil_mono hrs

end Litex

namespace Litex

/-- Fixed integer denotation; domain evidence is carried by each constructor. -/
noncomputable def integerDivisionValue {M : Semantics.{u}} (quotient : Bool)
    (a b : M.Value) : M.Value := by
  classical
  exact if h : ∃ p : ℤ × ℤ, a = M.number (p.1 : ℂ) ∧ b = M.number (p.2 : ℂ)
    then M.number ((if quotient then (Classical.choose h).1 / (Classical.choose h).2
      else (Classical.choose h).1 % (Classical.choose h).2 : ℤ) : ℂ)
    else M.number 0

theorem integerDivisionValue_numbers {M : Semantics.{u}} (quotient : Bool) (a b : ℤ) :
    integerDivisionValue quotient (M.number (a : ℂ)) (M.number (b : ℂ)) =
      M.number ((if quotient then a / b else a % b : ℤ) : ℂ) := by
  classical
  have h : ∃ p : ℤ × ℤ,
      M.number (a : ℂ) = M.number (p.1 : ℂ) ∧ M.number (b : ℂ) = M.number (p.2 : ℂ) :=
    ⟨(a, b), rfl, rfl⟩
  have hp : Classical.choose h = (a, b) := Prod.ext
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).1)).symm
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).2)).symm
  unfold integerDivisionValue
  rw [dif_pos h, hp]

structure ModObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure QuotObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

noncomputable instance modRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (ModObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right Z ∧ ¬ Same p.right (number 0)
  denote p := integerDivisionValue false (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp h.2.1
    exact M.member_isSet ((M.integer_members _).mpr
      ⟨a % b, by rw [ha, hb, integerDivisionValue_numbers]; rfl⟩)

noncomputable instance quotRepresentation {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (QuotObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right NPos
  denote p := integerDivisionValue true (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ h.2))
    exact M.member_isSet ((M.integer_members _).mpr
      ⟨a / b, by rw [ha, hb, integerDivisionValue_numbers]; rfl⟩)

noncomputable def mod {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) (h0 : ¬ Same b (number 0)) : Obj (M := M) (ModObj (M := M) α β) :=
  ⟨⟨a, b⟩, ha, hb, h0⟩

noncomputable def quot {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b NPos) : Obj (M := M) (QuotObj (M := M) α β) :=
  ⟨⟨a, b⟩, ha, hb⟩

theorem modDenoteInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number ((a % b : ℤ) : ℂ) := by
  change integerDivisionValue false _ _ = _
  rw [ha, hb, integerDivisionValue_numbers]; rfl

theorem quotDenoteInt {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number ((a / b : ℤ) : ℂ) := by
  change integerDivisionValue true _ _ = _
  rw [ha, hb, integerDivisionValue_numbers]; rfl

theorem modInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β)) : In p Z := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  exact (M.integer_members _).mpr ⟨_, modDenoteInt p a b ha hb⟩

theorem quotInZ {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β)) : In p Z := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ p.wd.2))
  exact (M.integer_members _).mpr ⟨_, quotDenoteInt p a b ha hb⟩

theorem integerWitnessOfNPos {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (h : In a NPos) :
    ∃ z : ℤ, denote a = M.number (z : ℂ) ∧ 0 < z := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ h))
  obtain ⟨r, hr, hpos⟩ := ((S.sep_members _ _ _).mp h).2
  have heq : (z : ℝ) = r := Complex.ofReal_injective (by
    simpa only [Complex.ofReal_intCast] using M.number_injective (hz.symm.trans hr))
  refine ⟨z, hz, ?_⟩
  rw [← heq] at hpos
  exact_mod_cast hpos

theorem quotDecomposition {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (quotientFirst : Bool) :
    denote p.val.left = M.addValue
      (if quotientFirst then M.mulValue (denote p) (denote p.val.right)
       else M.mulValue (denote p.val.right) (denote p))
      (integerDivisionValue false (denote p.val.left) (denote p.val.right)) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ p.wd.2))
  rw [quotDenoteInt p a b ha hb, ha, hb, integerDivisionValue_numbers]
  cases quotientFirst <;> simp only [Bool.false_eq_true, if_false, if_true,
    M.mul_numbers, M.add_numbers]
  · exact congrArg M.number (by exact_mod_cast (Int.mul_ediv_add_emod a b).symm)
  · exact congrArg M.number (by exact_mod_cast (Int.ediv_mul_add_emod a b).symm)

theorem quotByOne {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (h : Same p.val.right (number 1)) : Same p p.val.left := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  change denote p.val.right = M.number 1 at h
  change denote p = denote p.val.left
  rw [quotDenoteInt p a 1 ha (by simpa only [Int.cast_one] using h), Int.ediv_one, ha]

theorem quotSelfOne {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (h : Same p.val.left p.val.right) (hp : In p.val.right NPos) : Same p (number 1) := by
  obtain ⟨b, hb, hpos⟩ := integerWitnessOfNPos p.val.right hp
  change denote p = M.number 1
  rw [quotDenoteInt p b b (h.trans hb) hb, Int.ediv_self (ne_of_gt hpos), Int.cast_one]

theorem modNonnegative {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β))
    (ha : In p.val.left Z) (hb : In p.val.right NPos) : Le (number 0) p := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp ha
  obtain ⟨b, hb, hpos⟩ := integerWitnessOfNPos p.val.right hb
  refine ⟨0, ((a % b : ℤ) : ℝ), ?_, ?_, ?_⟩
  · change M.number (0 : ℂ) = M.number ((0 : ℝ) : ℂ)
    rw [Complex.ofReal_zero]
  · simpa only [Complex.ofReal_intCast] using modDenoteInt p a b ha hb
  · exact_mod_cast Int.emod_nonneg a (ne_of_gt hpos)

theorem modStrictUpper {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β))
    (ha : In p.val.left Z) (hb : In p.val.right NPos) : Lt p p.val.right := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp ha
  obtain ⟨b, hb, hpos⟩ := integerWitnessOfNPos p.val.right hb
  refine ⟨((a % b : ℤ) : ℝ), (b : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_intCast] using modDenoteInt p a b ha hb
  · simpa only [Complex.ofReal_intCast] using hb
  · exact_mod_cast Int.emod_lt_of_pos a hpos

end Litex

namespace Litex

noncomputable def gcdLcmValue {M : Semantics.{u}} (least : Bool) (a b : M.Value) : M.Value := by
  classical
  exact if h : ∃ p : ℤ × ℤ, a = M.number (p.1 : ℂ) ∧ b = M.number (p.2 : ℂ)
    then M.number ((if least then Int.lcm (Classical.choose h).1 (Classical.choose h).2
      else Int.gcd (Classical.choose h).1 (Classical.choose h).2 : ℕ) : ℂ)
    else M.number 0

theorem gcdLcmValue_numbers {M : Semantics.{u}} (least : Bool) (a b : ℤ) :
    gcdLcmValue least (M.number (a : ℂ)) (M.number (b : ℂ)) =
      M.number ((if least then Int.lcm a b else Int.gcd a b : ℕ) : ℂ) := by
  classical
  have h : ∃ p : ℤ × ℤ,
      M.number (a : ℂ) = M.number (p.1 : ℂ) ∧ M.number (b : ℂ) = M.number (p.2 : ℂ) :=
    ⟨(a, b), rfl, rfl⟩
  have hp : Classical.choose h = (a, b) := Prod.ext
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).1)).symm
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).2)).symm
  unfold gcdLcmValue
  rw [dif_pos h, hp]

structure GcdObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure LcmObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

noncomputable instance gcdRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (GcdObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right Z ∧ (¬ Same p.left (number 0) ∨ ¬ Same p.right (number 0))
  denote p := gcdLcmValue false (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp h.2.1
    exact M.member_isSet ((M.natural_members _).mpr
      ⟨Int.gcd a b, by rw [ha, hb, gcdLcmValue_numbers]; rfl⟩)

noncomputable instance lcmRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (LcmObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right Z
  denote p := gcdLcmValue true (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp h.2
    exact M.member_isSet ((M.natural_members _).mpr
      ⟨Int.lcm a b, by rw [ha, hb, gcdLcmValue_numbers]; rfl⟩)

noncomputable def gcd {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) (h0 : ¬ Same a (number 0) ∨ ¬ Same b (number 0)) :
    Obj (M := M) (GcdObj (M := M) α β) := ⟨⟨a, b⟩, ha, hb, h0⟩

noncomputable def lcm {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) : Obj (M := M) (LcmObj (M := M) α β) := ⟨⟨a, b⟩, ha, hb⟩

theorem gcdDenoteInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number (Int.gcd a b : ℂ) := by
  change gcdLcmValue false _ _ = _
  rw [ha, hb, gcdLcmValue_numbers]; rfl

theorem lcmDenoteInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number (Int.lcm a b : ℂ) := by
  change gcdLcmValue true _ _ = _
  rw [ha, hb, gcdLcmValue_numbers]; rfl

theorem lcmNonzeroOfArgs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β))
    (hla : ¬ Same p.val.left (number 0)) (hlb : ¬ Same p.val.right (number 0)) : ¬ Same p (number 0) := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b,hb⟩ := (M.integer_members _).mp p.wd.2
  have ha0 : a ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote p.val.left (a : ℂ) ha hla
    exact_mod_cast h
  have hb0 : b ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote p.val.right (b : ℂ) hb hlb
    exact_mod_cast h
  have hn : Int.lcm a b ≠ 0 := by
    rw [Int.lcm_eq_natAbs_lcm_natAbs]
    exact Nat.lcm_ne_zero (Int.natAbs_ne_zero.mpr ha0) (Int.natAbs_ne_zero.mpr hb0)
  apply NativeBridge.notSameOfNativeNonzero p (Int.lcm a b : ℂ) (lcmDenoteInt p a b ha hb)
  exact_mod_cast hn

theorem gcdInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) : In p N := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  exact (M.natural_members _).mpr ⟨_, gcdDenoteInt p a b ha hb⟩

theorem lcmInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β)) : In p N := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2
  exact (M.natural_members _).mpr ⟨_, lcmDenoteInt p a b ha hb⟩

theorem gcdPositiveWitness {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    ∃ n : ℕ, denote p = M.number (n : ℂ) ∧ 0 < n := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  refine ⟨Int.gcd a b, gcdDenoteInt p a b ha hb, Int.gcd_pos_iff.mpr ?_⟩
  rcases p.wd.2.2 with h | h
  · exact Or.inl (fun h0 => h (by change denote p.val.left = M.number 0; rw [ha, h0, Int.cast_zero]))
  · exact Or.inr (fun h0 => h (by change denote p.val.right = M.number 0; rw [hb, h0, Int.cast_zero]))

theorem gcdNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    ¬ Same p (number 0) := by
  obtain ⟨n, hn, hp⟩ := gcdPositiveWitness p
  intro h
  have hz : (n : ℂ) = 0 := M.number_injective (hn.symm.trans h)
  exact (Nat.ne_of_gt hp) (by exact_mod_cast hz)

theorem gcdInNPos {M : Semantics.{u}} [S : SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) : In p NPos := by
  obtain ⟨n, hn, hp⟩ := gcdPositiveWitness p
  apply (S.sep_members _ _ _).mpr
  refine ⟨gcdInN p, (n : ℝ), ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using hn
  · exact_mod_cast hp

theorem absValue_int {M : Semantics.{u}} (a : ℤ) :
    absValue (M.number (a : ℂ)) = M.number (a.natAbs : ℂ) := by
  rw [← Complex.ofReal_intCast, absValue_number]
  have h : |(a : ℝ)| = (a.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [h, Complex.ofReal_natCast]

theorem gcdCommutative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    denote p = gcdLcmValue false (denote p.val.right) (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  rw [gcdDenoteInt p a b ha hb, ha, hb, gcdLcmValue_numbers, Int.gcd_comm a b]; rfl

theorem lcmCommutative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β)) :
    denote p = gcdLcmValue true (denote p.val.right) (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2
  rw [lcmDenoteInt p a b ha hb, ha, hb, gcdLcmValue_numbers, Int.lcm_comm a b]; rfl

theorem gcdSelfAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (h : Same p.val.left p.val.right) : denote p = absValue (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  rw [gcdDenoteInt p a a ha (h.symm.trans ha), Int.gcd_self, ha, absValue_int]

theorem lcmSelfAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β))
    (h : Same p.val.left p.val.right) : denote p = absValue (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  rw [lcmDenoteInt p a a ha (h.symm.trans ha), Int.lcm_self, ha, absValue_int]

theorem gcdRightZeroAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (hz : Same p.val.right (number 0)) (_hn : ¬ Same p.val.left (number 0)) :
    denote p = absValue (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  change denote p.val.right = M.number 0 at hz
  rw [gcdDenoteInt p a 0 ha (by simpa only [Int.cast_zero] using hz), Int.gcd_zero, ha, absValue_int]

theorem gcdLeftZeroAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (hz : Same p.val.left (number 0)) (_hn : ¬ Same p.val.right (number 0)) :
    denote p = absValue (denote p.val.right) := by
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  change denote p.val.left = M.number 0 at hz
  rw [gcdDenoteInt p 0 b (by simpa only [Int.cast_zero] using hz) hb, Int.gcd_zero_left, hb, absValue_int]

theorem gcdEuclideanStep {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    denote p = gcdLcmValue false (denote p.val.right)
      (integerDivisionValue false (denote p.val.left) (denote p.val.right)) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  rw [gcdDenoteInt p a b ha hb, ha, hb, integerDivisionValue_numbers]
  change M.number (Int.gcd a b : ℂ) = gcdLcmValue false (M.number (b : ℂ)) (M.number ((a % b : ℤ) : ℂ))
  rw [gcdLcmValue_numbers, Int.gcd_comm b (a % b), Int.gcd_emod]; rfl

theorem gcdLcmProduct {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (gcdFirst reverseArgs : Bool) :
    (if gcdFirst then M.mulValue (denote p) (gcdLcmValue true (denote p.val.left) (denote p.val.right))
     else M.mulValue (gcdLcmValue true (denote p.val.left) (denote p.val.right)) (denote p)) =
    absValue (if reverseArgs then M.mulValue (denote p.val.right) (denote p.val.left)
      else M.mulValue (denote p.val.left) (denote p.val.right)) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  rw [gcdDenoteInt p a b ha hb, ha, hb, gcdLcmValue_numbers]
  cases gcdFirst <;> cases reverseArgs <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers, ← Int.cast_mul, absValue_int]
  all_goals
    apply congrArg M.number
    norm_cast
    simp only [Int.gcd_mul_lcm, Int.natAbs_mul, Nat.mul_comm]

end Litex

namespace Litex

noncomputable def factorialValue {M : Semantics.{u}} (a : M.Value) : M.Value := by
  classical
  exact if h : ∃ n : ℕ, a = M.number (n : ℂ)
    then M.number ((Classical.choose h).factorial : ℂ) else M.number 0

theorem factorialValue_number {M : Semantics.{u}} (n : ℕ) :
    factorialValue (M.number (n : ℂ)) = M.number (n.factorial : ℂ) := by
  classical
  have h : ∃ k : ℕ, M.number (n : ℂ) = M.number (k : ℂ) := ⟨n, rfl⟩
  have hk : Classical.choose h = n :=
    (Nat.cast_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold factorialValue
  rw [dif_pos h, hk]

structure FactorialObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance factorialRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (FactorialObj (M := M) α) where
  wd p := In p.arg N
  denote p := factorialValue (denote p.arg)
  wd_isSet {p} h := by
    obtain ⟨n, hn⟩ := (M.natural_members _).mp h
    exact M.member_isSet ((M.natural_members _).mpr
      ⟨n.factorial, by rw [hn, factorialValue_number]⟩)

noncomputable def factorial {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a N) : Obj (M := M) (FactorialObj (M := M) α) :=
  ⟨⟨a⟩, h⟩

theorem factorialDenoteNat {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) (n : ℕ)
    (hn : denote p.val.arg = M.number (n : ℂ)) : denote p = M.number (n.factorial : ℂ) := by
  change factorialValue _ = _
  rw [hn, factorialValue_number]

theorem factorialInN {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) : In p N := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp p.wd
  exact (M.natural_members _).mpr ⟨_, factorialDenoteNat p n hn⟩

theorem factorialInNPos {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) : In p NPos := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp p.wd
  apply (S.sep_members _ _ _).mpr
  refine ⟨factorialInN p, (n.factorial : ℝ), ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat p n hn
  · exact_mod_cast Nat.factorial_pos n

theorem factorialNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) : ¬ Same p (number 0) := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp p.wd
  intro h
  have hz : (n.factorial : ℂ) = 0 :=
    M.number_injective ((factorialDenoteNat p n hn).symm.trans h)
  exact Nat.factorial_ne_zero n (by exact_mod_cast hz)

/-- The two original certified factorial arguments differ by one. -/
theorem factorialStep {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FactorialObj (M := M) α))
    (q : Obj (M := M) (FactorialObj (M := M) β))
    (h : denote p.val.arg = M.addValue (denote q.val.arg) (M.number 1))
    (coefficientFirst : Bool) : denote p =
      (if coefficientFirst then M.mulValue (denote p.val.arg) (denote q)
       else M.mulValue (denote q) (denote p.val.arg)) := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp q.wd
  have hs : denote p.val.arg = M.number ((n + 1 : ℕ) : ℂ) := by
    rw [h, hn, M.add_numbers, Nat.cast_add, Nat.cast_one]
  rw [factorialDenoteNat p (n + 1) hs, factorialDenoteNat q n hn, hs]
  cases coefficientFirst <;> simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers]
  · rw [Nat.factorial_succ, Nat.cast_mul, mul_comm]
  · rw [Nat.factorial_succ, Nat.cast_mul]

theorem factorialMonotone {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FactorialObj (M := M) α))
    (q : Obj (M := M) (FactorialObj (M := M) β))
    (h : Le p.val.arg q.val.arg) : Le p q := by
  obtain ⟨m, hm⟩ := (M.natural_members _).mp p.wd
  obtain ⟨n, hn⟩ := (M.natural_members _).mp q.wd
  have hmr : denote p.val.arg = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hm
  have hnr : denote q.val.arg = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hn
  have hmn : m ≤ n := by
    exact_mod_cast (NativeBridge.le_iff_ofDenoteReal _ _ _ _ hmr hnr).mp h
  refine ⟨(m.factorial : ℝ), (n.factorial : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat p m hm
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat q n hn
  · exact_mod_cast Nat.factorial_le hmn

theorem factorialStrictMonotone {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FactorialObj (M := M) α))
    (q : Obj (M := M) (FactorialObj (M := M) β))
    (hp : In p.val.arg NPos) (h : Lt p.val.arg q.val.arg) : Lt p q := by
  obtain ⟨m, hm⟩ := (M.natural_members _).mp p.wd
  obtain ⟨n, hn⟩ := (M.natural_members _).mp q.wd
  have hmr : denote p.val.arg = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hm
  have hnr : denote q.val.arg = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hn
  have hmn : m < n := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hmr hnr).mp h
  have hm0 : 0 < m := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ 0 _ rfl hmr).mp (inNPos_positive _ hp)
  refine ⟨(m.factorial : ℝ), (n.factorial : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat p m hm
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat q n hn
  · exact_mod_cast Nat.factorial_lt_of_lt hm0 hmn

end Litex

namespace Litex

theorem integerPredecessorLe {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SubObj (M := M) β γ))
    (ha : In a Z) (hb : In p.val.left Z) (h1 : Same p.val.right (number 1))
    (hlt : Lt a p.val.left) : Le a p := by
  obtain ⟨m, hm⟩ := (M.integer_members _).mp ha
  obtain ⟨n, hn⟩ := (M.integer_members _).mp hb
  have hmr : denote a = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hm
  have hnr : denote p.val.left = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hn
  have hmn : m < n := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hmr hnr).mp hlt
  have hpred : m ≤ n - 1 := by omega
  refine ⟨(m : ℝ), (n : ℝ) - 1, hmr, ?_, ?_⟩
  · change M.subValue (denote p.val.left) (denote p.val.right) = _
    change denote p.val.right = M.number 1 at h1
    rw [hnr, h1, M.sub_numbers, Complex.ofReal_sub, Complex.ofReal_one]
  · exact_mod_cast hpred

end Litex

namespace Litex

open Lean Elab Tactic in
/-- Fixed coordinate normalization for the verifier's Complex polynomial tag.
Each stage runs only on remaining goals; the produced proof is kernel checked. -/
elab "litex_normalize_complex" : tactic => do
  evalTactic (← `(tactic| apply Complex.ext))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals norm_num [pow_succ]))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals ring!))

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

def IsRange (f r : M.Value) : Prop :=
  M.isSet r ∧ ∀ y, M.mem y r ↔ ∃ a, M.mem (F.pairValue a y) f

/-- The range depends only on the graph, independently of which signature certifies it. -/
noncomputable def rangeValue (f : M.Value) : M.Value :=
  by classical exact if h : ∃ r, IsRange f r then Classical.choose h else F.emptyValue

theorem range_spec {D B f : M.Value} (hB : M.isSet B)
    (hf : M.mem f (F.fnSetValue D B)) : IsRange f (rangeValue f) := by
  have exists_range : ∃ r, IsRange f r := by
    refine ⟨F.sepValue B (fun y => ∃ a, M.mem (F.pairValue a y) f), F.sep_isSet _ _ hB, ?_⟩
    intro y
    rw [F.sep_members]
    constructor
    · exact And.right
    · intro h
      obtain ⟨a, ha⟩ := h
      obtain ⟨x, _, z, hz, eq⟩ := ((F.fnSet_members D B f).mp hf).1 _ ha
      have hy : M.mem y B := (F.pair_injective eq).2.symm ▸ hz
      exact ⟨hy, a, ha⟩
  simpa only [rangeValue, dif_pos exists_range] using Classical.choose_spec exists_range

theorem range_mem_iff {D B f y : M.Value} (hB : M.isSet B)
    (hf : M.mem f (F.fnSetValue D B)) :
    M.mem y (rangeValue f) ↔ ∃ a, M.mem a D ∧ y = F.callValue f a := by
  rw [(range_spec hB hf).2 y]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, FiniteFunction.graph_pair_value ((F.fnSet_members D B f).mp hf) ha⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, F.call_graph D B f a ((F.fnSet_members D B f).mp hf) ha⟩

theorem range_subset {D B f y : M.Value} (hB : M.isSet B)
    (hf : M.mem f (F.fnSetValue D B)) (hy : M.mem y (rangeValue f)) : M.mem y B := by
  obtain ⟨a, ha, rfl⟩ := (range_mem_iff hB hf).mp hy
  exact call_mem D B f a hf ha
end FunctionSemantics

structure FunctionRange {M : Semantics.{u}} (α : Type v) [Representation M α] where
  function : Obj (M := M) α

noncomputable instance functionRangeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (FunctionRange (M := M) α) where
  wd r := ∃ s : FunctionSignature M, In r.function (fnSet s)
  denote r := FunctionSemantics.rangeValue (denote r.function)
  wd_isSet h := by
    obtain ⟨s, hs⟩ := h
    exact (FunctionSemantics.range_spec s.output_isSet hs).1

noncomputable def fnRange {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α)
    (s : FunctionSignature M) (hf : In f (fnSet s)) : Obj (M := M) (FunctionRange (M := M) α) :=
  ⟨⟨f⟩, ⟨s, hf⟩⟩

theorem inFnRange_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (FunctionRange (M := M) α)) (y : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In r.val.function (fnSet s)) :
    In y r ↔ ∃ a : Obj (M := M) M.Value, ∃ (_ha : M.mem (denote a) s.domain),
      denote y = F.callValue (denote r.val.function) (denote a) := by
  change M.mem (denote y) (FunctionSemantics.rangeValue (denote r.val.function)) ↔ _
  rw [FunctionSemantics.range_mem_iff s.output_isSet hf]
  constructor
  · rintro ⟨a, ha, eq⟩
    exact ⟨semanticObject a (M.member_isSet ha), ha, eq⟩
  · rintro ⟨a, ha, eq⟩
    exact ⟨denote a, ha, eq⟩

theorem fnRangeInOutput {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (FunctionRange (M := M) α)) (y : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In r.val.function (fnSet s)) (hy : In y r) :
    M.mem (denote y) s.output := FunctionSemantics.range_subset s.output_isSet hf hy

theorem callOnInFnRange {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallOnObj (M := M) α β))
    (r : Obj (M := M) (FunctionRange (M := M) α))
    (same : Same c.val.function r.val.function) : In c r := by
  change M.mem (F.callValue (denote c.val.function) (denote c.val.argument))
    (FunctionSemantics.rangeValue (denote r.val.function))
  rw [← same]
  exact (FunctionSemantics.range_mem_iff c.val.signature.output_isSet c.wd.1).mpr
    ⟨denote c.val.argument, c.wd.2, rfl⟩

theorem callInFnRange {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallObj (M := M) α β))
    (r : Obj (M := M) (FunctionRange (M := M) α))
    (same : Same c.val.function r.val.function) : In c r := by
  change M.mem (F.callValue (denote c.val.function) (denote c.val.argument))
    (FunctionSemantics.rangeValue (denote r.val.function))
  rw [← same]
  exact (FunctionSemantics.range_mem_iff c.val.output_isSet c.wd.1).mpr
    ⟨denote c.val.argument, (FunctionSignature.oneTarget_domain _ _ _ _ _).mpr c.wd.2, rfl⟩

theorem call2InFnRange {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (c : Obj (M := M) (CallObj2 (M := M) α β γ))
    (r : Obj (M := M) (FunctionRange (M := M) α))
    (same : Same c.val.function r.val.function) : In c r := by
  change M.mem (F.callValue (denote c.val.function) (FiniteFunction.pack2 (denote c.val.first) (denote c.val.second)))
    (FunctionSemantics.rangeValue (denote r.val.function))
  rw [← same]
  exact (FunctionSemantics.range_mem_iff c.val.output_isSet c.wd.1).mpr
    ⟨FiniteFunction.pack2 (denote c.val.first) (denote c.val.second),
      (FunctionSignature.twoTarget_domain _ _ _ _ _ _ _).mpr c.wd.2, rfl⟩

end Litex

namespace Litex

structure RangeObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  start : Obj (M := M) α
  finish : Obj (M := M) β

def RangeObj.condition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (r : RangeObj (M := M) α β) (value : M.Value) : Prop :=
  ∃ lower upper k : ℤ, denote r.start = M.number (lower : ℂ) ∧
    denote r.finish = M.number (upper : ℂ) ∧ value = M.number (k : ℂ) ∧
    lower ≤ k ∧ k < upper

instance rangeRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (RangeObj (M := M) α β) where
  wd r := In r.start Z ∧ In r.finish Z
  denote r := S.sepValue (M.standard .integer) r.condition
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .integer)

def range {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a Z) (hb : In b Z) :
    Obj (M := M) (RangeObj (M := M) α β) := ⟨⟨a, b⟩, ⟨ha, hb⟩⟩

theorem inRange_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) :
    In p (range a b ha hb) ↔
      ∃ lower upper k : ℤ, denote a = M.number (lower : ℂ) ∧
        denote b = M.number (upper : ℂ) ∧ denote p = M.number (k : ℂ) ∧
        lower ≤ k ∧ k < upper := by
  change M.mem (denote p) (S.sepValue (M.standard .integer) _) ↔ _
  rw [S.sep_members]
  constructor
  · exact fun h => h.2
  · rintro ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩
    exact ⟨(M.integer_members _).mpr ⟨k, hp⟩, lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem inRangeOfDenote {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) (lower upper k : ℤ)
    (hl : denote a = M.number (lower : ℂ))
    (hu : denote b = M.number (upper : ℂ))
    (hp : denote p = M.number (k : ℂ)) (hlo : lower ≤ k) (hhi : k < upper) :
    In p (range a b ha hb) :=
  (inRange_iff a b p ha hb).mpr ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem numberInRange {M : Semantics.{u}} [SetSemantics M]
    (lower upper k : ℤ) (hlo : lower ≤ k) (hhi : k < upper) :
    In (number (M := M) (k : ℂ))
      (range (number (lower : ℂ)) (number (upper : ℂ))
        (NativeBridge.numberInZ lower) (NativeBridge.numberInZ upper)) :=
  inRangeOfDenote _ _ _ _ _ lower upper k rfl rfl rfl hlo hhi

theorem numberInRangeOfEq {M : Semantics.{u}} [SetSemantics M]
    (a b p : ℂ) (lower upper k : ℤ)
    (ha : a = (lower : ℂ)) (hb : b = (upper : ℂ)) (hp : p = (k : ℂ))
    (hlo : lower ≤ k) (hhi : k < upper) :
    In (number (M := M) p)
      (range (number a) (number b)
        (NativeBridge.numberInZOfEq a lower ha) (NativeBridge.numberInZOfEq b upper hb)) :=
  inRangeOfDenote _ _ _ _ _ lower upper k
    (congrArg M.number ha) (congrArg M.number hb) (congrArg M.number hp) hlo hhi


theorem integerPositiveOfWitness {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) α) (k : ℤ)
    (hk : denote p = M.number (k : ℂ)) (hpos : 0 < k) : In p NPos := by
  apply (S.sep_members _ _ _).mpr
  have hn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hpos)
  refine ⟨(M.natural_members _).mpr ⟨k.toNat, ?_⟩, (k : ℝ), ?_, ?_⟩
  · exact hk.trans (congrArg M.number (by exact_mod_cast hn.symm))
  · simpa only [Complex.ofReal_intCast] using hk
  · exact_mod_cast hpos

theorem inClosedRangeInteger {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower upper : ℤ)
    (hl : denote r.val.start = M.number (lower : ℂ))
    (hu : denote r.val.finish = M.number (upper : ℂ)) (h : In p r) :
    ∃ k : ℤ, Same p (number (k : ℂ)) ∧ lower ≤ k ∧ k ≤ upper := by
  obtain ⟨l, u, k, ha, hb, hp, hlo, hhi⟩ :=
    (inClosedRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  have hb' : u = upper := by exact_mod_cast M.number_injective (hb.symm.trans hu)
  subst l
  subst u
  exact ⟨k, hp, hlo, hhi⟩

theorem inClosedRangeBounds {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (h : In p r) : In p Z ∧ Le r.val.start p ∧ Le p r.val.finish := by
  obtain ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩ :=
    (inClosedRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  refine ⟨(M.integer_members _).mpr ⟨k, hp⟩, ?_, ?_⟩
  · refine ⟨(lower : ℝ), (k : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hl
    · simpa only [Complex.ofReal_intCast] using hp
    · exact_mod_cast hlo
  · refine ⟨(k : ℝ), (upper : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hp
    · simpa only [Complex.ofReal_intCast] using hu
    · exact_mod_cast hhi

theorem inClosedRangePositive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower : ℤ) (hl : denote r.val.start = M.number (lower : ℂ))
    (hpos : 0 < lower) (h : In p r) : In p NPos := by
  obtain ⟨l, upper, k, ha, _, hp, hlo, _⟩ :=
    (inClosedRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  subst l
  exact integerPositiveOfWitness p k hp (lt_of_lt_of_le hpos hlo)

theorem inRangeInteger {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (RangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower upper : ℤ)
    (hl : denote r.val.start = M.number (lower : ℂ))
    (hu : denote r.val.finish = M.number (upper : ℂ)) (h : In p r) :
    ∃ k : ℤ, Same p (number (k : ℂ)) ∧ lower ≤ k ∧ k < upper := by
  obtain ⟨l, u, k, ha, hb, hp, hlo, hhi⟩ :=
    (inRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  have hb' : u = upper := by exact_mod_cast M.number_injective (hb.symm.trans hu)
  subst l
  subst u
  exact ⟨k, hp, hlo, hhi⟩

theorem inRangeBounds {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (RangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (h : In p r) : In p Z ∧ Le r.val.start p ∧ Lt p r.val.finish := by
  obtain ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩ :=
    (inRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  refine ⟨(M.integer_members _).mpr ⟨k, hp⟩, ?_, ?_⟩
  · refine ⟨(lower : ℝ), (k : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hl
    · simpa only [Complex.ofReal_intCast] using hp
    · exact_mod_cast hlo
  · refine ⟨(k : ℝ), (upper : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hp
    · simpa only [Complex.ofReal_intCast] using hu
    · exact_mod_cast hhi

theorem inRangePositive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (RangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower : ℤ) (hl : denote r.val.start = M.number (lower : ℂ))
    (hpos : 0 < lower) (h : In p r) : In p NPos := by
  obtain ⟨l, upper, k, ha, _, hp, hlo, _⟩ :=
    (inRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  subst l
  exact integerPositiveOfWitness p k hp (lt_of_lt_of_le hpos hlo)

/-! Weak additive shifts consume an ordered bound and a signed addend. -/

theorem leAddOfLeOfNonneg {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (AddObj (M := M) β γ))
    (ha : Le a p.val.left) (hb : Le (number 0) p.val.right) : Le a p := by
  obtain ⟨a', x', ha', hx', hax⟩ := ha
  obtain ⟨z', y', hz', hy', hzy⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨a', x' + y', ha', ?_, le_trans hax (le_add_of_nonneg_right (hz0 ▸ hzy))⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem leAddOfLeOfNonnegSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (AddObj (M := M) β γ))
    (ha : Le a p.val.right) (hb : Le (number 0) p.val.left) : Le a p := by
  obtain ⟨a', y', ha', hy', hay⟩ := ha
  obtain ⟨z', x', hz', hx', hzx⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨a', x' + y', ha', ?_, le_trans hay (le_add_of_nonneg_left (hz0 ▸ hzx))⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem addLeOfLeOfNonpos {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (a : Obj (M := M) γ)
    (ha : Le p.val.left a) (hb : Le p.val.right (number 0)) : Le p a := by
  obtain ⟨x', a', hx', ha', hxa⟩ := ha
  obtain ⟨y', z', hy', hz', hyz⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨x' + y', a', ?_, ha', le_trans (add_le_of_nonpos_right (hz0 ▸ hyz)) hxa⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem addLeOfLeOfNonposSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (a : Obj (M := M) γ)
    (ha : Le p.val.right a) (hb : Le p.val.left (number 0)) : Le p a := by
  obtain ⟨y', a', hy', ha', hya⟩ := ha
  obtain ⟨x', z', hx', hz', hxz⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨x' + y', a', ?_, ha', le_trans (add_le_of_nonpos_left (hz0 ▸ hxz)) hya⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem addLeAdd {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Le p.val.left q.val.left) (h₂ : Le p.val.right q.val.right) : Le p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_le_add hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem addLeAddSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Le p.val.left q.val.right) (h₂ : Le p.val.right q.val.left) : Le p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, d + b, ?_, ?_, ?_⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hd, hb, M.add_numbers, Complex.ofReal_add]
  · simpa only [add_comm b d] using add_le_add hab hcd

theorem addLtAddOfLtOfLe {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Lt p.val.left q.val.left) (h₂ : Le p.val.right q.val.right) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_lt_add_of_lt_of_le hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem addLtAddOfLeOfLt {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Le p.val.left q.val.left) (h₂ : Lt p.val.right q.val.right) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_lt_add_of_le_of_lt hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem subStructuralLeRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Le lhs.val.left rhs.val.left)
    (hSame : Same lhs.val.right rhs.val.right) : Le lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.2
  have hdiff : (a : ℂ) - z = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.sub_numbers] using hr
  have hc : denote lhs.val.right = M.number ((a - r : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (by
      calc z = (a : ℂ) - ((a : ℂ) - z) := (sub_sub_cancel _ _).symm
           _ = (a : ℂ) - (r : ℂ) := congrArg (fun t : ℂ => (a : ℂ) - t) hdiff)
  refine NativeBridge.leOfDenoteReal lhs rhs (a - (a - r)) (b - (a - r)) ?_ ?_ (sub_le_sub_right hab (a - r))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, ha, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, hb, M.sub_numbers, Complex.ofReal_sub]

theorem subStructuralLeLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Le rhs.val.right lhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Le lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.1
  have hdiff : z - (b : ℂ) = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, hb, M.sub_numbers] using hr
  have hc : denote lhs.val.left = M.number ((r + b : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_add]
    exact congrArg M.number (sub_eq_iff_eq_add.mp hdiff)
  refine NativeBridge.leOfDenoteReal lhs rhs ((r + b) - b) ((r + b) - a) ?_ ?_ (sub_le_sub_left hab (r + b))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, hb, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, ha, M.sub_numbers, Complex.ofReal_sub]

theorem subStructuralLtRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Lt lhs.val.left rhs.val.left)
    (hSame : Same lhs.val.right rhs.val.right) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.2
  have hdiff : (a : ℂ) - z = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.sub_numbers] using hr
  have hc : denote lhs.val.right = M.number ((a - r : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (by
      calc z = (a : ℂ) - ((a : ℂ) - z) := (sub_sub_cancel _ _).symm
           _ = (a : ℂ) - (r : ℂ) := congrArg (fun t : ℂ => (a : ℂ) - t) hdiff)
  refine NativeBridge.ltOfDenoteReal lhs rhs (a - (a - r)) (b - (a - r)) ?_ ?_ (sub_lt_sub_right hab (a - r))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, ha, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, hb, M.sub_numbers, Complex.ofReal_sub]

theorem subStructuralLtLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Lt rhs.val.right lhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.1
  have hdiff : z - (b : ℂ) = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, hb, M.sub_numbers] using hr
  have hc : denote lhs.val.left = M.number ((r + b : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_add]
    exact congrArg M.number (sub_eq_iff_eq_add.mp hdiff)
  refine NativeBridge.ltOfDenoteReal lhs rhs ((r + b) - b) ((r + b) - a) ?_ ?_ (sub_lt_sub_left hab (r + b))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, hb, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, ha, M.sub_numbers, Complex.ofReal_sub]

structure IntersectObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance intersectRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (IntersectObj (M := M) α β) where
  wd _ := True
  denote p := S.sepValue (denote p.left) (fun x => M.mem x (denote p.right))
  wd_isSet {p} _ := S.sep_isSet _ _ (isSet p.left)

def intersect {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (IntersectObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem inIntersect_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ) :
    In a (intersect A B) ↔ In a A ∧ In a B := S.sep_members _ _ _

/-- Optional foundation law; the ZF interpretation proves this below. -/
class RegularitySemantics (M : Semantics.{u}) where
  regularity : ∀ A, M.isSet A → (∃ x, M.mem x A) →
    ∃ x, M.mem x A ∧ ∀ y, M.mem y x → ¬ M.mem y A

noncomputable instance numericRegularitySemantics : RegularitySemantics NumericModel.model where
  regularity := fun (A : ZFSet.{0}) _ h => by
    change (∃ x : ZFSet.{0}, x ∈ A) at h
    change ∃ x : ZFSet.{0}, x ∈ A ∧ ∀ y : ZFSet.{0}, y ∈ x → ¬ y ∈ A
    have hA : A ≠ (∅ : ZFSet.{0}) := by
      rintro rfl
      obtain ⟨x, hx⟩ := h
      exact ZFSet.notMem_empty x hx
    obtain ⟨x, hx, disjoint⟩ := ZFSet.regularity A hA
    refine ⟨x, hx, ?_⟩
    intro y hy hAy
    have hm : y ∈ A ∩ x := ZFSet.mem_inter.mpr ⟨hAy, hy⟩
    rw [disjoint] at hm
    exact ZFSet.notMem_empty y hm

theorem regularity {M : Semantics.{u}} [S : SetSemantics M] [R : RegularitySemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (hA : IsNonempty A) :
    ∃ x : Obj (M := M) M.Value, ∃ (_ : In x A), Same (intersect x A) emptySet := by
  obtain ⟨x, hx, disjoint⟩ := R.regularity (denote A) (isSet A) hA
  let a := semanticObject x (M.member_isSet hx)
  refine ⟨a, hx, ?_⟩
  apply S.ext _ _ (isSet (intersect a A)) (isSet emptySet)
  intro y
  constructor
  · intro hy
    obtain ⟨hya, hyA⟩ := (S.sep_members _ _ _).mp hy
    exact False.elim (disjoint y hya hyA)
  · intro hy
    exact False.elim (S.empty_members y hy)

theorem intersectSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Subset (intersect A B) A :=
  fun x h => ((S.sep_members _ _ x).mp h).1

theorem intersectSubsetRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Subset (intersect A B) B :=
  fun x h => ((S.sep_members _ _ x).mp h).2

theorem intersectSubsetOfLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAD : Subset A D) : Subset (intersect A B) D :=
  fun x h => hAD x ((S.sep_members _ _ x).mp h).1

theorem intersectSubsetOfRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hBD : Subset B D) : Subset (intersect A B) D :=
  fun x h => hBD x ((S.sep_members _ _ x).mp h).2

theorem subsetIntersect {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (D : Obj (M := M) γ) (A : Obj (M := M) α) (B : Obj (M := M) β)
    (hDA : Subset D A) (hDB : Subset D B) : Subset D (intersect A B) :=
  fun x h => (S.sep_members _ _ x).mpr ⟨hDA x h, hDB x h⟩

theorem intersectComm {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (intersect A B) (intersect B A) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (denote B))) ↔ M.mem z (S.sepValue (denote B) (fun t => M.mem t (denote A)))
  simp only [S.sep_members, and_comm]

theorem intersectIdem {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (intersect A A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (denote A))) ↔ M.mem z (denote A)
  simp only [S.sep_members, and_self]

theorem intersectEmptyRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (intersect A (emptySet (M := M))) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t S.emptyValue)) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, and_false]

theorem intersectEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (intersect (emptySet (M := M)) A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue S.emptyValue (fun t => M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, false_and]

theorem intersectAssoc {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) : Same (intersect (intersect A B) C) (intersect A (intersect B C)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote A) (fun t => M.mem t (denote B))) (fun t => M.mem t (denote C))) ↔ M.mem z (S.sepValue (denote A) (fun t => M.mem t (S.sepValue (denote B) (fun t => M.mem t (denote C)))))
  simp only [S.sep_members, and_assoc]

theorem unionComm {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (union A B) (union B A) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) (denote B)) ↔ M.mem z (S.unionValue (denote B) (denote A))
  simp only [S.union_members, or_comm]

theorem unionIdem {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (union A A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) (denote A)) ↔ M.mem z (denote A)
  simp only [S.union_members, or_self]

theorem unionEmptyRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (union A (emptySet (M := M))) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) S.emptyValue) ↔ M.mem z (denote A)
  simp only [S.union_members, S.empty_members, or_false]

theorem unionEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (union (emptySet (M := M)) A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue S.emptyValue (denote A)) ↔ M.mem z (denote A)
  simp only [S.union_members, S.empty_members, false_or]

theorem unionAssoc {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) : Same (union (union A B) C) (union A (union B C)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (S.unionValue (denote A) (denote B)) (denote C)) ↔ M.mem z (S.unionValue (denote A) (S.unionValue (denote B) (denote C)))
  simp only [S.union_members, or_assoc]

theorem intersectUnionDistrib {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) : Same (intersect A (union B C)) (union (intersect A B) (intersect A C)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (S.unionValue (denote B) (denote C)))) ↔ M.mem z (S.unionValue (S.sepValue (denote A) (fun t => M.mem t (denote B))) (S.sepValue (denote A) (fun t => M.mem t (denote C))))
  simp only [S.sep_members, S.union_members, and_or_left]

theorem intersectOfSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) : Same (intersect A B) A :=
  setExt _ _ (intersectSubsetLeft A B)
    (subsetIntersect A A B (subsetRefl A) h)

theorem intersectOfSubsetRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset B A) : Same (intersect A B) B :=
  setExt _ _ (intersectSubsetRight A B)
    (subsetIntersect B A B h (subsetRefl B))

theorem intersectCongr {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (D : Obj (M := M) γ) (E : Obj (M := M) δ)
    (hAD : Same A D) (hBE : Same B E) : Same (intersect A B) (intersect D E) := by
  change S.sepValue (denote A) (fun t => M.mem t (denote B)) =
    S.sepValue (denote D) (fun t => M.mem t (denote E))
  rw [hAD, hBE]

theorem unionIntersectDistrib {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) :
    Same (union A (intersect B D)) (intersect (union A B) (union A D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) (S.sepValue (denote B) (fun t => M.mem t (denote D)))) ↔
    M.mem z (S.sepValue (S.unionValue (denote A) (denote B)) (fun t => M.mem t (S.unionValue (denote A) (denote D))))
  simp only [S.sep_members, S.union_members, or_and_left]

structure SetMinusObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance setMinusRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (SetMinusObj (M := M) α β) where
  wd _ := True
  denote p := S.sepValue (denote p.left) (fun t => ¬ M.mem t (denote p.right))
  wd_isSet {p} _ := S.sep_isSet _ _ (isSet p.left)

def setMinus {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (SetMinusObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem inSetMinus_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ) :
    In a (setMinus A B) ↔ In a A ∧ ¬ In a B := S.sep_members _ _ _

theorem setMinusSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Subset (setMinus A B) A :=
  fun z h => ((S.sep_members _ _ z).mp h).1

theorem notInSetMinusOfRight {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : In a B) : ¬ In a (setMinus A B) :=
  fun hx => ((inSetMinus_iff a A B).mp hx).2 h

theorem notInSetMinusOfLeft {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a A) : ¬ In a (setMinus A B) :=
  fun hx => h ((inSetMinus_iff a A B).mp hx).1

theorem setMinusSelf {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (setMinus A A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, and_not_self]

theorem setMinusEmptyRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (setMinus A (emptySet (M := M))) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t S.emptyValue)) ↔ M.mem z (denote A)
  simp only [S.sep_members, S.empty_members, not_false_eq_true, and_true]

theorem setMinusEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (setMinus (emptySet (M := M)) A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue S.emptyValue (fun t => ¬ M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, false_and]

theorem setMinusUnion {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) : Same (setMinus A (union B D)) (intersect (setMinus A B) (setMinus A D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.unionValue (denote B) (denote D)))) ↔ M.mem z (S.sepValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (fun t => M.mem t (S.sepValue (denote A) (fun t => ¬ M.mem t (denote D)))))
  simp only [S.sep_members, S.union_members, not_or]
  constructor
  · intro h; exact ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩
  · intro h; exact ⟨h.1.1, h.1.2, h.2.2⟩

theorem setMinusIntersect {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) : Same (setMinus A (intersect B D)) (union (setMinus A B) (setMinus A D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.sepValue (denote B) (fun t => M.mem t (denote D))))) ↔ M.mem z (S.unionValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (S.sepValue (denote A) (fun t => ¬ M.mem t (denote D))))
  simp only [S.sep_members, S.union_members, not_and_or, and_or_left]

theorem intersectSetMinusEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (intersect A (setMinus B A)) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (S.sepValue (denote B) (fun t => ¬ M.mem t (denote A))))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members]
  exact ⟨fun h => h.2.2 h.1, False.elim⟩

theorem setMinusIntersectEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (intersect (setMinus B A) A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote B) (fun t => ¬ M.mem t (denote A))) (fun t => M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members]
  exact ⟨fun h => h.1.2 h.2, False.elim⟩

theorem setMinusChain {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) :
    Same (setMinus (setMinus A B) D) (setMinus A (union B D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (fun t => ¬ M.mem t (denote D))) ↔
    M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.unionValue (denote B) (denote D))))
  simp only [S.sep_members, S.union_members, not_or, and_assoc]

theorem setMinusChainSwap {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) :
    Same (setMinus (setMinus A B) D) (setMinus A (union D B)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (fun t => ¬ M.mem t (denote D))) ↔
    M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.unionValue (denote D) (denote B))))
  simp only [S.sep_members, S.union_members, not_or]
  exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

theorem notInIntersectOfLeft {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a A) : ¬ In a (intersect A B) :=
  fun hx => h ((inIntersect_iff a A B).mp hx).1

theorem notInIntersectOfRight {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a B) : ¬ In a (intersect A B) :=
  fun hx => h ((inIntersect_iff a A B).mp hx).2

theorem notInUnion {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (hA : ¬ In a A) (hB : ¬ In a B) : ¬ In a (union A B) :=
  fun hx => ((inUnion_iff a A B).mp hx).elim hA hB

theorem subsetTrans {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAB : Subset A B) (hBD : Subset B D) : Subset A D :=
  fun z hz => hBD z (hAB z hz)

theorem unionSubsetOfBoth {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAD : Subset A D) (hBD : Subset B D) : Subset (union A B) D :=
  fun z hz => ((S.union_members _ _ z).mp hz).elim (hAD z) (hBD z)

theorem unionMono {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (D : Obj (M := M) γ) (E : Obj (M := M) δ)
    (hAD : Subset A D) (hBE : Subset B E) : Subset (union A B) (union D E) :=
  fun z hz => (S.union_members _ _ z).mpr (((S.union_members _ _ z).mp hz).elim
    (fun h => Or.inl (hAD z h)) (fun h => Or.inr (hBE z h)))

theorem unionMonoSwap {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (D : Obj (M := M) γ) (E : Obj (M := M) δ)
    (hAE : Subset A E) (hBD : Subset B D) : Subset (union A B) (union D E) :=
  fun z hz => (S.union_members _ _ z).mpr (((S.union_members _ _ z).mp hz).elim
    (fun h => Or.inr (hAE z h)) (fun h => Or.inl (hBD z h)))

theorem powerSetMono {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (hAB : Subset A B) : Subset (powerSet A) (powerSet B) := by
  intro z hz
  obtain ⟨hs, hsub⟩ := (S.power_members _ z).mp hz
  exact (S.power_members _ z).mpr ⟨hs, fun t ht => hAB t (hsub t ht)⟩

theorem setMinusMono {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAB : Subset A B) : Subset (setMinus A D) (setMinus B D) :=
  fun z hz => (S.sep_members _ _ z).mpr
    ⟨hAB z ((S.sep_members _ _ z).mp hz).1, ((S.sep_members _ _ z).mp hz).2⟩

theorem setMinusSubsetOfLeft {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAD : Subset A D) : Subset (setMinus A B) D :=
  subsetTrans _ A D (setMinusSubsetLeft A B) hAD

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Input selection depends on the graph and predicate, not on a signature witness. -/
def IsPreimage (f : M.Value) (P : M.Value → Prop) (r : M.Value) : Prop :=
  M.isSet r ∧ ∀ x, M.mem x r ↔ ∃ y, M.mem (F.pairValue x y) f ∧ P y

noncomputable def preimageValue (f : M.Value) (P : M.Value → Prop) : M.Value :=
  by classical exact if h : ∃ r, IsPreimage f P r then Classical.choose h else F.emptyValue

theorem preimage_spec {D B f : M.Value} (P : M.Value → Prop) (hD : M.isSet D)
    (hf : M.mem f (F.fnSetValue D B)) : IsPreimage f P (preimageValue f P) := by
  have exists_preimage : ∃ r, IsPreimage f P r := by
    refine ⟨F.sepValue D (fun x => P (F.callValue f x)), F.sep_isSet _ _ hD, ?_⟩
    intro x
    rw [F.sep_members]
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨F.callValue f x, F.call_graph D B f x ((F.fnSet_members D B f).mp hf) hx, hp⟩
    · rintro ⟨y, hy, hp⟩
      obtain ⟨hx, eq⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members D B f).mp hf) hy
      exact ⟨hx, eq ▸ hp⟩
  simpa only [preimageValue, dif_pos exists_preimage] using Classical.choose_spec exists_preimage

theorem preimage_mem_iff {D B f x : M.Value} (P : M.Value → Prop) (hD : M.isSet D)
    (hf : M.mem f (F.fnSetValue D B)) :
    M.mem x (preimageValue f P) ↔ M.mem x D ∧ P (F.callValue f x) := by
  rw [(preimage_spec P hD hf).2 x]
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨hx, eq⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members D B f).mp hf) hy
    exact ⟨hx, eq ▸ hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨F.callValue f x, F.call_graph D B f x ((F.fnSet_members D B f).mp hf) hx, hp⟩
end FunctionSemantics

structure PointPreimageObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  target : Obj (M := M) β

noncomputable instance preimageRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (PointPreimageObj (M := M) α β) where
  wd p := ∃ s : FunctionSignature M, In p.function (fnSet s)
  denote p := FunctionSemantics.preimageValue (denote p.function) (fun y => y = denote p.target)
  wd_isSet {p} h := by
    obtain ⟨s, hs⟩ := h
    exact (FunctionSemantics.preimage_spec (fun y => y = denote p.target) s.domain_isSet hs).1

noncomputable def preimage {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (target : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In f (fnSet s)) :
    Obj (M := M) (PointPreimageObj (M := M) α β) := ⟨⟨f, target⟩, ⟨s, hf⟩⟩

theorem preimageMembers {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (PointPreimageObj (M := M) α β))
    (s : FunctionSignature M) (hf : In p.val.function (fnSet s)) (x : M.Value) :
    M.mem x (denote p) ↔ M.mem x s.domain ∧
      F.callValue (denote p.val.function) x = denote p.val.target :=
  FunctionSemantics.preimage_mem_iff _ s.domain_isSet hf

structure SetPreimageObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  target : Obj (M := M) β

noncomputable instance preimageSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (SetPreimageObj (M := M) α β) where
  wd p := ∃ s : FunctionSignature M, In p.function (fnSet s)
  denote p := FunctionSemantics.preimageValue (denote p.function) (fun y => M.mem y (denote p.target))
  wd_isSet {p} h := by
    obtain ⟨s, hs⟩ := h
    exact (FunctionSemantics.preimage_spec (fun y => M.mem y (denote p.target)) s.domain_isSet hs).1

noncomputable def preimageSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (target : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In f (fnSet s)) :
    Obj (M := M) (SetPreimageObj (M := M) α β) := ⟨⟨f, target⟩, ⟨s, hf⟩⟩

theorem preimageSetMembers {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (SetPreimageObj (M := M) α β))
    (s : FunctionSignature M) (hf : In p.val.function (fnSet s)) (x : M.Value) :
    M.mem x (denote p) ↔ M.mem x s.domain ∧
      M.mem (F.callValue (denote p.val.function) x) (denote p.val.target) :=
  FunctionSemantics.preimage_mem_iff _ s.domain_isSet hf

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Complete presentations of one graph have the same input members. -/
theorem domain_mem_iff {f D B E C x : M.Value}
    (hf : M.mem f (F.fnSetValue D B)) (hg : M.mem f (F.fnSetValue E C)) :
    M.mem x D ↔ M.mem x E := by
  constructor
  · intro hx
    exact (FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hg)
      (F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hf) hx)).1
  · intro hx
    exact (FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hf)
      (F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hg) hx)).1

/-- Graph composition mentions only its operands, never a signature witness. -/
def IsComposition (f g r : M.Value) : Prop :=
  M.isSet r ∧ ∀ edge, M.mem edge r ↔
    ∃ x y z, M.mem (F.pairValue x y) g ∧ M.mem (F.pairValue y z) f ∧ edge = F.pairValue x z

noncomputable def compositionValue (f g : M.Value) : M.Value := by
  classical
  exact if h : ∃ r, IsComposition f g r then Classical.choose h else F.emptyValue

theorem composition_graph_spec {f g D E B C : M.Value}
    (hf : M.mem f (F.fnSetValue E C)) (hg : M.mem g (F.fnSetValue D B))
    (hc : ∀ x, M.mem x D → M.mem (F.callValue g x) E) :
    IsComposition f g (F.graphValue D C (fun x => F.callValue f (F.callValue g x))) := by
  have hreturn : ∀ x, M.mem x D → M.mem (F.callValue f (F.callValue g x)) C :=
    fun x hx => call_mem _ _ _ _ hf (hc x hx)
  refine ⟨M.member_isSet (graph_inFnSet _ _ _ hreturn), ?_⟩
  intro edge
  constructor
  · intro he
    obtain ⟨x, hx, z, _, heq, hz⟩ := (F.graph_members _ _ _ _).mp he
    refine ⟨x, F.callValue g x, z, F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hg) hx, ?_, heq⟩
    rw [hz]
    exact F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hf) (hc x hx)
  · rintro ⟨x, y, z, hxy, hyz, rfl⟩
    obtain ⟨hx, hy⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hg) hxy
    obtain ⟨_, hz⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hf) hyz
    apply (pair_mem_graph _ _ _ _ _).mpr
    refine ⟨hx, ?_, ?_⟩
    · rw [hz, hy]
      exact hreturn x hx
    · rw [hz, hy]

theorem composition_spec {f g D E B C : M.Value}
    (hf : M.mem f (F.fnSetValue E C)) (hg : M.mem g (F.fnSetValue D B))
    (hc : ∀ x, M.mem x D → M.mem (F.callValue g x) E) :
    IsComposition f g (compositionValue f g) := by
  have h : ∃ r, IsComposition f g r := ⟨_, composition_graph_spec hf hg hc⟩
  simpa only [compositionValue, dif_pos h] using Classical.choose_spec h

theorem composition_eq_graph {f g D E B C : M.Value}
    (hf : M.mem f (F.fnSetValue E C)) (hg : M.mem g (F.fnSetValue D B))
    (hc : ∀ x, M.mem x D → M.mem (F.callValue g x) E) :
    compositionValue f g = F.graphValue D C (fun x => F.callValue f (F.callValue g x)) := by
  have hs := composition_spec hf hg hc
  have ht := composition_graph_spec hf hg hc
  exact F.ext _ _ hs.1 ht.1 (fun p => (hs.2 p).trans (ht.2 p).symm)

end FunctionSemantics

structure CompositionObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  outer : Obj (M := M) α
  inner : Obj (M := M) β

noncomputable instance compositionRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CompositionObj (M := M) α β) where
  wd c := ∃ s t : FunctionSignature M, In c.outer (fnSet s) ∧ In c.inner (fnSet t) ∧
    ∀ x, M.mem x t.domain → M.mem (F.callValue (denote c.inner) x) s.domain
  denote c := FunctionSemantics.compositionValue (denote c.outer) (denote c.inner)
  wd_isSet {c} h := by
    obtain ⟨s, t, hf, hg, hc⟩ := h
    exact (FunctionSemantics.composition_spec hf hg hc).1

noncomputable def compose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (g : Obj (M := M) β) (s t : FunctionSignature M)
    (hf : In f (fnSet s)) (hg : In g (fnSet t))
    (hc : ∀ x, M.mem x t.domain → M.mem (F.callValue (denote g) x) s.domain) :
    Obj (M := M) (CompositionObj (M := M) α β) := ⟨⟨f, g⟩, ⟨s, t, hf, hg, hc⟩⟩

/-- A cached composition remains compatible under any checked complete interfaces. -/
theorem composeCompatible {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t)) :
    ∀ x, M.mem x t.domain → M.mem (F.callValue (denote c.val.inner) x) s.domain := by
  obtain ⟨s₀, t₀, hf₀, hg₀, hc₀⟩ := c.wd
  intro x hx
  exact (FunctionSemantics.domain_mem_iff hf₀ hf).mp
    (hc₀ x ((FunctionSemantics.domain_mem_iff hg hg₀).mp hx))

theorem composeGraph {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t)) :
    denote c = F.graphValue t.domain s.output
      (fun x => F.callValue (denote c.val.outer) (F.callValue (denote c.val.inner) x)) :=
  FunctionSemantics.composition_eq_graph hf hg (composeCompatible c s t hf hg)

theorem composeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t)) :
    In c (fnSet (FunctionSignature.ofDomain t.domain s.output t.domain_isSet s.output_isSet)) := by
  change M.mem (denote c) (F.fnSetValue t.domain s.output)
  rw [composeGraph c s t hf hg]
  exact FunctionSemantics.graph_inFnSet _ _ _ (fun x hx =>
    FunctionSemantics.call_mem _ _ _ _ hf (composeCompatible c s t hf hg x hx))

theorem composeCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t))
    (x : M.Value) (hx : M.mem x t.domain) :
    F.callValue (denote c) x = F.callValue (denote c.val.outer) (F.callValue (denote c.val.inner) x) := by
  rw [composeGraph c s t hf hg]
  exact FunctionSemantics.call_graphValue _ _ _ (fun a ha =>
    FunctionSemantics.call_mem _ _ _ _ hf (composeCompatible c s t hf hg a ha)) _ hx

theorem callInputInDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallObj (M := M) α β)) (s : FunctionSignature M)
    (hf : In c.val.function (fnSet s)) : M.mem (denote c.val.argument) s.domain :=
  (FunctionSemantics.domain_mem_iff c.wd.1 hf).mp
    ((FunctionSignature.oneTarget_domain _ _ _ _ _).mpr c.wd.2)

theorem callOnInputInDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallOnObj (M := M) α β)) (s : FunctionSignature M)
    (hf : In c.val.function (fnSet s)) : M.mem (denote c.val.argument) s.domain :=
  (FunctionSemantics.domain_mem_iff c.wd.1 hf).mp c.wd.2


namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem composition_pair_iff {f g c x z : M.Value} (hc : IsComposition f g c) :
    M.mem (F.pairValue x z) c ↔ ∃ y, M.mem (F.pairValue x y) g ∧ M.mem (F.pairValue y z) f := by
  constructor
  · intro h
    obtain ⟨a, y, b, hay, hyb, heq⟩ := (hc.2 _).mp h
    obtain ⟨rfl, rfl⟩ := F.pair_injective heq
    exact ⟨y, hay, hyb⟩
  · rintro ⟨y, hxy, hyz⟩
    exact (hc.2 _).mpr ⟨x, y, z, hxy, hyz, rfl⟩

theorem composition_associative {f g h fg gh left right : M.Value}
    (hfg : IsComposition f g fg) (hgh : IsComposition g h gh)
    (hl : IsComposition fg h left) (hr : IsComposition f gh right) : left = right := by
  apply F.ext _ _ hl.1 hr.1
  intro edge
  constructor
  · intro he
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := (hl.2 edge).mp he
    obtain ⟨a, hya, haz⟩ := (composition_pair_iff hfg).mp hyz
    exact (hr.2 _).mpr ⟨x, a, z, (composition_pair_iff hgh).mpr ⟨y, hxy, hya⟩, haz, rfl⟩
  · intro he
    obtain ⟨x, a, z, hxa, haz, rfl⟩ := (hr.2 edge).mp he
    obtain ⟨y, hxy, hya⟩ := (composition_pair_iff hgh).mp hxa
    exact (hl.2 _).mpr ⟨x, y, z, hxy, (composition_pair_iff hfg).mpr ⟨a, hya, haz⟩, rfl⟩

end FunctionSemantics

theorem composeSpec {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) :
    FunctionSemantics.IsComposition (denote c.val.outer) (denote c.val.inner) (denote c) := by
  obtain ⟨s, t, hf, hg, hc⟩ := c.wd
  exact FunctionSemantics.composition_spec hf hg hc

theorem composeLeftIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (identity : Obj (M := M) (FormulaFn M)) (heq : Same c.val.outer identity)
    (hbody : ∀ x, identity.val.bodyValue x = x) : Same c c.val.inner := by
  obtain ⟨s, t, hf, hg, hc⟩ := c.wd
  have hi : In c.val.outer (fnSet identity.val.signature) := by
    change M.mem (denote c.val.outer) _
    rw [heq]
    exact formulaFnInFnSet identity
  apply functionExtOnDomain c c.val.inner
    (FunctionSignature.ofDomain t.domain s.output t.domain_isSet s.output_isSet) t
    (composeInFnSet c s t hf hg) hg rfl
  intro x hx
  rw [composeCall c s t hf hg x hx, heq]
  exact (FunctionSemantics.call_graphValue _ _ _ identity.wd _
    ((FunctionSemantics.domain_mem_iff hf hi).mp (hc x hx))).trans (hbody _)

theorem composeRightIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (identity : Obj (M := M) (FormulaFn M)) (heq : Same c.val.inner identity)
    (hbody : ∀ x, identity.val.bodyValue x = x)
    (s : FunctionSignature M) (hf : In c.val.outer (fnSet s))
    (hD : s.domain = identity.val.signature.domain) : Same c c.val.outer := by
  obtain ⟨s₀, t, hf₀, hg, hc⟩ := c.wd
  have hi : In c.val.inner (fnSet identity.val.signature) := by
    change M.mem (denote c.val.inner) _
    rw [heq]
    exact formulaFnInFnSet identity
  have hdomain : t.domain = identity.val.signature.domain :=
    F.ext _ _ t.domain_isSet identity.val.signature.domain_isSet
      (fun x => FunctionSemantics.domain_mem_iff hg hi)
  apply functionExtOnDomain c c.val.outer
    (FunctionSignature.ofDomain t.domain s₀.output t.domain_isSet s₀.output_isSet) s
    (composeInFnSet c s₀ t hf₀ hg) hf (hdomain.trans hD.symm)
  intro x hx
  rw [composeCall c s₀ t hf₀ hg x hx, heq]
  exact congrArg (F.callValue (denote c.val.outer))
    ((FunctionSemantics.call_graphValue _ _ _ identity.wd _ (hdomain ▸ hx)).trans (hbody x))

theorem composeEqFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (f : Obj (M := M) (FormulaFn M)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t))
    (hD : t.domain = f.val.signature.domain)
    (hbody : ∀ x, M.mem x t.domain → f.val.bodyValue x =
      F.callValue (denote c.val.outer) (F.callValue (denote c.val.inner) x)) : Same c f := by
  apply functionExtOnDomain c f
    (FunctionSignature.ofDomain t.domain s.output t.domain_isSet s.output_isSet)
    f.val.signature (composeInFnSet c s t hf hg) (formulaFnInFnSet f) hD
  intro x hx
  rw [composeCall c s t hf hg x hx]
  exact ((FunctionSemantics.call_graphValue _ _ _ f.wd _ (hD ▸ hx)).trans (hbody x hx)).symm

theorem composeRangeSubset {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (r : Obj (M := M) (FunctionRange (M := M) γ))
    (q : Obj (M := M) (FunctionRange (M := M) δ))
    (hr : Same r.val.function c) (hq : Same q.val.function c.val.outer) : Subset r q := by
  obtain ⟨s, t, hf, hg, hc⟩ := c.wd
  intro z hz
  change M.mem z (FunctionSemantics.rangeValue (denote q.val.function))
  change M.mem z (FunctionSemantics.rangeValue (denote r.val.function)) at hz
  rw [hr] at hz
  rw [hq]
  obtain ⟨a, ha, rfl⟩ := (FunctionSemantics.range_mem_iff s.output_isSet
    (composeInFnSet c s t hf hg)).mp hz
  exact (FunctionSemantics.range_mem_iff s.output_isSet hf).mpr
    ⟨F.callValue (denote c.val.inner) a, hc a ha, composeCall c s t hf hg a ha⟩

end Litex

namespace Litex

def memberSet {M : Semantics.{u}} (A : M.Value) : Set M.Value := {x | M.mem x A}

def IsFiniteSet {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := (memberSet (denote A)).Finite

noncomputable def finiteCard {M : Semantics.{u}} (A : M.Value) : ℕ :=
  (memberSet A).ncard

structure FiniteSetSizeObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance finiteSetSizeRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (FiniteSetSizeObj (M := M) α) where
  wd p := IsFiniteSet p.set
  denote p := M.number (finiteCard (denote p.set) : ℂ)
  wd_isSet _ := M.member_isSet ((M.natural_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteSetSize {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : IsFiniteSet A) : Obj (M := M) (FiniteSetSizeObj (M := M) α) :=
  ⟨⟨A⟩, h⟩

theorem finiteSetSizeInN {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) : In p N :=
  (M.natural_members _).mpr ⟨_, rfl⟩

theorem memberSet_empty {M : Semantics.{u}} [S : SetSemantics M] :
    memberSet S.emptyValue = ∅ := by
  ext x
  exact ⟨fun h => (S.empty_members x h).elim, False.elim⟩

theorem memberSet_insert {M : Semantics.{u}} [S : SetSemantics M] (a A : M.Value) :
    memberSet (S.insertValue a A) = Insert.insert a (memberSet A) := by
  ext x
  exact S.insert_members a A x

theorem finiteSetEmpty {M : Semantics.{u}} [S : SetSemantics M] :
    IsFiniteSet (emptySet (M := M)) := by
  change (memberSet S.emptyValue).Finite
  rw [memberSet_empty]
  exact Set.finite_empty

theorem finiteSetInsert {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (h : IsFiniteSet p.val.tail) :
    IsFiniteSet p := by
  change (memberSet (S.insertValue _ _)).Finite
  rw [memberSet_insert]
  exact h.insert _

theorem finiteCardEmpty {M : Semantics.{u}} [S : SetSemantics M] :
    finiteCard S.emptyValue = 0 := by rw [finiteCard, memberSet_empty, Set.ncard_empty]

theorem finiteCardInsert {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (h : IsFiniteSet p.val.tail) :
    finiteCard (denote p) = finiteCard (denote p.val.tail) + 1 := by
  change (memberSet (S.insertValue _ _)).ncard = _
  rw [memberSet_insert]
  exact Set.ncard_insert_of_notMem (s := memberSet (denote p.val.tail)) (a := denote p.val.element) p.wd h

theorem finiteSetSizeDenote {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) (n : ℕ)
    (h : finiteCard (denote p.val.set) = n) : denote p = M.number (n : ℂ) := by
  change M.number ((finiteCard _) : ℂ) = _
  rw [h]

theorem finiteSetSizeNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) : Le (number 0) p := by
  refine ⟨0, (finiteCard (denote p.val.set) : ℝ), ?_, ?_, Nat.cast_nonneg _⟩
  · change M.number (0 : ℂ) = M.number ((0 : ℝ) : ℂ)
    rfl
  · change M.number ((finiteCard _) : ℂ) = _
    rw [Complex.ofReal_natCast]

/-- Real observations of members, independent of any finiteness/WD proof. -/
def realMembers {M : Semantics.{u}} (A : M.Value) : Set ℝ :=
  {r | M.mem (M.number (r : ℂ)) A}

theorem realMembers_finite {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : IsFiniteSet A) : (realMembers (denote A)).Finite :=
  Set.Finite.preimage (M.number_injective.comp Complex.ofReal_injective).injOn h

theorem realMembers_nonempty {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : IsNonempty A) (hr : Subset A R) :
    (realMembers (denote A)).Nonempty := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨r, he⟩ := (M.real_members a).mp (hr a ha)
  refine ⟨r, ?_⟩
  change M.mem (M.number (r : ℂ)) (denote A)
  rw [← he]
  exact ha

noncomputable def finiteExtremumValue {M : Semantics.{u}} (maximum : Bool) (A : M.Value) : ℝ :=
  if maximum then sSup (realMembers A) else sInf (realMembers A)

structure FiniteExtremumObj {M : Semantics.{u}} (maximum : Bool) (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance finiteExtremumRepresentation {M : Semantics.{u}} (maximum : Bool)
    {α : Type v} [Representation M α] : Representation M (FiniteExtremumObj (M := M) maximum α) where
  wd p := IsFiniteSet p.set ∧ IsNonempty p.set ∧ Subset p.set R
  denote p := M.number (finiteExtremumValue maximum (denote p.set) : ℂ)
  wd_isSet _ := M.member_isSet ((M.real_members _).mpr ⟨_, rfl⟩)


noncomputable def finiteExtremum {M : Semantics.{u}} (maximum : Bool)
    {α : Type v} [Representation M α] (A : Obj (M := M) α)
    (hf : IsFiniteSet A) (hn : IsNonempty A) (hr : Subset A R) :
    Obj (M := M) (FiniteExtremumObj (M := M) maximum α) := ⟨⟨A⟩, hf, hn, hr⟩

theorem finiteExtremumInR {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α)) : In p R :=
  (M.real_members _).mpr ⟨_, rfl⟩

theorem finiteExtremumInSet {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α)) : In p p.val.set := by
  have hf := realMembers_finite p.val.set p.wd.1
  have hn := realMembers_nonempty p.val.set p.wd.2.1 p.wd.2.2
  cases maximum
  · exact hn.csInf_mem hf
  · exact hn.csSup_mem hf

theorem finiteExtremumDenote {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α)) (r : ℝ)
    (hr : M.mem (M.number (r : ℂ)) (denote p.val.set))
    (hb : ∀ x ∈ realMembers (denote p.val.set), if maximum then x ≤ r else r ≤ x) :
    denote p = M.number (r : ℂ) := by
  have hf := realMembers_finite p.val.set p.wd.1
  have hn := realMembers_nonempty p.val.set p.wd.2.1 p.wd.2.2
  apply congrArg (fun x : ℝ => M.number (x : ℂ))
  cases maximum
  · exact le_antisymm (csInf_le hf.bddBelow hr) (le_csInf hn hb)
  · exact le_antisymm (csSup_le hn hb) (le_csSup hf.bddAbove hr)

theorem finiteExtremumBound {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α))
    (a : Obj (M := M) β) (ha : In a p.val.set) : if maximum then Le a p else Le p a := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp (p.wd.2.2 (denote a) ha)
  have hm : r ∈ realMembers (denote p.val.set) := by
    change M.mem (M.number (r : ℂ)) (denote p.val.set)
    rw [← hr]
    exact ha
  have hf := realMembers_finite p.val.set p.wd.1
  cases maximum
  · exact ⟨_, r, rfl, hr, csInf_le hf.bddBelow hm⟩
  · exact ⟨r, _, hr, rfl, le_csSup hf.bddAbove hm⟩


theorem finiteMembersEmpty {M : Semantics.{u}} [S : SetSemantics M] (x : M.Value) :
    M.mem x (denote (emptySet (M := M))) ↔ x ∈ ([] : List M.Value) := by
  exact ⟨fun h => (S.empty_members x h).elim, fun h => (List.not_mem_nil h).elim⟩

theorem finiteMembersInsert {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (a : M.Value) (xs : List M.Value)
    (he : denote p.val.element = a)
    (ht : ∀ x, M.mem x (denote p.val.tail) ↔ x ∈ xs) :
    ∀ x, M.mem x (denote p) ↔ x ∈ a :: xs := by
  intro x
  change M.mem x (S.insertValue _ _) ↔ _
  rw [S.insert_members, he, ht, List.mem_cons]

theorem finiteExtremumListDenote {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α))
    (xs : List ℝ) (r : ℝ)
    (hm : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs.map (fun q : ℝ => M.number (q : ℂ)))
    (hs : r ∈ xs) (hb : ∀ x ∈ xs, if maximum then x ≤ r else r ≤ x) :
    denote p = M.number (r : ℂ) := by
  apply finiteExtremumDenote p r
  · exact (hm _).mpr ((List.mem_map (f := fun q : ℝ => M.number (q : ℂ))).mpr ⟨r, hs, rfl⟩)
  · intro x hx
    obtain ⟨q, hq, he⟩ := (List.mem_map (f := fun q : ℝ => M.number (q : ℂ))).mp ((hm _).mp hx)
    have hqx : q = x := Complex.ofReal_injective (M.number_injective he)
    exact hqx ▸ hb q hq

end Litex

namespace Litex

namespace NativeBridge
variable {M : Semantics.{u}}

/-- Total observations of the fixed denotation. Source WD supplies their domains. -/
noncomputable def complexValue (a : M.Value) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, a = M.number z then Classical.choose h else 0

theorem complexValue_number (z : ℂ) : complexValue (M.number z) = z := by
  classical
  have h : ∃ w : ℂ, M.number z = M.number w := ⟨z, rfl⟩
  unfold complexValue
  rw [dif_pos h]
  exact (M.number_injective (Classical.choose_spec h)).symm

theorem complexValue_spec (a : M.Value) (ha : M.mem a (M.standard .complex)) :
    a = M.number (complexValue a) := by
  obtain ⟨z, rfl⟩ := (M.complex_members a).mp ha
  rw [complexValue_number]

noncomputable def integerValue (a : M.Value) : ℤ := by
  classical
  exact if h : ∃ k : ℤ, a = M.number (k : ℂ) then Classical.choose h else 0

theorem integerValue_number (k : ℤ) : integerValue (M.number (k : ℂ)) = k := by
  classical
  have h : ∃ j : ℤ, M.number (k : ℂ) = M.number (j : ℂ) := ⟨k, rfl⟩
  unfold integerValue
  rw [dif_pos h]
  have he := M.number_injective (Classical.choose_spec h)
  exact_mod_cast he.symm

theorem integerValue_spec (a : M.Value) (ha : M.mem a (M.standard .integer)) :
    a = M.number (integerValue a : ℂ) := by
  obtain ⟨k, rfl⟩ := (M.integer_members a).mp ha
  rw [integerValue_number]

end NativeBridge

noncomputable def nativeRangeAggregate (product : Bool) (first last : ℤ)
    (value : ℤ → ℂ) : ℂ :=
  if product then ∏ i ∈ Finset.Icc first last, value i
  else ∑ i ∈ Finset.Icc first last, value i

structure RangeAggregateObj {M : Semantics.{u}} (product : Bool)
    (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  first : Obj (M := M) α
  last : Obj (M := M) β
  function : Obj (M := M) γ
  signature : FunctionSignature M

noncomputable instance rangeAggregateRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] (product : Bool)
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (RangeAggregateObj (M := M) product α β γ) where
  wd p := In p.first Z ∧ In p.last Z ∧ Le p.first p.last ∧
    In p.function (fnSet p.signature) ∧
    (∀ y, M.mem y p.signature.output → M.mem y (M.standard .complex)) ∧
    (∀ k : ℤ, NativeBridge.integerValue (denote p.first) ≤ k →
      k ≤ NativeBridge.integerValue (denote p.last) →
      M.mem (M.number (k : ℂ)) p.signature.domain)
  denote p := M.number (nativeRangeAggregate product
    (NativeBridge.integerValue (denote p.first))
    (NativeBridge.integerValue (denote p.last))
    (fun k => NativeBridge.complexValue (F.callValue (denote p.function) (M.number (k : ℂ)))))
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def rangeAggregate {M : Semantics.{u}} [FunctionSemantics M]
    (product : Bool) {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (f : Obj (M := M) γ)
    (s : FunctionSignature M) (ha : In a Z) (hb : In b Z) (hle : Le a b)
    (hf : In f (fnSet s))
    (hr : ∀ y, M.mem y s.output → M.mem y (M.standard .complex))
    (hd : ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → M.mem (M.number (k : ℂ)) s.domain) :
    Obj (M := M) (RangeAggregateObj (M := M) product α β γ) :=
  ⟨⟨a, b, f, s⟩, ha, hb, hle, hf, hr, hd⟩

theorem rangeAggregateInC {M : Semantics.{u}} [FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ)) : In p C :=
  (M.complex_members _).mpr ⟨_, rfl⟩

theorem rangeAggregateCallInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (k : ℤ) (ha : NativeBridge.integerValue (denote p.val.first) ≤ k)
    (hb : k ≤ NativeBridge.integerValue (denote p.val.last)) :
    M.mem (F.callValue (denote p.val.function) (M.number (k : ℂ))) (M.standard .complex) :=
  p.wd.2.2.2.2.1 _ (FunctionSemantics.call_mem _ _ _ _ p.wd.2.2.2.1
    (p.wd.2.2.2.2.2 k ha hb))

theorem rangeAggregateDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (a b : ℤ) (ha : denote p.val.first = M.number (a : ℂ))
    (hb : denote p.val.last = M.number (b : ℂ)) (value : ℂ)
    (h : nativeRangeAggregate product a b
      (fun k => NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number (k : ℂ)))) = value) :
    denote p = M.number value := by
  change M.number (nativeRangeAggregate product _ _ _) = _
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number, h]

theorem integerInUnboundedCarrier {M : Semantics.{u}} (A : StandardSetValue)
    (h : A ≠ .natural) (k : ℤ) : M.mem (M.number (k : ℂ)) (M.standard A) := by
  cases A
  · exact (h rfl).elim
  · exact NativeBridge.numberInZ k
  · exact integerToRational (number (k : ℂ)) (NativeBridge.numberInZ k)
  · exact integerToReal (number (k : ℂ)) (NativeBridge.numberInZ k)
  · exact numberInC (k : ℂ)

theorem unguardedIntegerDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B) (h : A ≠ .natural)
    (k : ℤ) : M.mem (M.number (k : ℂ))
      (FunctionSignature.oneTarget A B hB (fun _ => True)).domain :=
  (FunctionSignature.oneTarget_domain A B hB (fun _ => True) _).mpr
    ⟨integerInUnboundedCarrier A h k, True.intro⟩

theorem standardZeroMember {M : Semantics.{u}} (A : StandardSetValue) :
    M.mem (M.number 0) (M.standard A) := by
  cases A
  · exact (M.natural_members _).mpr ⟨0, by simp⟩
  · exact (M.integer_members _).mpr ⟨0, by simp⟩
  · exact (M.rational_members _).mpr ⟨0, by simp⟩
  · exact (M.real_members _).mpr ⟨0, by simp⟩
  · exact (M.complex_members _).mpr ⟨0, by simp⟩

theorem standardOneMember {M : Semantics.{u}} (A : StandardSetValue) :
    M.mem (M.number 1) (M.standard A) := by
  cases A
  · exact (M.natural_members _).mpr ⟨1, by simp⟩
  · exact (M.integer_members _).mpr ⟨1, by simp⟩
  · exact (M.rational_members _).mpr ⟨1, by simp⟩
  · exact (M.real_members _).mpr ⟨1, by simp⟩
  · exact (M.complex_members _).mpr ⟨1, by simp⟩

theorem standardAddMember {M : Semantics.{u}} (A : StandardSetValue)
    (a b : ℂ) (ha : M.mem (M.number a) (M.standard A))
    (hb : M.mem (M.number b) (M.standard A)) :
    M.mem (M.number (a + b)) (M.standard A) := by
  rw [← M.add_numbers]
  cases A
  · exact addInN (number a) (number b) ha hb
  · exact addInZ (number a) (number b) ha hb
  · exact addInQ (number a) (number b) ha hb
  · exact addInR (number a) (number b) ha hb
  · exact addInC (number a) (number b) ha hb

theorem standardMulMember {M : Semantics.{u}} (A : StandardSetValue)
    (a b : ℂ) (ha : M.mem (M.number a) (M.standard A))
    (hb : M.mem (M.number b) (M.standard A)) :
    M.mem (M.number (a * b)) (M.standard A) := by
  rw [← M.mul_numbers]
  cases A
  · exact mulInN (number a) (number b) ha hb
  · exact mulInZ (number a) (number b) ha hb
  · exact mulInQ (number a) (number b) ha hb
  · exact mulInR (number a) (number b) ha hb
  · exact mulInC (number a) (number b) ha hb

theorem nativeRangeAggregateMember {M : Semantics.{u}} (product : Bool)
    (A : StandardSetValue) (a b : ℤ) (value : ℤ → ℂ)
    (h : ∀ i ∈ Finset.Icc a b, M.mem (M.number (value i)) (M.standard A)) :
    M.mem (M.number (nativeRangeAggregate product a b value)) (M.standard A) := by
  unfold nativeRangeAggregate
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    generalize Finset.Icc a b = s at *
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember A _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    generalize Finset.Icc a b = s at *
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember A _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem rangeAggregateMember {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (A : StandardSetValue) (hs : p.val.signature.output = M.standard A) :
    In p (standardSet A) := by
  apply nativeRangeAggregateMember product A
  intro i hi
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hi
  rw [← NativeBridge.complexValue_spec _ (rangeAggregateCallInC p i ha hb)]
  rw [← hs]
  exact FunctionSemantics.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2.2 i ha hb)

end Litex

namespace Litex

/-- The finite fold observes semantic members; no WD proof selects its value. -/
noncomputable def finiteAggregateValue {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (value : M.Value → ℂ) : ℂ := by
  classical
  exact if h : (memberSet A).Finite then
    if product then ∏ x ∈ h.toFinset, value x else ∑ x ∈ h.toFinset, value x
  else if product then 1 else 0

structure FiniteAggregateObj {M : Semantics.{u}} (product : Bool)
    (α : Type v) (β : Type w) [Representation M α] [Representation M β] where
  set : Obj (M := M) α
  function : Obj (M := M) β
  input : StandardSetValue
  signature : FunctionSignature M

noncomputable instance finiteAggregateRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] (product : Bool)
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (FiniteAggregateObj (M := M) product α β) where
  wd p := IsFiniteSet p.set ∧ Subset p.set (standardSet p.input) ∧
    (∀ y, M.mem y p.signature.output → M.mem y (M.standard .complex)) ∧
    In p.function (fnSet p.signature) ∧
    (∀ x, M.mem x (M.standard p.input) → M.mem x p.signature.domain)
  denote p := M.number (finiteAggregateValue product (denote p.set)
    (fun x => NativeBridge.complexValue (F.callValue (denote p.function) x)))
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteAggregate {M : Semantics.{u}} [FunctionSemantics M]
    (product : Bool) {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (f : Obj (M := M) β)
    (input : StandardSetValue) (s : FunctionSignature M)
    (hf : IsFiniteSet A) (hi : Subset A (standardSet input))
    (hr : ∀ y, M.mem y s.output → M.mem y (M.standard .complex))
    (hfn : In f (fnSet s))
    (hd : ∀ x, M.mem x (M.standard input) → M.mem x s.domain) :
    Obj (M := M) (FiniteAggregateObj (M := M) product α β) :=
  ⟨⟨A, f, input, s⟩, hf, hi, hr, hfn, hd⟩

theorem finiteAggregateCallInOutput {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (x : M.Value) (hx : M.mem x (denote p.val.set)) :
    M.mem (F.callValue (denote p.val.function) x) p.val.signature.output :=
  F.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2 x (p.wd.2.1 x hx))

theorem finiteAggregateMember {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (A : StandardSetValue) (hs : p.val.signature.output = M.standard A) :
    In p (standardSet A) := by
  classical
  have hm : ∀ x ∈ p.wd.1.toFinset,
      M.mem (M.number (NativeBridge.complexValue (F.callValue (denote p.val.function) x)))
        (M.standard A) := by
    intro x hx
    have ho := finiteAggregateCallInOutput p x (p.wd.1.mem_toFinset.mp hx)
    rw [← NativeBridge.complexValue_spec _ (p.wd.2.2.1 _ ho), ← hs]
    exact ho
  change M.mem (M.number (finiteAggregateValue product _ _)) (M.standard A)
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf]
  generalize p.wd.1.toFinset = s at *
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))

theorem finiteAggregateListDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (xs : List ℂ) (value : ℂ)
    (hm : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs.map M.number)
    (hc : (if product then ∏ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))
      else ∑ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))) = value) :
    denote p = M.number value := by
  classical
  have ht : p.wd.1.toFinset = xs.toFinset.image M.number := by
    ext x
    rw [Set.Finite.mem_toFinset]
    change M.mem x (denote p.val.set) ↔ _
    rw [hm]
    simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]
  change M.number (finiteAggregateValue product _ _) = _
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf, ht]
  apply congrArg M.number
  have hi : ∀ a ∈ xs.toFinset, ∀ b ∈ xs.toFinset, M.number a = M.number b → a = b :=
    fun _ _ _ _ h => M.number_injective h
  cases product
  · simpa only [Bool.false_eq_true, ↓reduceIte, Finset.sum_image hi] using hc
  · simpa only [↓reduceIte, Finset.prod_image hi] using hc

end Litex

namespace Litex

def realBound {M : Semantics.{u}} (closed : Bool) (a b : M.Value) : Prop :=
  if closed then ∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s
  else ∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r < s

theorem realBound_iff {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (closed : Bool)
    (a : Obj (M := M) α) (b : Obj (M := M) β) :
    realBound closed (denote a) (denote b) ↔ (if closed then Le a b else Lt a b) := by
  cases closed <;> rfl

theorem realBound_le {M : Semantics.{u}} {c : Bool} {a b : M.Value}
    (h : realBound c a b) : realBound true a b := by
  cases c
  · obtain ⟨r,s,hr,hs,h⟩ := h; exact ⟨r,s,hr,hs,h.le⟩
  · exact h

theorem realBound_not_opposite {M : Semantics.{u}} {c : Bool} {a b : M.Value}
    (h : realBound c a b) : ¬ realBound (!c) b a := by
  cases c <;> intro g
  all_goals
    obtain ⟨r,s,hr,hs,h⟩ := h
    obtain ⟨t,q,ht,hq,g⟩ := g
    have hst : s = t := Complex.ofReal_injective (M.number_injective (hs.symm.trans ht))
    have hrq : r = q := Complex.ofReal_injective (M.number_injective (hr.symm.trans hq))
    subst t; subst q
    linarith

structure RealIntervalObj {M : Semantics.{u}} (lc rc : Bool)
    (α : Type v) (β : Type w) [Representation M α] [Representation M β] where
  lower : Obj (M := M) α
  upper : Obj (M := M) β

instance realIntervalRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    (lc rc : Bool) {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (RealIntervalObj (M := M) lc rc α β) where
  wd p := In p.lower R ∧ In p.upper R
  denote p := S.sepValue (M.standard .real)
    (fun a => realBound lc (denote p.lower) a ∧ realBound rc a (denote p.upper))
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .real)

def realInterval {M : Semantics.{u}} [SetSemantics M] (lc rc : Bool)
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a R) (hb : In b R) :
    Obj (M := M) (RealIntervalObj (M := M) lc rc α β) := ⟨⟨a,b⟩,ha,hb⟩

theorem inRealInterval_iff {M : Semantics.{u}} [S : SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) (a : Obj (M := M) γ) :
    In a p ↔ In a R ∧ (if lc then Le p.val.lower a else Lt p.val.lower a) ∧
      (if rc then Le a p.val.upper else Lt a p.val.upper) := by
  change M.mem (denote a) (S.sepValue _ _) ↔ _
  rw [S.sep_members, realBound_iff, realBound_iff]
  rfl

theorem realIntervalSubsetR {M : Semantics.{u}} [S : SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) : Subset p R :=
  fun _ h => (S.sep_members _ _ _).mp h |>.1

theorem notInRealIntervalLower {M : Semantics.{u}} [SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) (a : Obj (M := M) γ)
    (h : Lt a p.val.lower) : ¬ In a p := by
  intro hi
  have hb := ((realBound_iff lc p.val.lower a).mpr ((inRealInterval_iff p a).mp hi).2.1)
  exact realBound_not_opposite (realBound_le hb) h

theorem notInRealIntervalUpper {M : Semantics.{u}} [SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) (a : Obj (M := M) γ)
    (h : Lt p.val.upper a) : ¬ In a p := by
  intro hi
  have hb := ((realBound_iff rc a p.val.upper).mpr ((inRealInterval_iff p a).mp hi).2.2)
  exact realBound_not_opposite (realBound_le hb) h

theorem notInRealIntervalOpenLower {M : Semantics.{u}} [SetSemantics M]
    {rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) false rc α β)) (a : Obj (M := M) γ)
    (h : Same a p.val.lower) : ¬ In a p :=
  fun hi => ltNotSame p.val.lower a ((inRealInterval_iff p a).mp hi).2.1 h.symm

theorem notInRealIntervalOpenUpper {M : Semantics.{u}} [SetSemantics M]
    {lc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc false α β)) (a : Obj (M := M) γ)
    (h : Same a p.val.upper) : ¬ In a p :=
  fun hi => ltNotSame a p.val.upper ((inRealInterval_iff p a).mp hi).2.2 h

structure RealRayObj {M : Semantics.{u}} (lower closed : Bool)
    (α : Type v) [Representation M α] where
  endpoint : Obj (M := M) α

instance realRayRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    (lower closed : Bool) {α : Type v} [Representation M α] :
    Representation M (RealRayObj (M := M) lower closed α) where
  wd p := In p.endpoint R
  denote p := S.sepValue (M.standard .real) (fun a =>
    if lower then realBound closed (denote p.endpoint) a else realBound closed a (denote p.endpoint))
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .real)

def realRay {M : Semantics.{u}} [SetSemantics M] (lower closed : Bool)
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (RealRayObj (M := M) lower closed α) := ⟨⟨a⟩,ha⟩

theorem inRealRay_iff {M : Semantics.{u}} [S : SetSemantics M]
    {lower closed : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealRayObj (M := M) lower closed α)) (a : Obj (M := M) β) :
    In a p ↔ In a R ∧ (if lower then
      (if closed then Le p.val.endpoint a else Lt p.val.endpoint a)
      else (if closed then Le a p.val.endpoint else Lt a p.val.endpoint)) := by
  change M.mem (denote a) (S.sepValue _ _) ↔ _
  rw [S.sep_members]
  cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte, realBound_iff] <;> rfl

theorem realRaySubsetR {M : Semantics.{u}} [S : SetSemantics M]
    {lower closed : Bool} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealRayObj (M := M) lower closed α)) : Subset p R :=
  fun _ h => (S.sep_members _ _ _).mp h |>.1

theorem notInRealRayOpposite {M : Semantics.{u}} [S : SetSemantics M]
    {lower closed : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealRayObj (M := M) lower closed α)) (a : Obj (M := M) β)
    (h : if lower then (if closed then Lt a p.val.endpoint else Le a p.val.endpoint)
      else (if closed then Lt p.val.endpoint a else Le p.val.endpoint a)) : ¬ In a p := by
  intro hi
  have hb := ((S.sep_members _ _ _).mp hi).2
  cases lower <;> cases closed <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hb h <;>
    exact realBound_not_opposite hb h

theorem notInRealRayEndpoint {M : Semantics.{u}} [SetSemantics M]
    {lower : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealRayObj (M := M) lower false α)) (a : Obj (M := M) β)
    (h : Same a p.val.endpoint) : ¬ In a p := by
  intro hi
  have hb := ((inRealRay_iff p a).mp hi).2
  cases lower
  · exact ltNotSame a p.val.endpoint hb h
  · exact ltNotSame p.val.endpoint a hb h.symm

/-- Sequence indices are positive naturals, as in the source seq(S) contract. -/
structure SeqSetObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  carrier : Obj (M := M) α

def seqSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) : FunctionSignature M :=
  FunctionSignature.withGuard (denote (NPos (M := M))) (denote A)
    (isSet NPos) (isSet A) (fun _ => True)

instance seqSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (SeqSetObj (M := M) α) where
  wd p := IsSet p.carrier
  denote p := F.fnSetValue (seqSignature p.carrier).domain (denote p.carrier)
  wd_isSet {p} h := F.fnSet_isSet _ _ (seqSignature p.carrier).domain_isSet h

def seqSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (hA : IsSet A) :
    Obj (M := M) (SeqSetObj (M := M) α) := ⟨⟨A⟩,hA⟩

theorem seqSet_eq_fnSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (s : Obj (M := M) (SeqSetObj (M := M) α)) :
    Same s (fnSet (seqSignature s.val.carrier)) := rfl

end Litex

namespace Litex

/-- A total denotation on semantic values; the constructor owns its domain WD. -/
noncomputable def realUnaryValue {M : Semantics.{u}} (f : ℝ → ℝ) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, x = M.number (r : ℂ) then
    M.number ((f (Classical.choose h) : ℝ) : ℂ) else M.number 0

theorem realUnaryValue_number {M : Semantics.{u}} (f : ℝ → ℝ) (r : ℝ) :
    realUnaryValue f (M.number (r : ℂ)) = M.number ((f r : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold realUnaryValue
  rw [dif_pos h, hr]

structure ExpObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance expRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ExpObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.exp (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.exp r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def exp {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) : Obj (M := M) (ExpObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteExp {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.exp r : ℝ) : ℂ) := by
  change realUnaryValue Real.exp (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

/-- The exponential of a real is nonzero. -/
theorem expNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr : denote p.val.arg = M.number ((r : ℝ) : ℂ) := NativeBridge.asReal_spec p.val.arg p.wd
  have hx : ((Real.exp r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.exp_pos r))
  have hp : denote p = M.number ((Real.exp r : ℝ) : ℂ) := denoteExp p r hr
  intro h
  exact hx (M.number_injective (hp.symm.trans h))

theorem expInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.exp (NativeBridge.asReal p.val.arg p.wd),
    denoteExp p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

theorem expInRPos {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) : In p RPos :=
  inRPos_intro p (expInR p) (NativeBridge.ltOfDenoteReal (number 0) p 0 _ rfl
    (denoteExp p _ (NativeBridge.asReal_spec p.val.arg p.wd)) (Real.exp_pos _))

structure LnObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance lnRepresentation {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] : Representation M (LnObj (M := M) α) where
  wd a := In a.arg RPos
  denote a := realUnaryValue Real.log (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp (inRPos_real a.arg h)
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.log r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def ln {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a RPos) : Obj (M := M) (LnObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteLn {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.log r : ℝ) : ℂ) := by
  change realUnaryValue Real.log (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem lnInR {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.log (NativeBridge.asReal p.val.arg (inRPos_real _ p.wd)),
    denoteLn p _ (NativeBridge.asReal_spec p.val.arg (inRPos_real _ p.wd))⟩

/-- The exponential preserves and reflects the order of real arguments. -/
theorem expLtIff {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ExpObj (M := M) α)) (q : Obj (M := M) (ExpObj (M := M) β)) :
    Lt p q ↔ Lt p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg p.wd
  let y := NativeBridge.asReal q.val.arg q.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  have hy := NativeBridge.asReal_spec q.val.arg q.wd
  exact (NativeBridge.lt_iff_ofDenoteReal p q (Real.exp x) (Real.exp y) (denoteExp p x hx) (denoteExp q y hy)).trans
    (Real.exp_lt_exp.trans (NativeBridge.lt_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

theorem expLeIff {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ExpObj (M := M) α)) (q : Obj (M := M) (ExpObj (M := M) β)) :
    Le p q ↔ Le p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg p.wd
  let y := NativeBridge.asReal q.val.arg q.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  have hy := NativeBridge.asReal_spec q.val.arg q.wd
  exact (NativeBridge.le_iff_ofDenoteReal p q (Real.exp x) (Real.exp y) (denoteExp p x hx) (denoteExp q y hy)).trans
    (Real.exp_le_exp.trans (NativeBridge.le_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

/-- The logarithm preserves and reflects order on positive real arguments. -/
theorem lnLtIff {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LnObj (M := M) α)) (q : Obj (M := M) (LnObj (M := M) β)) :
    Lt p q ↔ Lt p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg (inRPos_real _ p.wd)
  let y := NativeBridge.asReal q.val.arg (inRPos_real _ q.wd)
  have hx := NativeBridge.asReal_spec p.val.arg (inRPos_real _ p.wd)
  have hy := NativeBridge.asReal_spec q.val.arg (inRPos_real _ q.wd)
  have hx0 : 0 < x := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 x rfl hx).mp (inRPos_positive _ p.wd)
  have hy0 : 0 < y := (NativeBridge.lt_iff_ofDenoteReal (number 0) q.val.arg 0 y rfl hy).mp (inRPos_positive _ q.wd)
  exact (NativeBridge.lt_iff_ofDenoteReal p q (Real.log x) (Real.log y) (denoteLn p x hx) (denoteLn q y hy)).trans
    ((Real.log_lt_log_iff hx0 hy0).trans (NativeBridge.lt_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

theorem lnLeIff {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LnObj (M := M) α)) (q : Obj (M := M) (LnObj (M := M) β)) :
    Le p q ↔ Le p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg (inRPos_real _ p.wd)
  let y := NativeBridge.asReal q.val.arg (inRPos_real _ q.wd)
  have hx := NativeBridge.asReal_spec p.val.arg (inRPos_real _ p.wd)
  have hy := NativeBridge.asReal_spec q.val.arg (inRPos_real _ q.wd)
  have hx0 : 0 < x := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 x rfl hx).mp (inRPos_positive _ p.wd)
  have hy0 : 0 < y := (NativeBridge.lt_iff_ofDenoteReal (number 0) q.val.arg 0 y rfl hy).mp (inRPos_positive _ q.wd)
  exact (NativeBridge.le_iff_ofDenoteReal p q (Real.log x) (Real.log y) (denoteLn p x hx) (denoteLn q y hy)).trans
    ((Real.log_le_log_iff hx0 hy0).trans (NativeBridge.le_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

structure LogObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  base : Obj (M := M) α
  arg : Obj (M := M) β

theorem logBaseNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (r : ℝ) (hr : denote a = M.number (r : ℂ))
    (h0 : Lt (number 0) a) (h1 : ¬ Same a (number 1)) : (Real.log r : ℂ) ≠ 0 := by
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp h0
  have hr1 : r ≠ 1 := by
    intro heq
    apply h1
    change denote a = M.number 1
    simpa only [heq, Complex.ofReal_one] using hr
  exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hr0 hr1

noncomputable instance logRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (LogObj (M := M) α β) where
  wd p := In p.base R ∧ In p.arg R ∧ Lt (number 0) p.base ∧
    Lt (number 0) p.arg ∧ ¬ Same p.base (number 1)
  denote p := M.divValue (realUnaryValue Real.log (denote p.arg)) (realUnaryValue Real.log (denote p.base))
  wd_isSet {p} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    obtain ⟨s, hs⟩ := (M.real_members _).mp h.2.1
    have hn := logBaseNonzero p.base r hr h.2.2.1 h.2.2.2.2
    rw [hr, hs, realUnaryValue_number, realUnaryValue_number, M.div_numbers _ _ hn]
    exact M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def log {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) (ha0 : Lt (number 0) a) (hb0 : Lt (number 0) b)
    (ha1 : ¬ Same a (number 1)) : Obj (M := M) (LogObj (M := M) α β) := ⟨⟨a,b⟩,ha,hb,ha0,hb0,ha1⟩

theorem denoteLog {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LogObj (M := M) α β))
    (r s : ℝ) (hr : denote p.val.base = M.number (r : ℂ))
    (hs : denote p.val.arg = M.number (s : ℂ)) :
    denote p = M.number (((Real.log s / Real.log r) : ℝ) : ℂ) := by
  change M.divValue (realUnaryValue Real.log (denote p.val.arg)) (realUnaryValue Real.log (denote p.val.base)) = _
  have hn := logBaseNonzero p.val.base r hr p.wd.2.2.1 p.wd.2.2.2.2
  rw [hr, hs, realUnaryValue_number, realUnaryValue_number, M.div_numbers _ _ hn, Complex.ofReal_div]

theorem logNonzeroOfGuards {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LogObj (M := M) α β))
    (hb0 : Lt (number 0) p.val.base) (hb1 : ¬ Same p.val.base (number 1))
    (ha0 : Lt (number 0) p.val.arg) (ha1 : ¬ Same p.val.arg (number 1)) : ¬ Same p (number 0) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s,hs⟩ := (M.real_members _).mp p.wd.2.1
  have hbr : Real.log r ≠ 0 := by
    have h := logBaseNonzero p.val.base r hr hb0 hb1
    exact_mod_cast h
  have har : Real.log s ≠ 0 := by
    have h := logBaseNonzero p.val.arg s hs ha0 ha1
    exact_mod_cast h
  apply NativeBridge.notSameOfNativeNonzero p (((Real.log s / Real.log r : ℝ) : ℂ)) (denoteLog p r s hr hs)
  exact_mod_cast (div_ne_zero har hbr)

theorem powerNonunitOfGuards {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hb0 : Lt (number 0) p.val.base) (hb1 : ¬ Same p.val.base (number 1))
    (heZ : In p.val.exponent Z) (he0 : ¬ Same p.val.exponent (number 0)) :
    ¬ Same p (number 1) := by
  obtain ⟨r0,r,hr0,hr,hlt⟩ := hb0
  have hzero : r0 = 0 := Complex.ofReal_injective (M.number_injective hr0.symm)
  have hrpos : 0 < r := hzero ▸ hlt
  have hr1 : r ≠ 1 := by
    intro h
    apply hb1
    change denote p.val.base = M.number 1
    simpa only [h, Complex.ofReal_one] using hr
  obtain ⟨n, hn⟩ := (M.integer_members _).mp heZ
  have hn0 : n ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote p.val.exponent (n : ℂ) hn he0
    exact_mod_cast h
  have hbase0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
  have hp : denote p = M.number ((r : ℂ) ^ n) := by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [hr, hn, M.pow_numbers_int _ _ hbase0]
  intro he
  change denote p = M.number 1 at he
  have hpower : r ^ n = 1 := by
    have h := M.number_injective (hp.symm.trans he)
    exact_mod_cast h
  exact hn0 ((zpow_eq_one_iff_right₀ (le_of_lt hrpos) hr1).mp hpower)

theorem logInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LogObj (M := M) α β)) : In p R :=
  (M.real_members _).mpr ⟨_, denoteLog p _ _ (NativeBridge.asReal_spec p.val.base p.wd.1)
    (NativeBridge.asReal_spec p.val.arg p.wd.2.1)⟩

theorem lnExp {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) (ExpObj (M := M) α))) :
    Same p p.val.arg.val.arg := by
  let r := NativeBridge.asReal p.val.arg.val.arg p.val.arg.wd
  have hr := NativeBridge.asReal_spec p.val.arg.val.arg p.val.arg.wd
  change denote p = _
  rw [denoteLn p (Real.exp r) (denoteExp p.val.arg r hr), Real.log_exp]
  exact hr.symm

theorem expLn {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) (LnObj (M := M) α)))
    (h : Lt (number 0) p.val.arg.val.arg) : Same p p.val.arg.val.arg := by
  let r := NativeBridge.asReal p.val.arg.val.arg (inRPos_real _ p.val.arg.wd)
  have hr := NativeBridge.asReal_spec p.val.arg.val.arg (inRPos_real _ p.val.arg.wd)
  have h0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg.val.arg 0 r rfl hr).mp h
  change denote p = _
  rw [denoteExp p (Real.log r) (denoteLn p.val.arg r hr), Real.exp_log h0]
  exact hr.symm

end Litex

namespace Litex
theorem rationalLogValue (b x : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hb : 0 < b) (hb1 : b ≠ 1) (hpower : x ^ q = b ^ p) :
    Real.log x / Real.log b = (p : ℝ) / (q : ℝ) := by
  have hn := Real.log_ne_zero_of_pos_of_ne_one hb hb1
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hq)
  have h := congrArg Real.log hpower
  rw [Real.log_pow, Real.log_zpow] at h
  field_simp
  nlinarith
theorem logGuardAbove {M : Semantics} {α : Type*} [Representation M α]
    (a : Obj (M := M) α) (h : Lt (number 1) a) :
    Lt (number 0) a ∧ ¬ Same a (number 1) := by
  refine ⟨ltTrans (number 0) (number 1) a ?_ h, ?_⟩
  · exact NativeBridge.ltOfDenoteReal (number 0) (number 1) 0 1 rfl rfl (by norm_num)
  · exact fun heq => ltNotSame (number 1) a h heq.symm

theorem logOne {M : Semantics} {α β : Type*} [Representation M α] [Representation M β]
    (p : Obj (M := M) (LogObj (M := M) α β)) (harg : Same p.val.arg (number 1))
    (hpos : Lt (number 0) p.val.base) (hne : ¬ Same p.val.base (number 1)) :
    Same p (number 0) := by
  let r := NativeBridge.asReal p.val.base p.wd.1
  have hr := NativeBridge.asReal_spec p.val.base p.wd.1
  have hn : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp (logBaseNonzero p.val.base r hr hpos hne)
  have hs : denote p.val.arg = M.number ((1 : ℝ) : ℂ) := by
    change denote p.val.arg = M.number 1 at harg
    simpa only [Complex.ofReal_one] using harg
  change denote p = M.number 0
  rw [denoteLog p r 1 hr hs]
  have hv : Real.log 1 / Real.log r = 0 := (div_eq_iff hn).mpr (by simp only [Real.log_one, zero_mul])
  rw [hv, Complex.ofReal_zero]

theorem logSelf {M : Semantics} {α β : Type*} [Representation M α] [Representation M β]
    (p : Obj (M := M) (LogObj (M := M) α β)) (harg : Same p.val.arg p.val.base)
    (hpos : Lt (number 0) p.val.base) (hne : ¬ Same p.val.base (number 1)) :
    Same p (number 1) := by
  let r := NativeBridge.asReal p.val.base p.wd.1
  have hr := NativeBridge.asReal_spec p.val.base p.wd.1
  have hn : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp (logBaseNonzero p.val.base r hr hpos hne)
  change denote p = M.number 1
  rw [denoteLog p r r hr (harg.trans hr), div_self hn, Complex.ofReal_one]

theorem lnEuler {M : Semantics} [SetSemantics M] {α : Type*} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) α))
    (h : denote p.val.arg = M.number ((Real.exp 1 : ℝ) : ℂ)) : Same p (number 1) := by
  change denote p = M.number 1
  rw [denoteLn p (Real.exp 1) h, Real.log_exp, Complex.ofReal_one]

theorem eulerNonunit {M : Semantics.{u}} :
    ¬ Same (number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (number 1) := by
  intro h
  change M.number ((Real.exp 1 : ℝ) : ℂ) = M.number 1 at h
  have hr : Real.exp (1 : ℝ) = 1 := by
    have hc := M.number_injective h
    exact_mod_cast hc
  have hp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  exact (ne_of_gt hp) hr
end Litex

namespace Litex

structure SinObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sinRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SinObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.sin (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sin r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (SinObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteSin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.sin r : ℝ) : ℂ) := by
  change realUnaryValue Real.sin (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem sinInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.sin (NativeBridge.asReal p.val.arg p.wd),
    denoteSin p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CosObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cosRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CosObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.cos (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.cos r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def cos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (CosObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteCos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CosObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.cos r : ℝ) : ℂ) := by
  change realUnaryValue Real.cos (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cosInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CosObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.cos (NativeBridge.asReal p.val.arg p.wd),
    denoteCos p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure TanObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance tanRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (TanObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.cos (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue Real.tan (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.tan r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def tan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (cos a ha) (number 0)) :
    Obj (M := M) (TanObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteTan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.tan r : ℝ) : ℂ) := by
  change realUnaryValue Real.tan (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem tanInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.tan (NativeBridge.asReal p.val.arg p.wd.1),
    denoteTan p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

theorem sinSqAddCosSq (x : ℝ) :
    (Real.sin x : ℂ)^2 + (Real.cos x : ℂ)^2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq x

theorem tanQuotient (x : ℝ) :
    (Real.tan x : ℂ) = (Real.sin x : ℂ) / (Real.cos x : ℂ) := by
  rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
end Litex

namespace Litex
theorem tanPiDivSix : Real.tan (Real.pi / 6) = Real.sqrt 3 / 3 := by
  rw [Real.tan_pi_div_six]
  apply (div_eq_div_iff (by positivity) (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
end Litex

namespace Litex
noncomputable def complexUnaryValue {M : Semantics.{u}} (f : ℂ → ℂ) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ z : ℂ, x = M.number z then
    M.number (f (Classical.choose h)) else M.number 0

theorem complexUnaryValue_number {M : Semantics.{u}} (f : ℂ → ℂ) (z : ℂ) :
    complexUnaryValue f (M.number z) = M.number (f z) := by
  classical
  have h : ∃ w : ℂ, M.number z = M.number w := ⟨z, rfl⟩
  have hz : Classical.choose h = z := (M.number_injective (Classical.choose_spec h)).symm
  unfold complexUnaryValue
  rw [dif_pos h, hz]

structure ConjugateObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance conjRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ConjugateObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => star z) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨star z, by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def conj {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (ConjugateObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteConjugate {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ConjugateObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number (star z) := by
  change complexUnaryValue (fun z : ℂ => star z) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem conjInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ConjugateObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨star z, denoteConjugate p z hz⟩

structure RealPartObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance reRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (RealPartObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => (z.re : ℂ)) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨(z.re : ℂ), by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def re {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (RealPartObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteRealPart {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealPartObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number ((z.re : ℂ)) := by
  change complexUnaryValue (fun z : ℂ => (z.re : ℂ)) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem reInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealPartObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨(z.re : ℂ), denoteRealPart p z hz⟩

theorem reInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealPartObj (M := M) α)) : In p R := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.real_members _).mpr ⟨z.re, denoteRealPart p z hz⟩

structure ImaginaryPartObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance imgRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ImaginaryPartObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => (z.im : ℂ)) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨(z.im : ℂ), by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def img {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (ImaginaryPartObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteImaginaryPart {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ImaginaryPartObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number ((z.im : ℂ)) := by
  change complexUnaryValue (fun z : ℂ => (z.im : ℂ)) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem imgInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ImaginaryPartObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨(z.im : ℂ), denoteImaginaryPart p z hz⟩

theorem imgInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ImaginaryPartObj (M := M) α)) : In p R := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.real_members _).mpr ⟨z.im, denoteImaginaryPart p z hz⟩

structure ComplexAbsObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance complexAbsRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ComplexAbsObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨(‖z‖ : ℂ), by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def complexAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (ComplexAbsObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteComplexAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number ((‖z‖ : ℂ)) := by
  change complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem complexAbsEqSqrtOfNormSq {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α))
    (q : Obj (M := M) (SqrtObj (M := M) β)) (z : ℂ) (r : ℝ)
    (hz : denote p.val.arg = M.number z)
    (hr : denote q.val.arg = M.number (r : ℂ))
    (hnorm : Complex.normSq z = r) : Same p q := by
  have hp := denoteComplexAbs p z hz
  have hq := NativeBridge.denoteSqrt q.val.arg q.wd.1 q.wd.2 r hr
  change denote p = denote q
  rw [Complex.norm_def, hnorm] at hp
  exact hp.trans hq.symm

theorem complexAbsInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨(‖z‖ : ℂ), denoteComplexAbs p z hz⟩

theorem complexAbsInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α)) : In p R := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.real_members _).mpr ⟨‖z‖, denoteComplexAbs p z hz⟩

theorem conjugateNonzeroOfArg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ConjugateObj (M := M) α))
    (ha : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  have hz0 := NativeBridge.nativeNonzeroOfDenote p.val.arg z hz ha
  apply NativeBridge.notSameOfNativeNonzero p (star z) (denoteConjugate p z hz)
  simpa using hz0

theorem complexAbsNonzeroOfArg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α))
    (ha : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  have hz0 := NativeBridge.nativeNonzeroOfDenote p.val.arg z hz ha
  apply NativeBridge.notSameOfNativeNonzero p ((‖z‖ : ℝ) : ℂ) (denoteComplexAbs p z hz)
  exact_mod_cast (norm_ne_zero_iff.mpr hz0)

theorem complexReconstruction (z : ℂ) : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z :=
  Complex.re_add_im z
end Litex

namespace Litex

noncomputable def nativeCot (x : ℝ) : ℝ := Real.cos x / Real.sin x
noncomputable def nativeSec (x : ℝ) : ℝ := 1 / Real.cos x
noncomputable def nativeCsc (x : ℝ) : ℝ := 1 / Real.sin x
-- Litex uses the principal cotangent inverse in (0, pi).
noncomputable def nativeArccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

theorem nativeCot_arccot (x : ℝ) : nativeCot (nativeArccot x) = x := by
  rw [nativeCot, nativeArccot, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos, Real.tan_arctan]

theorem nativeArccot_pos (x : ℝ) : 0 < nativeArccot x :=
  sub_pos.mpr (Real.arctan_lt_pi_div_two x)

theorem nativeArccot_lt_pi (x : ℝ) : nativeArccot x < Real.pi := by
  unfold nativeArccot
  linarith [Real.neg_pi_div_two_lt_arctan x]

theorem sin_nativeArccot_pos (x : ℝ) : 0 < Real.sin (nativeArccot x) := by
  rw [nativeArccot, Real.sin_pi_div_two_sub]
  exact Real.cos_arctan_pos x


structure ArctanObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arctanRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArctanObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.arctan (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.arctan r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arctan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (ArctanObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteArctan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.arctan r : ℝ) : ℂ) := by
  change realUnaryValue Real.arctan (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arctanInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.arctan (NativeBridge.asReal p.val.arg p.wd),
    denoteArctan p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩


structure ArccotObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arccotRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArccotObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue nativeArccot (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeArccot r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arccot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (ArccotObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteArccot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeArccot r : ℝ) : ℂ) := by
  change realUnaryValue nativeArccot (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arccotInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeArccot (NativeBridge.asReal p.val.arg p.wd),
    denoteArccot p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩


structure ArcsinObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arcsinRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArcsinObj (M := M) α) where
  wd a := In a.arg R ∧ Le (number (-1)) a.arg ∧ Le a.arg (number 1)
  denote a := realUnaryValue Real.arcsin (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.arcsin r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arcsin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hlo : Le (number (-1)) a) (hhi : Le a (number 1)) :
    Obj (M := M) (ArcsinObj (M := M) α) := ⟨⟨a⟩,⟨ha,hlo,hhi⟩⟩

theorem denoteArcsin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.arcsin r : ℝ) : ℂ) := by
  change realUnaryValue Real.arcsin (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arcsinInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.arcsin (NativeBridge.asReal p.val.arg p.wd.1),
    denoteArcsin p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


structure ArccosObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arccosRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArccosObj (M := M) α) where
  wd a := In a.arg R ∧ Le (number (-1)) a.arg ∧ Le a.arg (number 1)
  denote a := realUnaryValue Real.arccos (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.arccos r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arccos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hlo : Le (number (-1)) a) (hhi : Le a (number 1)) :
    Obj (M := M) (ArccosObj (M := M) α) := ⟨⟨a⟩,⟨ha,hlo,hhi⟩⟩

theorem denoteArccos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccosObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.arccos r : ℝ) : ℂ) := by
  change realUnaryValue Real.arccos (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arccosInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccosObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.arccos (NativeBridge.asReal p.val.arg p.wd.1),
    denoteArccos p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


structure CotObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cotRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CotObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.sin (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue nativeCot (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCot r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def cot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (sin a ha) (number 0)) :
    Obj (M := M) (CotObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteCot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CotObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCot r : ℝ) : ℂ) := by
  change realUnaryValue nativeCot (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cotInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CotObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCot (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCot p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

theorem sinNonzeroOfNegatedArg {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SinObj (M := M) α)) (q : Obj (M := M) (SinObj (M := M) β))
    (harg : denote p.val.arg = M.negValue (denote q.val.arg))
    (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal q.val.arg q.wd
  have hr := NativeBridge.asReal_spec q.val.arg q.wd
  have hp : denote p.val.arg = M.number ((-r : ℝ) : ℂ) := by
    rw [harg, hr, M.neg_numbers, Complex.ofReal_neg]
  have hs : Real.sin r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.sin r : ℝ) : ℂ) (denoteSin q r hr) hn
    exact_mod_cast h
  apply NativeBridge.notSameOfNativeNonzero p ((Real.sin (-r) : ℝ) : ℂ) (denoteSin p (-r) hp)
  exact_mod_cast (show Real.sin (-r) ≠ 0 from by simpa using hs)

theorem cosNonzeroOfNegatedArg {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (CosObj (M := M) α)) (q : Obj (M := M) (CosObj (M := M) β))
    (harg : denote p.val.arg = M.negValue (denote q.val.arg))
    (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal q.val.arg q.wd
  have hr := NativeBridge.asReal_spec q.val.arg q.wd
  have hp : denote p.val.arg = M.number ((-r : ℝ) : ℂ) := by
    rw [harg, hr, M.neg_numbers, Complex.ofReal_neg]
  have hc : Real.cos r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.cos r : ℝ) : ℂ) (denoteCos q r hr) hn
    exact_mod_cast h
  apply NativeBridge.notSameOfNativeNonzero p ((Real.cos (-r) : ℝ) : ℂ) (denoteCos p (-r) hp)
  exact_mod_cast (show Real.cos (-r) ≠ 0 from by simpa using hc)

theorem tanNonzeroOfSin {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (TanObj (M := M) α)) (q : Obj (M := M) (SinObj (M := M) β))
    (harg : Same p.val.arg q.val.arg) (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hq : denote q.val.arg = M.number (r : ℂ) := harg.symm.trans hr
  have hs : Real.sin r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.sin r : ℝ) : ℂ) (denoteSin q r hq) hn
    exact_mod_cast h
  have hc : Real.cos r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  have ht : Real.tan r ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hs hc
  apply NativeBridge.notSameOfNativeNonzero p ((Real.tan r : ℝ) : ℂ) (denoteTan p r hr)
  exact_mod_cast ht

theorem cotNonzeroOfCos {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (CotObj (M := M) α)) (q : Obj (M := M) (CosObj (M := M) β))
    (harg : Same p.val.arg q.val.arg) (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hq : denote q.val.arg = M.number (r : ℂ) := harg.symm.trans hr
  have hc : Real.cos r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.cos r : ℝ) : ℂ) (denoteCos q r hq) hn
    exact_mod_cast h
  have hs : Real.sin r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  have ht : nativeCot r ≠ 0 := by
    unfold nativeCot
    exact div_ne_zero hc hs
  apply NativeBridge.notSameOfNativeNonzero p ((nativeCot r : ℝ) : ℂ) (denoteCot p r hr)
  exact_mod_cast ht


structure SecObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance secRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SecObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.cos (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue nativeSec (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeSec r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sec {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (cos a ha) (number 0)) :
    Obj (M := M) (SecObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteSec {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeSec r : ℝ) : ℂ) := by
  change realUnaryValue nativeSec (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem secInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeSec (NativeBridge.asReal p.val.arg p.wd.1),
    denoteSec p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


structure CscObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cscRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CscObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.sin (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue nativeCsc (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCsc r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def csc {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (sin a ha) (number 0)) :
    Obj (M := M) (CscObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteCsc {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCsc r : ℝ) : ℂ) := by
  change realUnaryValue nativeCsc (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cscInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCsc (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCsc p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


theorem cosArctanNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) :
    ¬ Same (cos p (arctanInR p)) (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue Real.cos (denote p) ≠ M.number 0
  rw [denoteArctan p r hr, realUnaryValue_number]
  intro h
  have hz : Real.cos (Real.arctan r) = 0 :=
    Complex.ofReal_injective (M.number_injective h)
  exact (Real.cos_arctan_pos r).ne' hz


theorem sinArccotNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) :
    ¬ Same (sin p (arccotInR p)) (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue Real.sin (denote p) ≠ M.number 0
  rw [denoteArccot p r hr, realUnaryValue_number]
  intro h
  have hz : Real.sin (nativeArccot r) = 0 :=
    Complex.ofReal_injective (M.number_injective h)
  exact (sin_nativeArccot_pos r).ne' hz


theorem sinArcsin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) :
    Same (sin p (arcsinInR p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hlo : -1 ≤ r := (NativeBridge.le_iff_ofDenoteReal
    (number (-1)) p.val.arg (-1) r (by
      change M.number (-1) = M.number ((-1 : ℝ) : ℂ)
      rw [Complex.ofReal_neg, Complex.ofReal_one]) hr).mp p.wd.2.1
  have hhi : r ≤ 1 := (NativeBridge.le_iff_ofDenoteReal
    p.val.arg (number 1) r 1 hr rfl).mp p.wd.2.2
  change realUnaryValue Real.sin (denote p) = denote p.val.arg
  rw [denoteArcsin p r hr, realUnaryValue_number, Real.sin_arcsin hlo hhi, hr]


theorem cosArccos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccosObj (M := M) α)) :
    Same (cos p (arccosInR p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hlo : -1 ≤ r := (NativeBridge.le_iff_ofDenoteReal
    (number (-1)) p.val.arg (-1) r (by
      change M.number (-1) = M.number ((-1 : ℝ) : ℂ)
      rw [Complex.ofReal_neg, Complex.ofReal_one]) hr).mp p.wd.2.1
  have hhi : r ≤ 1 := (NativeBridge.le_iff_ofDenoteReal
    p.val.arg (number 1) r 1 hr rfl).mp p.wd.2.2
  change realUnaryValue Real.cos (denote p) = denote p.val.arg
  rw [denoteArccos p r hr, realUnaryValue_number, Real.cos_arccos hlo hhi, hr]


theorem tanArctan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) :
    Same (tan p (arctanInR p) (cosArctanNonzero p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue Real.tan (denote p) = denote p.val.arg
  rw [denoteArctan p r hr, realUnaryValue_number, Real.tan_arctan r, hr]


theorem cotArccot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) :
    Same (cot p (arccotInR p) (sinArccotNonzero p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue nativeCot (denote p) = denote p.val.arg
  rw [denoteArccot p r hr, realUnaryValue_number, nativeCot_arccot r, hr]

end Litex

namespace Litex

theorem secNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hd : Real.cos r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  change denote p ≠ M.number 0
  rw [denoteSec p r hr]
  intro h
  have hz : 1 / Real.cos r = 0 := Complex.ofReal_injective (M.number_injective h)
  exact (one_div_ne_zero hd) hz

theorem secInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) : In p RStar :=
  inRStar_intro p (secInR p) (secNonzero p)

theorem cscNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hd : Real.sin r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  change denote p ≠ M.number 0
  rw [denoteCsc p r hr]
  intro h
  have hz : 1 / Real.sin r = 0 := Complex.ofReal_injective (M.number_injective h)
  exact (one_div_ne_zero hd) hz

theorem cscInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) : In p RStar :=
  inRStar_intro p (cscInR p) (cscNonzero p)
end Litex


namespace Litex

/-- Source proper inclusion uses semantic inequality, not host inequality. -/
def Superset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop := Subset B A

def ProperSubset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop := Subset A B ∧ ¬ Same A B

def ProperSuperset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop := Subset B A ∧ ¬ Same A B

/-- Numeric predicate meanings depend only on semantic denotation. -/
def PrimeValue (M : Semantics.{u}) (a : M.Value) : Prop :=
  ∃ n : ℕ, a = M.number (n : ℂ) ∧ Nat.Prime n

def CoprimeValue (M : Semantics.{u}) (a b : M.Value) : Prop :=
  ∃ m n : ℕ, a = M.number (m : ℂ) ∧ b = M.number (n : ℂ) ∧ Nat.Coprime m n

/-- Litex puts the dividend first and requires a nonzero integer divisor. -/
def DvdValue (M : Semantics.{u}) (a b : M.Value) : Prop :=
  ∃ m n : ℤ, a = M.number (m : ℂ) ∧ b = M.number (n : ℂ) ∧ n ≠ 0 ∧ n ∣ m

def Prime {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : Prop := PrimeValue M (denote a)

def Coprime {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop := CoprimeValue M (denote a) (denote b)

def Dvd {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop := DvdValue M (denote a) (denote b)

theorem prime_iff_of_denote {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (n : ℕ) (ha : denote a = M.number (n : ℂ)) :
    Prime a ↔ Nat.Prime n := by
  constructor
  · rintro ⟨m, hm, hp⟩
    have h : m = n := by exact_mod_cast M.number_injective (hm.symm.trans ha)
    exact h ▸ hp
  · intro hp
    exact ⟨n, ha, hp⟩

theorem coprime_iff_of_denote {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m n : ℕ)
    (ha : denote a = M.number (m : ℂ)) (hb : denote b = M.number (n : ℂ)) :
    Coprime a b ↔ Nat.Coprime m n := by
  constructor
  · rintro ⟨i, j, hi, hj, h⟩
    have h₁ : i = m := by exact_mod_cast M.number_injective (hi.symm.trans ha)
    have h₂ : j = n := by exact_mod_cast M.number_injective (hj.symm.trans hb)
    exact h₁ ▸ h₂ ▸ h
  · intro h
    exact ⟨m, n, ha, hb, h⟩

theorem dvd_iff_of_denote {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m n : ℤ)
    (ha : denote a = M.number (m : ℂ)) (hb : denote b = M.number (n : ℂ)) :
    Dvd a b ↔ n ≠ 0 ∧ n ∣ m := by
  constructor
  · rintro ⟨i, j, hi, hj, h⟩
    have h₁ : i = m := by exact_mod_cast M.number_injective (hi.symm.trans ha)
    have h₂ : j = n := by exact_mod_cast M.number_injective (hj.symm.trans hb)
    exact h₁ ▸ h₂ ▸ h
  · rintro ⟨hn, h⟩
    exact ⟨m, n, ha, hb, hn, h⟩

theorem emptyNotNonempty {M : Semantics.{u}} [S : SetSemantics M] :
    ¬ IsNonempty (emptySet (M := M)) := by
  rintro ⟨x, hx⟩
  exact S.empty_members x hx

end Litex

namespace Litex

theorem dvdOfModZero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ModObj (M := M) α β)) (h : Same p (number 0)) :
    Dvd p.val.left p.val.right := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  have hb0 : b ≠ 0 := by
    intro hzero
    apply p.wd.2.2
    change denote p.val.right = M.number 0
    simpa only [hzero, Int.cast_zero] using hb
  have hmod : a % b = 0 := by
    have he : ((a % b : ℤ) : ℂ) = 0 := M.number_injective ((modDenoteInt p a b ha hb).symm.trans h)
    exact_mod_cast he
  exact ⟨a, b, ha, hb, hb0, Int.dvd_of_emod_eq_zero hmod⟩

end Litex

namespace Litex

theorem naturalNotFinite {M : Semantics.{u}} : ¬ IsFiniteSet (N (M := M)) := by
  have hi : Function.Injective (fun n : ℕ => M.number (n : ℂ)) := by
    intro a b h
    exact_mod_cast M.number_injective h
  intro h
  apply Set.infinite_range_of_injective hi
  exact h.subset (by
    rintro _ ⟨n, rfl⟩
    exact (M.natural_members _).mpr ⟨n, rfl⟩)

end Litex

namespace Litex

structure SymmetricDifferenceObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

def symmetricDifferenceValue {M : Semantics.{u}} [S : SetSemantics M]
    (A B : M.Value) : M.Value :=
  S.unionValue (S.sepValue A (fun x => ¬ M.mem x B))
    (S.sepValue B (fun x => ¬ M.mem x A))

instance symmetricDifferenceRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (SymmetricDifferenceObj (M := M) α β) where
  wd _ := True
  denote p := symmetricDifferenceValue (denote p.left) (denote p.right)
  wd_isSet {p} _ := S.union_isSet _ _
    (S.sep_isSet _ _ (isSet p.left)) (S.sep_isSet _ _ (isSet p.right))

def symmetricDifference {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (SymmetricDifferenceObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem symmetricDifference_members {M : Semantics.{u}} [S : SetSemantics M]
    (A B x : M.Value) : M.mem x (symmetricDifferenceValue A B) ↔
      (M.mem x A ∧ ¬ M.mem x B) ∨ (¬ M.mem x A ∧ M.mem x B) := by
  simp only [symmetricDifferenceValue, S.union_members, S.sep_members]
  exact or_congr Iff.rfl and_comm

theorem inSymmetricDifferenceLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : In a p.val.left) (hb : ¬ In a p.val.right) : In a p :=
  (symmetricDifference_members _ _ _).mpr (Or.inl ⟨ha, hb⟩)

theorem inSymmetricDifferenceRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : ¬ In a p.val.left) (hb : In a p.val.right) : In a p :=
  (symmetricDifference_members _ _ _).mpr (Or.inr ⟨ha, hb⟩)

theorem notInSymmetricDifferenceBoth {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : In a p.val.left) (hb : In a p.val.right) : ¬ In a p := by
  intro h
  rcases (symmetricDifference_members _ _ _).mp h with h | h
  · exact h.2 hb
  · exact h.1 ha

theorem notInSymmetricDifferenceNeither {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : ¬ In a p.val.left) (hb : ¬ In a p.val.right) : ¬ In a p := by
  intro h
  rcases (symmetricDifference_members _ _ _).mp h with h | h
  · exact ha h.1
  · exact hb h.2

theorem symmetricDifferenceDefinition {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (symmetricDifference A B) (union (setMinus A B) (setMinus B A)) := rfl

theorem symmetricDifferenceSelf {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Same (symmetricDifference A A) emptySet := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (symmetricDifferenceValue (denote A) (denote A)) ↔ M.mem x S.emptyValue
  rw [symmetricDifference_members]
  simp only [and_not_self, not_and_self, or_self, S.empty_members, iff_self]

end Litex

namespace Litex

section IndexedSets
variable {M : Semantics.{u}} [F : FunctionSemantics M]
variable {α : Type v} {β : Type w} {γ : Type x}
variable [Representation M α] [Representation M β] [Representation M γ]

def indexFamilySignature (I : Obj (M := M) α) (X : Obj (M := M) β) :
    FunctionSignature M :=
  FunctionSignature.withGuard (denote I) (denote X) (isSet I) (isSet X) (fun _ => True)

def indexedFamilyWD (I : Obj (M := M) α) (X : Obj (M := M) β)
    (A : Obj (M := M) γ) : Prop :=
  IsNonempty I ∧ IsSet I ∧ IsSet X ∧ In A (fnSet (indexFamilySignature I (powerSet X)))

def indexUnionValue (I X A : M.Value) : M.Value :=
  F.sepValue X (fun a => ∃ i, M.mem i I ∧ M.mem a (F.callValue A i))

def indexIntersectValue (I X A : M.Value) : M.Value :=
  F.sepValue X (fun a => ∀ i, M.mem i I → M.mem a (F.callValue A i))

structure IndexUnionObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  index : Obj (M := M) α
  ambient : Obj (M := M) β
  family : Obj (M := M) γ

instance indexUnionRepresentation : Representation M (IndexUnionObj M α β γ) where
  wd p := indexedFamilyWD p.index p.ambient p.family
  denote p := indexUnionValue (denote p.index) (denote p.ambient) (denote p.family)
  wd_isSet {p} _ := F.sep_isSet _ _ (isSet p.ambient)

def indexUnion (I : Obj (M := M) α) (X : Obj (M := M) β) (A : Obj (M := M) γ)
    (hI : IsNonempty I) (hIs : IsSet I) (hX : IsSet X)
    (hA : In A (fnSet (indexFamilySignature I (powerSet X)))) :
    Obj (M := M) (IndexUnionObj M α β γ) := ⟨⟨I, X, A⟩, hI, hIs, hX, hA⟩

structure IndexIntersectObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  index : Obj (M := M) α
  ambient : Obj (M := M) β
  family : Obj (M := M) γ

instance indexIntersectRepresentation : Representation M (IndexIntersectObj M α β γ) where
  wd p := indexedFamilyWD p.index p.ambient p.family
  denote p := indexIntersectValue (denote p.index) (denote p.ambient) (denote p.family)
  wd_isSet {p} _ := F.sep_isSet _ _ (isSet p.ambient)

def indexIntersect (I : Obj (M := M) α) (X : Obj (M := M) β) (A : Obj (M := M) γ)
    (hI : IsNonempty I) (hIs : IsSet I) (hX : IsSet X)
    (hA : In A (fnSet (indexFamilySignature I (powerSet X)))) :
    Obj (M := M) (IndexIntersectObj M α β γ) := ⟨⟨I, X, A⟩, hI, hIs, hX, hA⟩

theorem indexUnionMember {δ : Type t} {ε : Type*}
    [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (IndexUnionObj M α β γ))
    (i : Obj (M := M) δ) (a : Obj (M := M) ε)
    (hi : In i p.val.index)
    (ha : M.mem (denote a) (F.callValue (denote p.val.family) (denote i))) : In a p := by
  have hdom : M.mem (denote i) (indexFamilySignature p.val.index (powerSet p.val.ambient)).domain :=
    (F.sep_members _ _ _).mpr ⟨hi, True.intro⟩
  have hfiber := F.call_mem _ _ _ _ p.wd.2.2.2 hdom
  have hx : In a p.val.ambient := ((F.power_members _ _).mp hfiber).2 _ ha
  exact (F.sep_members _ _ _).mpr ⟨hx, denote i, hi, ha⟩

theorem indexIntersectMember {δ : Type t} [Representation M δ]
    (p : Obj (M := M) (IndexIntersectObj M α β γ)) (a : Obj (M := M) δ)
    (ha : In a p.val.ambient)
    (hall : ∀ i, M.mem i (denote p.val.index) →
      M.mem (denote a) (F.callValue (denote p.val.family) i)) : In a p :=
  (F.sep_members _ _ _).mpr ⟨ha, hall⟩

def indexCartValue [IU : IndexedUnionSemantics M] (I S g : M.Value) : M.Value :=
  F.sepValue (F.fnSetValue (F.sepValue I (fun _ => True)) (IU.indexedUnionValue S id))
    (fun f => ∀ i, M.mem i I → M.mem (F.callValue f i) (F.callValue g i))

structure IndexCartObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  index : Obj (M := M) α
  familySet : Obj (M := M) β
  family : Obj (M := M) γ

instance indexCartRepresentation [IU : IndexedUnionSemantics M] :
    Representation M (IndexCartObj M α β γ) where
  wd p := IsNonempty p.index ∧ IsSet p.index ∧ IsNonempty p.familySet ∧
    In p.family (fnSet (indexFamilySignature p.index p.familySet))
  denote p := indexCartValue (denote p.index) (denote p.familySet) (denote p.family)
  wd_isSet {p} _ := F.sep_isSet _ _ (F.fnSet_isSet _ _
    (F.sep_isSet _ _ (isSet p.index))
    (IU.indexedUnion_isSet _ _ (isSet p.familySet) (fun _ h => M.member_isSet h)))

def indexCart [IndexedUnionSemantics M]
    (I : Obj (M := M) α) (S : Obj (M := M) β) (g : Obj (M := M) γ)
    (hI : IsNonempty I) (hIs : IsSet I) (hS : IsNonempty S)
    (hg : In g (fnSet (indexFamilySignature I S))) :
    Obj (M := M) (IndexCartObj M α β γ) := ⟨⟨I, S, g⟩, hI, hIs, hS, hg⟩

theorem indexCartMember [IndexedUnionSemantics M]
    {δ : Type t} [Representation M δ]
    (p : Obj (M := M) (IndexCartObj M α β γ)) (f : Obj (M := M) δ)
    (hf : In f (fnSet (indexFamilySignature p.val.index (familyUnion p.val.familySet))))
    (hg : IsChoiceFunctionFor p.val.index p.val.familySet p.val.family f) : In f p :=
  (F.sep_members _ _ _).mpr ⟨hf, hg⟩

end IndexedSets
end Litex

namespace Litex

/-- A source forall ranges over all representations. A one-point carrier can
represent any fixed semantic value, even in a smaller host universe. -/
theorem forallMembersOfRepresentations {M : Semantics.{u}} {α : Type v}
    [Representation M α] {P : M.Value → Prop} (A : Obj (M := M) α)
    (h : ∀ {β : Type w} [Representation M β], (x : Obj (M := M) β) →
      In x A → P (denote x)) : ∀ x, M.mem x (denote A) → P x := by
  intro x hx
  letI : Representation M PUnit.{w+1} := {
    wd := fun _ => True
    denote := fun _ => x
    wd_isSet := fun _ => M.member_isSet hx }
  exact h (⟨PUnit.unit, True.intro⟩ : Obj (M := M) PUnit.{w+1}) hx

structure FamilyIntersectObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  family : Obj (M := M) α

def familyIntersectValue {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] (F : M.Value) : M.Value :=
  S.sepValue (I.indexedUnionValue F id) (fun x => ∀ A, M.mem A F → M.mem x A)

instance familyIntersectRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] {α : Type v} [Representation M α] :
    Representation M (FamilyIntersectObj (M := M) α) where
  wd p := IsNonempty p.family
  denote p := familyIntersectValue (denote p.family)
  wd_isSet {p} _ := S.sep_isSet _ _ (I.indexedUnion_isSet _ _ (isSet p.family)
    (fun _ h => M.member_isSet h))

def familyIntersect {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (F : Obj (M := M) α) (h : IsNonempty F) :
    Obj (M := M) (FamilyIntersectObj (M := M) α) := ⟨⟨F⟩, h⟩

theorem familyIntersect_members {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (FamilyIntersectObj (M := M) α)) (x : M.Value) :
    M.mem x (denote p) ↔ ∀ A, M.mem A (denote p.val.family) → M.mem x A := by
  change M.mem x (S.sepValue _ _) ↔ _
  rw [S.sep_members]
  constructor
  · exact And.right
  · intro h
    obtain ⟨A, hA⟩ := p.wd
    exact ⟨(I.indexedUnion_members _ _ _).mpr ⟨A, hA, h A hA⟩, h⟩

theorem familyIntersectMember {M : Semantics.{u}} [SetSemantics M]
    [IndexedUnionSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FamilyIntersectObj (M := M) α)) (x : Obj (M := M) β)
    (h : ∀ A, M.mem A (denote p.val.family) → M.mem (denote x) A) : In x p :=
  (familyIntersect_members p (denote x)).mpr h

end Litex

-- Ordered and finite folds retain their checked functions and domains.
universe r
namespace Litex
section FoldSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def foldApply2 (operation a b : M.Value) : M.Value :=
  F.callValue operation (FiniteFunction.pack2 a b)

noncomputable def foldValue (items : List M.Value) (f operation seed : M.Value) : M.Value :=
  items.foldl (fun acc i => foldApply2 operation acc (F.callValue f i)) seed

noncomputable def homogeneousFoldSignature (E : M.Value) (hE : M.isSet E) :
    FunctionSignature M :=
  FunctionSignature.withGuard (FiniteFunction.cartValue ![E, E]) E
    (FiniteFunction.cart_isSet _ (by intro i; fin_cases i <;> exact hE)) hE (fun _ => True)

theorem homogeneousFoldSignature_member (E : M.Value) (hE : M.isSet E)
    (a b : M.Value) (ha : M.mem a E) (hb : M.mem b E) :
    M.mem (FiniteFunction.pack2 a b) (homogeneousFoldSignature E hE).domain :=
  (F.sep_members _ _ _).mpr ⟨(FiniteFunction.cart2_members _ _ _).mpr
    ⟨a, ha, b, hb, rfl⟩, True.intro⟩

theorem foldApply2_mem (s : FunctionSignature M) (operation a b : M.Value)
    (hop : M.mem operation (F.fnSetValue (homogeneousFoldSignature s.output s.output_isSet).domain s.output))
    (ha : M.mem a s.output) (hb : M.mem b s.output) :
    M.mem (foldApply2 operation a b) s.output :=
  F.call_mem _ _ _ _ hop (homogeneousFoldSignature_member _ _ _ _ ha hb)

theorem foldValue_mem (s : FunctionSignature M) (items : List M.Value) (f operation seed : M.Value)
    (hf : M.mem f (F.fnSetValue s.domain s.output))
    (hop : M.mem operation (F.fnSetValue (homogeneousFoldSignature s.output s.output_isSet).domain s.output))
    (hseed : M.mem seed s.output)
    (hitems : ∀ i ∈ items, M.mem i s.domain) : M.mem (foldValue items f operation seed) s.output := by
  induction items generalizing seed with
  | nil => exact hseed
  | cons i rest ih =>
    apply ih
    · exact foldApply2_mem s operation seed (F.callValue f i) hop hseed
        (F.call_mem _ _ _ _ hf (hitems i (List.mem_cons_self)))
    · intro j hj
      exact hitems j (List.mem_cons_of_mem i hj)

def integerFoldIndices (first last : ℤ) : List ℤ :=
  (List.range (last - first + 1).toNat).map (fun (n : ℕ) => first + (n : ℤ))

theorem integerFoldIndices_mem (first last k : ℤ) :
    k ∈ integerFoldIndices first last ↔ first ≤ k ∧ k ≤ last := by
  simp only [integerFoldIndices, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    refine ⟨(k - first).toNat, ?_, ?_⟩ <;> omega

noncomputable def rangeFoldValue (first last f operation seed : M.Value) : M.Value :=
  foldValue ((integerFoldIndices (NativeBridge.integerValue first)
    (NativeBridge.integerValue last)).map (fun (k : ℤ) => M.number (k : ℂ))) f operation seed

structure RangeFoldObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    (δ : Type t) (ε : Type r) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] [Representation M ε] where
  first : Obj (M := M) α
  last : Obj (M := M) β
  function : Obj (M := M) γ
  operation : Obj (M := M) δ
  seed : Obj (M := M) ε
  signature : FunctionSignature M

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
variable [Representation M α] [Representation M β] [Representation M γ]
variable [Representation M δ] [Representation M ε]

def rangeFoldWD (p : RangeFoldObj M α β γ δ ε) : Prop :=
  In p.first Z ∧ In p.last Z ∧ In p.function (fnSet p.signature) ∧
  In p.operation (fnSet (homogeneousFoldSignature p.signature.output p.signature.output_isSet)) ∧
  M.mem (denote p.seed) p.signature.output ∧
  ∀ k : ℤ, NativeBridge.integerValue (denote p.first) ≤ k →
    k ≤ NativeBridge.integerValue (denote p.last) → M.mem (M.number (k : ℂ)) p.signature.domain

theorem rangeFoldValue_mem (p : RangeFoldObj M α β γ δ ε) (h : rangeFoldWD p) :
    M.mem (rangeFoldValue (denote p.first) (denote p.last) (denote p.function)
      (denote p.operation) (denote p.seed)) p.signature.output := by
  apply foldValue_mem p.signature _ _ _ _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
  obtain ⟨hl, hr⟩ := (integerFoldIndices_mem _ _ _).mp hk
  exact h.2.2.2.2.2 k hl hr

noncomputable instance rangeFoldRepresentation : Representation M (RangeFoldObj M α β γ δ ε) where
  wd := rangeFoldWD
  denote p := rangeFoldValue (denote p.first) (denote p.last) (denote p.function)
    (denote p.operation) (denote p.seed)
  wd_isSet {p} h := M.member_isSet (rangeFoldValue_mem p h)

noncomputable def rangeFold (first : Obj (M := M) α) (last : Obj (M := M) β)
    (f : Obj (M := M) γ) (operation : Obj (M := M) δ) (seed : Obj (M := M) ε)
    (s : FunctionSignature M) (hfirst : In first Z) (hlast : In last Z)
    (hf : In f (fnSet s)) (hop : In operation (fnSet (homogeneousFoldSignature s.output s.output_isSet)))
    (hseed : M.mem (denote seed) s.output)
    (hindices : ∀ k : ℤ, NativeBridge.integerValue (denote first) ≤ k →
      k ≤ NativeBridge.integerValue (denote last) → M.mem (M.number (k : ℂ)) s.domain) :
    Obj (M := M) (RangeFoldObj M α β γ δ ε) :=
  ⟨⟨first, last, f, operation, seed, s⟩, hfirst, hlast, hf, hop, hseed, hindices⟩

theorem rangeFoldInOutput (p : Obj (M := M) (RangeFoldObj M α β γ δ ε)) :
    M.mem (denote p) p.val.signature.output := rangeFoldValue_mem p.val p.wd

theorem rangeFoldEmpty (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (h : NativeBridge.integerValue (denote p.val.last) < NativeBridge.integerValue (denote p.val.first)) :
    Same p p.val.seed := by
  change foldValue _ _ _ _ = _
  have hz : (NativeBridge.integerValue (denote p.val.last) -
    NativeBridge.integerValue (denote p.val.first) + 1).toNat = 0 := by omega
  simp only [integerFoldIndices, hz, List.range_zero, List.map_nil, foldValue, List.foldl_nil]
theorem rangeFoldEmptyOfLt (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (h : Lt p.val.last p.val.first) : Same p p.val.seed := by
  apply rangeFoldEmpty p
  have ha : denote p.val.last = M.number ((NativeBridge.integerValue (denote p.val.last) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.2.1
  have hb : denote p.val.first = M.number ((NativeBridge.integerValue (denote p.val.first) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.1
  have hl := (NativeBridge.lt_iff_ofDenoteReal p.val.last p.val.first _ _ ha hb).mp h
  exact_mod_cast hl

end FoldSemantics
end Litex

namespace Litex
section FiniteFoldSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def foldEnumeration (A : M.Value) : List M.Value := by
  classical
  exact if h : (memberSet A).Finite then h.toFinset.toList else []

omit F in
theorem foldEnumeration_mem (A x : M.Value) (h : (memberSet A).Finite) :
    x ∈ foldEnumeration A ↔ M.mem x A := by
  classical
  unfold foldEnumeration
  split_ifs
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset]
  rfl

noncomputable def finiteFoldValue (A f operation seed : M.Value) : M.Value :=
  foldValue (foldEnumeration A) f operation seed

def foldCommutative (E operation : M.Value) : Prop :=
  ∀ a, M.mem a E → ∀ b, M.mem b E → foldApply2 operation a b = foldApply2 operation b a

def foldAssociative (E operation : M.Value) : Prop :=
  ∀ a, M.mem a E → ∀ b, M.mem b E → ∀ c, M.mem c E →
    foldApply2 operation (foldApply2 operation a b) c =
      foldApply2 operation a (foldApply2 operation b c)

structure FiniteFoldObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  set : Obj (M := M) α
  function : Obj (M := M) β
  operation : Obj (M := M) γ
  seed : Obj (M := M) δ
  signature : FunctionSignature M

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
variable [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]

def finiteFoldWD (p : FiniteFoldObj M α β γ δ) : Prop :=
  IsFiniteSet p.set ∧ In p.function (fnSet p.signature) ∧
  In p.operation (fnSet (homogeneousFoldSignature p.signature.output p.signature.output_isSet)) ∧
  M.mem (denote p.seed) p.signature.output ∧
  (∀ i, M.mem i (denote p.set) → M.mem i p.signature.domain) ∧
  foldCommutative p.signature.output (denote p.operation) ∧
  foldAssociative p.signature.output (denote p.operation)

theorem finiteFoldValue_mem (p : FiniteFoldObj M α β γ δ) (h : finiteFoldWD p) :
    M.mem (finiteFoldValue (denote p.set) (denote p.function)
      (denote p.operation) (denote p.seed)) p.signature.output := by
  apply foldValue_mem p.signature _ _ _ _ h.2.1 h.2.2.1 h.2.2.2.1
  intro i hi
  exact h.2.2.2.2.1 i ((foldEnumeration_mem _ _ h.1).mp hi)

noncomputable instance finiteFoldRepresentation : Representation M (FiniteFoldObj M α β γ δ) where
  wd := finiteFoldWD
  denote p := finiteFoldValue (denote p.set) (denote p.function) (denote p.operation) (denote p.seed)
  wd_isSet {p} h := M.member_isSet (finiteFoldValue_mem p h)

noncomputable def finiteFold (A : Obj (M := M) α) (f : Obj (M := M) β)
    (operation : Obj (M := M) γ) (seed : Obj (M := M) δ) (s : FunctionSignature M)
    (hfinite : IsFiniteSet A) (hf : In f (fnSet s))
    (hop : In operation (fnSet (homogeneousFoldSignature s.output s.output_isSet)))
    (hseed : M.mem (denote seed) s.output)
    (hcover : ∀ i, M.mem i (denote A) → M.mem i s.domain)
    (hcomm : foldCommutative s.output (denote operation))
    (hassoc : foldAssociative s.output (denote operation)) :
    Obj (M := M) (FiniteFoldObj M α β γ δ) :=
  ⟨⟨A, f, operation, seed, s⟩, hfinite, hf, hop, hseed, hcover, hcomm, hassoc⟩

theorem finiteFoldInOutput (p : Obj (M := M) (FiniteFoldObj M α β γ δ)) :
    M.mem (denote p) p.val.signature.output := finiteFoldValue_mem p.val p.wd

omit F in
theorem foldEnumeration_empty (A : M.Value) (h : ∀ x, ¬ M.mem x A) :
    foldEnumeration A = [] := by
  classical
  unfold foldEnumeration
  split_ifs with hf
  · have hz : hf.toFinset = ∅ := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
      exact h x
    rw [hz]
    exact Finset.toList_empty
  · rfl

theorem finiteFoldEmpty (p : Obj (M := M) (FiniteFoldObj M α β γ δ))
    (h : Same p.val.set emptySet) : Same p p.val.seed := by
  change foldValue (foldEnumeration (denote p.val.set)) _ _ _ = _
  have he : denote p.val.set = F.emptyValue := h
  rw [foldEnumeration_empty _ (fun x hx => (F.empty_members x) (he ▸ hx))]
  rfl

end FiniteFoldSemantics
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem foldValue_perm (s : FunctionSignature M) (f op : M.Value)
    (hf : M.mem f (F.fnSetValue s.domain s.output))
    (hop : M.mem op (F.fnSetValue (homogeneousFoldSignature s.output s.output_isSet).domain s.output))
    (comm : foldCommutative s.output op) (assoc : foldAssociative s.output op)
    {xs ys : List M.Value} (p : xs.Perm ys) (seed : M.Value) (hs : M.mem seed s.output)
    (hx : ∀ x ∈ xs, M.mem x s.domain) : foldValue xs f op seed = foldValue ys f op seed := by
  have exchange (seed a b : M.Value) (hs : M.mem seed s.output)
      (ha : M.mem a s.domain) (hb : M.mem b s.domain) :
      foldApply2 op (foldApply2 op seed (F.callValue f a)) (F.callValue f b) =
      foldApply2 op (foldApply2 op seed (F.callValue f b)) (F.callValue f a) := by
    have hfa := F.call_mem _ _ _ _ hf ha
    have hfb := F.call_mem _ _ _ _ hf hb
    rw [assoc seed hs _ hfa _ hfb, comm _ hfa _ hfb, ← assoc seed hs _ hfb _ hfa]
  induction p generalizing seed with
  | nil => rfl
  | cons a p ih =>
    apply ih
    · exact foldApply2_mem s op seed _ hop hs (F.call_mem _ _ _ _ hf (hx _ (by simp)))
    · intro x h
      exact hx x (List.mem_cons_of_mem a h)
  | swap a b xs =>
    change foldValue xs f op (foldApply2 op (foldApply2 op seed (F.callValue f b)) (F.callValue f a)) = _
    rw [exchange seed b a hs (hx b (by simp)) (hx a (by simp))]
    rfl
  | trans p q ihp ihq =>
    exact (ihp seed hs hx).trans (ihq seed hs (fun x h => hx x (p.mem_iff.mpr h)))

omit F in
theorem foldEnumeration_nodup (A : M.Value) : (foldEnumeration A).Nodup := by
  classical
  unfold foldEnumeration
  split_ifs
  · exact Finset.nodup_toList _
  · exact List.nodup_nil

omit F in
theorem foldEnumeration_singleton (A x : M.Value) (h : (memberSet A).Finite)
    (hm : ∀ y, M.mem y A ↔ y = x) : foldEnumeration A = [x] := by
  classical
  have hp : (foldEnumeration A).Perm [x] :=
    (List.perm_ext_iff_of_nodup (foldEnumeration_nodup A) (by simp)).mpr (fun y => by
      rw [foldEnumeration_mem _ _ h, List.mem_singleton]
      exact hm y)
  exact List.perm_singleton.mp hp

theorem integerFoldIndices_last (a b : ℤ) (h : a ≤ b) :
    integerFoldIndices a b = integerFoldIndices a (b - 1) ++ [b] := by
  have hn : (b-a+1).toNat = (b-a).toNat + 1 := by omega
  have hb : a + ((b-a).toNat : ℤ) = b := by omega
  unfold integerFoldIndices
  rw [hn, List.range_succ, List.map_append]
  simp only [List.map_singleton, hb]
  have he : b - 1 - a + 1 = b - a := by omega
  rw [he]

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
variable [Representation M α] [Representation M β] [Representation M γ]
variable [Representation M δ] [Representation M ε]

theorem rangeFoldDenote (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (a b : ℤ) (ha : denote p.val.first = M.number (a : ℂ))
    (hb : denote p.val.last = M.number (b : ℂ)) (value : M.Value)
    (h : foldValue ((integerFoldIndices a b).map (fun (k : ℤ) => M.number (k : ℂ)))
      (denote p.val.function) (denote p.val.operation) (denote p.val.seed) = value) :
    denote p = value := by
  change rangeFoldValue _ _ _ _ _ = _
  unfold rangeFoldValue
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number]
  exact h

theorem finiteFoldEnumerate (p : Obj (M := M) (FiniteFoldObj M α β γ δ))
    (xs : List M.Value) (hd : xs.Nodup)
    (hx : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs) :
    denote p = foldValue xs (denote p.val.function) (denote p.val.operation) (denote p.val.seed) := by
  change foldValue (foldEnumeration _) _ _ _ = _
  have hp : (foldEnumeration (denote p.val.set)).Perm xs :=
    (List.perm_ext_iff_of_nodup (foldEnumeration_nodup _) hd).mpr (fun x =>
      (foldEnumeration_mem _ _ p.wd.1).trans (hx x))
  exact foldValue_perm p.val.signature _ _ p.wd.2.1 p.wd.2.2.1
    p.wd.2.2.2.2.2.1 p.wd.2.2.2.2.2.2 hp _ p.wd.2.2.2.1
    (fun x h => p.wd.2.2.2.2.1 x ((foldEnumeration_mem _ _ p.wd.1).mp h))

theorem finiteFoldSingleton (p : Obj (M := M) (FiniteFoldObj M α β γ δ))
    (x : M.Value) (hx : ∀ y, M.mem y (denote p.val.set) ↔ y = x) :
    denote p = foldApply2 (denote p.val.operation) (denote p.val.seed)
      (F.callValue (denote p.val.function) x) := by
  change foldValue (foldEnumeration _) _ _ _ = _
  rw [foldEnumeration_singleton _ _ p.wd.1 hx]
  rfl

end Litex

namespace Litex
variable {M : Semantics.{u}}
theorem integerValue_nonneg_of_natural {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a N) : 0 ≤ NativeBridge.integerValue (denote a) := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp ha
  have hc : (n : ℂ) = ((n : ℤ) : ℂ) := by simp
  rw [hn, hc, NativeBridge.integerValue_number]
  exact Int.natCast_nonneg n

theorem integerInNaturalAbove {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a N) (k : ℤ)
    (hk : NativeBridge.integerValue (denote a) ≤ k) :
    M.mem (M.number (k : ℂ)) (M.standard .natural) := by
  have hn : 0 ≤ k := le_trans (integerValue_nonneg_of_natural a ha) hk
  refine (M.natural_members _).mpr ⟨k.toNat, congrArg M.number ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hn).symm

theorem integerBoundsEmpty {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (i j : ℤ)
    (ha : Same a (number (i : ℂ))) (hb : Same b (number (j : ℂ))) (h : j < i) :
    ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → False := by
  change denote a = M.number (i : ℂ) at ha
  change denote b = M.number (j : ℂ) at hb
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number]
  omega
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
theorem rangeFoldValue_last (a b f op seed : M.Value)
    (hb : M.mem b (M.standard .integer))
    (h : NativeBridge.integerValue a ≤ NativeBridge.integerValue b) :
    rangeFoldValue a b f op seed = foldApply2 op
      (rangeFoldValue a (M.subValue b (M.number 1)) f op seed) (F.callValue f b) := by
  have hbv := NativeBridge.integerValue_spec b hb
  have hsub : M.subValue b (M.number 1) = M.number ((NativeBridge.integerValue b - 1 : ℤ) : ℂ) := by
    conv_lhs => rw [hbv, M.sub_numbers]
    congr 1
    push_cast
    rfl
  have hp : NativeBridge.integerValue (M.subValue b (M.number 1)) = NativeBridge.integerValue b - 1 := by
    rw [hsub, NativeBridge.integerValue_number]
  unfold rangeFoldValue
  rw [hp, integerFoldIndices_last _ _ h, List.map_append]
  simp only [List.map_singleton, foldValue, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← hbv]

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
variable [Representation M α] [Representation M β] [Representation M γ]
variable [Representation M δ] [Representation M ε]

theorem rangeFoldLast (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (h : Le p.val.first p.val.last) :
    denote p = foldApply2 (denote p.val.operation)
      (rangeFoldValue (denote p.val.first) (M.subValue (denote p.val.last) (M.number 1))
        (denote p.val.function) (denote p.val.operation) (denote p.val.seed))
      (F.callValue (denote p.val.function) (denote p.val.last)) := by
  apply rangeFoldValue_last _ _ _ _ _ p.wd.2.1
  have ha : denote p.val.first = M.number ((NativeBridge.integerValue (denote p.val.first) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.1
  have hb : denote p.val.last = M.number ((NativeBridge.integerValue (denote p.val.last) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.2.1
  have hl := (NativeBridge.le_iff_ofDenoteReal p.val.first p.val.last _ _ ha hb).mp h
  exact_mod_cast hl
end Litex

namespace Litex
variable {M : Semantics.{u}}
theorem integerLowerBound {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a Z) (k : ℤ)
    (hk : NativeBridge.integerValue (denote a) ≤ k) : Le a (number (k : ℂ)) := by
  refine NativeBridge.leOfDenoteReal a (number (k : ℂ))
    (NativeBridge.integerValue (denote a) : ℝ) (k : ℝ)
    (NativeBridge.integerValue_spec _ ha) ?_ ?_
  · change M.number (k : ℂ) = M.number ((k : ℝ) : ℂ)
    simp only [Complex.ofReal_intCast]
  · exact_mod_cast hk

theorem integerUpperBound {α : Type v} [Representation M α]
    (b : Obj (M := M) α) (hb : In b Z) (k : ℤ)
    (hk : k ≤ NativeBridge.integerValue (denote b)) : Le (number (k : ℂ)) b := by
  refine NativeBridge.leOfDenoteReal (number (k : ℂ)) b
    (k : ℝ) (NativeBridge.integerValue (denote b) : ℝ)
    ?_ (NativeBridge.integerValue_spec _ hb) ?_
  · change M.number (k : ℂ) = M.number ((k : ℝ) : ℂ)
    simp only [Complex.ofReal_intCast]
  · exact_mod_cast hk

theorem integerRangeGuards {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (i j : ℤ)
    (ha : Same a (number (i : ℂ))) (hb : Same b (number (j : ℂ)))
    (G : M.Value → Prop) (h : ∀ k ∈ integerFoldIndices i j, G (M.number (k : ℂ))) :
    ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → G (M.number (k : ℂ)) := by
  change denote a = M.number (i : ℂ) at ha
  change denote b = M.number (j : ℂ) at hb
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number]
  exact fun k hlo hhi => h k ((integerFoldIndices_mem i j k).mpr ⟨hlo, hhi⟩)
end Litex

namespace Litex
variable {M : Semantics.{u}} [S : SetSemantics M]
theorem finiteGuardEmpty (G : M.Value → Prop) :
    ∀ x, M.mem x (denote (emptySet (M := M))) → G x :=
  fun x hx => (S.empty_members x hx).elim

theorem finiteGuardInsert {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (G : M.Value → Prop)
    (head : G (denote p.val.element))
    (tail : ∀ x, M.mem x (denote p.val.tail) → G x) :
    ∀ x, M.mem x (denote p) → G x := by
  intro x hx
  obtain h | h := (S.insert_members _ _ _).mp hx
  · exact h ▸ head
  · exact tail x h
end Litex

namespace Litex
noncomputable def nativeCoth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
noncomputable def nativeSech (x : ℝ) : ℝ := 1 / Real.cosh x
noncomputable def nativeCsch (x : ℝ) : ℝ := 1 / Real.sinh x

structure SinhObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sinhRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SinhObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.sinh (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sinh r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sinh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (SinhObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteSinh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.sinh r : ℝ) : ℂ) := by
  change realUnaryValue Real.sinh (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem sinhInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.sinh (NativeBridge.asReal p.val.arg p.wd),
    denoteSinh p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CoshObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance coshRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CoshObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.cosh (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.cosh r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def cosh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (CoshObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteCosh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.cosh r : ℝ) : ℂ) := by
  change realUnaryValue Real.cosh (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem coshInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.cosh (NativeBridge.asReal p.val.arg p.wd),
    denoteCosh p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure TanhObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance tanhRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (TanhObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.tanh (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.tanh r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def tanh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (TanhObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteTanh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanhObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.tanh r : ℝ) : ℂ) := by
  change realUnaryValue Real.tanh (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem tanhInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanhObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.tanh (NativeBridge.asReal p.val.arg p.wd),
    denoteTanh p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CothObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cothRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CothObj (M := M) α) where
  wd a := In a.arg R ∧ ¬ Same a.arg (number 0)
  denote a := realUnaryValue nativeCoth (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCoth r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def coth {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hzero : ¬ Same a (number 0)) :
    Obj (M := M) (CothObj (M := M) α) := ⟨⟨a⟩,ha,hzero⟩

theorem denoteCoth {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCoth r : ℝ) : ℂ) := by
  change realUnaryValue nativeCoth (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cothInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCoth (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCoth p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

structure SechObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sechRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SechObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue nativeSech (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeSech r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sech {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (SechObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteSech {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeSech r : ℝ) : ℂ) := by
  change realUnaryValue nativeSech (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem sechInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeSech (NativeBridge.asReal p.val.arg p.wd),
    denoteSech p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CschObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cschRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CschObj (M := M) α) where
  wd a := In a.arg R ∧ ¬ Same a.arg (number 0)
  denote a := realUnaryValue nativeCsch (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCsch r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def csch {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hzero : ¬ Same a (number 0)) :
    Obj (M := M) (CschObj (M := M) α) := ⟨⟨a⟩,ha,hzero⟩

theorem denoteCsch {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCsch r : ℝ) : ℂ) := by
  change realUnaryValue nativeCsch (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cschInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCsch (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCsch p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

theorem coshPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : Lt (number 0) p := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.ltOfDenoteReal (number 0) p 0 (Real.cosh x) rfl
    (denoteCosh p x (NativeBridge.asReal_spec p.val.arg p.wd)) (Real.cosh_pos x)

theorem sechPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : Lt (number 0) p := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.ltOfDenoteReal (number 0) p 0 (nativeSech x) rfl
    (denoteSech p x (NativeBridge.asReal_spec p.val.arg p.wd))
    (one_div_pos.mpr (Real.cosh_pos x))

theorem coshInRPos {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : In p RPos :=
  inRPos_intro p (coshInR p) (coshPositive p)

theorem sechInRPos {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : In p RPos :=
  inRPos_intro p (sechInR p) (sechPositive p)

theorem sinhNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α))
    (hne : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  have hn : x ≠ 0 := Complex.ofReal_ne_zero.mp (NativeBridge.nativeNonzeroOfDenote p.val.arg (x : ℂ) hx hne)
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (Real.sinh x : ℂ) 0
    (denoteSinh p x hx) rfl (Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr hn))

theorem coshNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (Real.cosh x : ℂ) 0
    (denoteCosh p x (NativeBridge.asReal_spec p.val.arg p.wd)) rfl
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos x)))

theorem sechNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (nativeSech x : ℂ) 0
    (denoteSech p x (NativeBridge.asReal_spec p.val.arg p.wd)) rfl
    (Complex.ofReal_ne_zero.mpr (one_div_ne_zero (ne_of_gt (Real.cosh_pos x))))

theorem cothNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd.1
  have hx := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hn : x ≠ 0 := Complex.ofReal_ne_zero.mp (NativeBridge.nativeNonzeroOfDenote p.val.arg (x : ℂ) hx p.wd.2)
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (nativeCoth x : ℂ) 0
    (denoteCoth p x hx) rfl (Complex.ofReal_ne_zero.mpr
      (div_ne_zero (ne_of_gt (Real.cosh_pos x)) (Real.sinh_ne_zero.mpr hn)))

theorem cschNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd.1
  have hx := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hn : x ≠ 0 := Complex.ofReal_ne_zero.mp (NativeBridge.nativeNonzeroOfDenote p.val.arg (x : ℂ) hx p.wd.2)
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (nativeCsch x : ℂ) 0
    (denoteCsch p x hx) rfl (Complex.ofReal_ne_zero.mpr (one_div_ne_zero (Real.sinh_ne_zero.mpr hn)))

theorem cothInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) : In p RStar :=
  inRStar_intro p (cothInR p) (cothNonzero p)

theorem cschInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) : In p RStar :=
  inRStar_intro p (cschInR p) (cschNonzero p)

end Litex

namespace Litex
@[simp] theorem nativeSech_zero : nativeSech 0 = 1 := by simp [nativeSech]
end Litex

namespace Litex
theorem sinhDefinition {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α)) :
    denote p = M.divValue
      (M.subValue (realUnaryValue Real.exp (denote p.val.arg))
        (realUnaryValue Real.exp (M.negValue (denote p.val.arg)))) (M.number 2) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  rw [denoteSinh p x hx, hx, M.neg_numbers, ← Complex.ofReal_neg,
    realUnaryValue_number, realUnaryValue_number, M.sub_numbers,
    M.div_numbers _ _ (by norm_num)]
  apply congrArg M.number
  rw [Real.sinh_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]

theorem coshDefinition {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) :
    denote p = M.divValue
      (M.addValue (realUnaryValue Real.exp (denote p.val.arg))
        (realUnaryValue Real.exp (M.negValue (denote p.val.arg)))) (M.number 2) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  rw [denoteCosh p x hx, hx, M.neg_numbers, ← Complex.ofReal_neg,
    realUnaryValue_number, realUnaryValue_number, M.add_numbers,
    M.div_numbers _ _ (by norm_num)]
  apply congrArg M.number
  rw [Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
end Litex

namespace Litex

theorem hyperbolicPythagorean (x : ℝ) :
    (Real.cosh x : ℂ)^2 - (Real.sinh x : ℂ)^2 = 1 := by
  exact_mod_cast Real.cosh_sq_sub_sinh_sq x

theorem sinhDoubleAngle (x : ℝ) :
    (Real.sinh (2*x) : ℂ) = 2 * (Real.sinh x : ℂ) * (Real.cosh x : ℂ) := by
  exact_mod_cast Real.sinh_two_mul x

theorem coshDoubleAngle (x : ℝ) :
    (Real.cosh (2*x) : ℂ) = (Real.cosh x : ℂ)^2 + (Real.sinh x : ℂ)^2 := by
  exact_mod_cast Real.cosh_two_mul x

theorem sinhAddition (x y : ℝ) :
    (Real.sinh (x+y) : ℂ) = (Real.sinh x : ℂ)*(Real.cosh y : ℂ) +
      (Real.cosh x : ℂ)*(Real.sinh y : ℂ) := by
  exact_mod_cast Real.sinh_add x y

theorem coshAddition (x y : ℝ) :
    (Real.cosh (x+y) : ℂ) = (Real.cosh x : ℂ)*(Real.cosh y : ℂ) +
      (Real.sinh x : ℂ)*(Real.sinh y : ℂ) := by
  exact_mod_cast Real.cosh_add x y

theorem tanhReciprocal (x : ℝ) :
    (Real.tanh x : ℂ) * (Real.cosh x : ℂ) = (Real.sinh x : ℂ) := by
  have h : Real.tanh x * Real.cosh x = Real.sinh x := by
    rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ (ne_of_gt (Real.cosh_pos x))]
  exact_mod_cast h

theorem cothReciprocal (x : ℝ) (hx : x ≠ 0) :
    (nativeCoth x : ℂ) * (Real.sinh x : ℂ) = (Real.cosh x : ℂ) := by
  have h : nativeCoth x * Real.sinh x = Real.cosh x := by
    exact div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)
  exact_mod_cast h

theorem sechReciprocal (x : ℝ) :
    (nativeSech x : ℂ) * (Real.cosh x : ℂ) = 1 := by
  have h : nativeSech x * Real.cosh x = 1 := div_mul_cancel₀ _ (ne_of_gt (Real.cosh_pos x))
  exact_mod_cast h

theorem cschReciprocal (x : ℝ) (hx : x ≠ 0) :
    (nativeCsch x : ℂ) * (Real.sinh x : ℂ) = 1 := by
  have h : nativeCsch x * Real.sinh x = 1 := div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)
  exact_mod_cast h

theorem tanhThroughSech (x : ℝ) :
    (Real.tanh x : ℂ) = (Real.sinh x : ℂ) * (nativeSech x : ℂ) := by
  simp only [Real.tanh_eq_sinh_div_cosh, nativeSech, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem cothThroughCsch (x : ℝ) :
    (nativeCoth x : ℂ) = (Real.cosh x : ℂ) * (nativeCsch x : ℂ) := by
  rw [nativeCoth, nativeCsch, Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem tanhCothProduct (x : ℝ) (hx : x ≠ 0) :
    (Real.tanh x : ℂ) * (nativeCoth x : ℂ) = 1 := by
  have h : Real.tanh x * nativeCoth x = 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, nativeCoth]
    field_simp
  exact_mod_cast h

theorem tanhSechSquare (x : ℝ) :
    1 - (Real.tanh x : ℂ)^2 = (nativeSech x : ℂ)^2 := by
  have h : 1 - (Real.tanh x)^2 = (nativeSech x)^2 := by
    rw [Real.tanh_eq_sinh_div_cosh, nativeSech]
    have hc := ne_of_gt (Real.cosh_pos x)
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  exact_mod_cast h

theorem cothCschSquare (x : ℝ) (hx : x ≠ 0) :
    (nativeCoth x : ℂ)^2 - 1 = (nativeCsch x : ℂ)^2 := by
  have h : (nativeCoth x)^2 - 1 = (nativeCsch x)^2 := by
    rw [nativeCoth, nativeCsch]
    have hs := Real.sinh_ne_zero.mpr hx
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  exact_mod_cast h

theorem expThroughHyperbolic {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    realUnaryValue Real.exp (denote a) =
      M.addValue (realUnaryValue Real.cosh (denote a)) (realUnaryValue Real.sinh (denote a)) := by
  obtain ⟨x, hx⟩ := (M.real_members _).mp ha
  rw [hx, realUnaryValue_number, realUnaryValue_number, realUnaryValue_number, M.add_numbers]
  apply congrArg M.number
  exact_mod_cast (Real.cosh_add_sinh x).symm

theorem expNegativeThroughHyperbolic {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    realUnaryValue Real.exp (M.negValue (denote a)) =
      M.subValue (realUnaryValue Real.cosh (denote a)) (realUnaryValue Real.sinh (denote a)) := by
  obtain ⟨x, hx⟩ := (M.real_members _).mp ha
  rw [hx, M.neg_numbers, ← Complex.ofReal_neg, realUnaryValue_number,
    realUnaryValue_number, realUnaryValue_number, M.sub_numbers]
  apply congrArg M.number
  exact_mod_cast (Real.cosh_sub_sinh x).symm
end Litex

namespace Litex

structure MatrixSetObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  carrier : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

def matrixIndexValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (dimension : Obj (M := M) α) : M.Value :=
  F.sepValue (M.standard .integer) (ClosedRangeObj.condition ⟨number 1, dimension⟩)

theorem matrixIndexValue_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (dimension : Obj (M := M) α) :
    M.isSet (matrixIndexValue dimension) := F.sep_isSet _ _ (M.standard_isSet .integer)

noncomputable def matrixDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![matrixIndexValue rows, matrixIndexValue cols])
    (fun _ => True)

theorem matrixDomain_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) : M.isSet (matrixDomain rows cols) :=
  F.sep_isSet _ _ (FiniteFunction.cart_isSet _ (by
    intro i; fin_cases i <;> exact matrixIndexValue_isSet _))

noncomputable instance matrixSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixSetObj (M := M) α β γ) where
  wd s := IsSet s.carrier ∧ In s.rows N ∧ In s.cols N
  denote s := F.fnSetValue (matrixDomain s.rows s.cols) (denote s.carrier)
  wd_isSet {s} h := F.fnSet_isSet _ _ (matrixDomain_isSet s.rows s.cols) h.1

noncomputable def matrixSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (S : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hS : IsSet S) (hm : In m N) (hn : In n N) :
    Obj (M := M) (MatrixSetObj (M := M) α β γ) := ⟨⟨S,m,n⟩,hS,hm,hn⟩

noncomputable def matrixSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (s : Obj (M := M) (MatrixSetObj (M := M) α β γ)) : FunctionSignature M :=
  ⟨matrixDomain s.val.rows s.val.cols, matrixDomain_isSet s.val.rows s.val.cols,
    denote s.val.carrier, s.wd.1⟩

theorem matrixSet_eq_fnSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (s : Obj (M := M) (MatrixSetObj (M := M) α β γ)) :
    Same s (fnSet (matrixSignature s)) := rfl
end Litex

namespace Litex

structure ZeroMatrixObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  rows : Obj (M := M) α
  cols : Obj (M := M) β

noncomputable def zeroMatrixSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) : FunctionSignature M :=
  ⟨matrixDomain m n, matrixDomain_isSet m n, M.standard .real, M.standard_isSet .real⟩

noncomputable instance zeroMatrixRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (ZeroMatrixObj (M := M) α β) where
  wd a := In a.rows N ∧ In a.cols N
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .real) (fun _ => M.number 0)
  wd_isSet {a} _ := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun _ _ => (M.real_members _).mpr ⟨0, by simp only [Complex.ofReal_zero]⟩))

noncomputable def zeroMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N) :
    Obj (M := M) (ZeroMatrixObj (M := M) α β) := ⟨⟨m,n⟩,hm,hn⟩

theorem zeroMatrixInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ZeroMatrixObj (M := M) α β)) :
    In p (fnSet (zeroMatrixSignature p.val.rows p.val.cols)) :=
  FunctionSemantics.graph_inFnSet _ _ _
    (fun _ _ => (M.real_members _).mpr ⟨0, by simp only [Complex.ofReal_zero]⟩)

theorem zeroMatrixCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ZeroMatrixObj (M := M) α β)) (x : M.Value)
    (hx : M.mem x (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) x = M.number 0 :=
  F.call_graphValue _ _ _
    (fun _ _ => (M.real_members _).mpr ⟨0, by simp only [Complex.ofReal_zero]⟩) x hx

theorem functionRealToComplex {M : Semantics.{u}} [F : FunctionSemantics M]
    {D f : M.Value} (h : M.mem f (F.fnSetValue D (M.standard .real))) :
    M.mem f (F.fnSetValue D (M.standard .complex)) :=
  F.fnSet_of_returns h (fun x hx => M.real_subset_complex _ (F.call_mem _ _ _ x h hx))
end Litex

namespace Litex

theorem matrixDomain_swap {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain rows cols)) :
    M.mem (FiniteFunction.pack2 (FiniteFunction.unpack2 p).2 (FiniteFunction.unpack2 p).1)
      (matrixDomain cols rows) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, ha, b, hb, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  apply (F.sep_members _ _ _).mpr
  refine ⟨?_, True.intro⟩
  rw [FiniteFunction.unpack_pack2]
  exact (FiniteFunction.cart2_members _ _ _).mpr ⟨b,hb,a,ha,rfl⟩

structure MatrixTransposeObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

noncomputable def matrixTransposeBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a p : M.Value) : M.Value :=
  F.callValue a (FiniteFunction.pack2 (FiniteFunction.unpack2 p).2 (FiniteFunction.unpack2 p).1)

noncomputable def matrixTransposeSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) (S : StandardSetValue) : FunctionSignature M :=
  ⟨matrixDomain cols rows, matrixDomain_isSet cols rows, M.standard S, M.standard_isSet S⟩

noncomputable instance matrixTransposeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixTransposeObj (M := M) α β γ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.matrix) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.cols a.rows) (M.standard .complex)
    (matrixTransposeBody (denote a.matrix))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun p hp => F.call_mem _ _ _ _ h.2.2 (matrixDomain_swap a.cols a.rows p hp)))

noncomputable def transpose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixTransposeObj (M := M) α β γ) := ⟨⟨A,m,n⟩,hm,hn,hA⟩

theorem transposeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows q hq))

theorem transposeCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.cols p.val.rows)) :
    F.callValue (denote p) q = matrixTransposeBody (denote p.val.matrix) q :=
  F.call_graphValue _ _ _
    (fun x hx => F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows x hx)) q hq

theorem transposeInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ))
    (hA : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (transposeInFnSet p)
  intro q hq
  rw [transposeCall p q hq]
  exact F.call_mem _ _ _ _ hA (matrixDomain_swap p.val.cols p.val.rows q hq)
end Litex

namespace Litex

theorem transpose_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.cols p.val.rows)
    (hbody : g.val.bodyValue = matrixTransposeBody (denote p.val.matrix)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixTransposeSignature p.val.rows p.val.cols .complex) g.val.signature
    (transposeInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [transposeCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex

theorem conjugateValueInComplex {M : Semantics.{u}} (a : M.Value)
    (h : M.mem a (M.standard .complex)) :
    M.mem (complexUnaryValue (fun z : ℂ => star z) a) (M.standard .complex) := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp h
  rw [hz, complexUnaryValue_number]
  exact (M.complex_members _).mpr ⟨star z,rfl⟩

theorem conjugateValueInReal {M : Semantics.{u}} (a : M.Value)
    (h : M.mem a (M.standard .real)) :
    M.mem (complexUnaryValue (fun z : ℂ => star z) a) (M.standard .real) := by
  obtain ⟨z,hz⟩ := (M.real_members _).mp h
  rw [hz, complexUnaryValue_number]
  exact (M.real_members _).mpr ⟨z,congrArg M.number (Complex.conj_ofReal z)⟩

structure MatrixConjugateTransposeObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

noncomputable def matrixConjugateTransposeBody {M : Semantics.{u}} [FunctionSemantics M]
    (a p : M.Value) : M.Value :=
  complexUnaryValue (fun z : ℂ => star z) (matrixTransposeBody a p)

noncomputable instance matrixConjugateTransposeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixConjugateTransposeObj (M := M) α β γ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.matrix) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.cols a.rows) (M.standard .complex)
    (matrixConjugateTransposeBody (denote a.matrix))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun p hp => conjugateValueInComplex _
      (F.call_mem _ _ _ _ h.2.2 (matrixDomain_swap a.cols a.rows p hp))))

noncomputable def conjugateTranspose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ) := ⟨⟨A,m,n⟩,hm,hn,hA⟩

theorem conjugateTransposeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => conjugateValueInComplex _
      (F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows q hq)))

theorem conjugateTransposeCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.cols p.val.rows)) :
    F.callValue (denote p) q = matrixConjugateTransposeBody (denote p.val.matrix) q :=
  F.call_graphValue _ _ _
    (fun x hx => conjugateValueInComplex _
      (F.call_mem _ _ _ _ p.wd.2.2 (matrixDomain_swap p.val.cols p.val.rows x hx))) q hq

theorem conjugateTransposeInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ))
    (hA : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixTransposeSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (conjugateTransposeInFnSet p)
  intro q hq
  rw [conjugateTransposeCall p q hq]
  exact conjugateValueInReal _
    (F.call_mem _ _ _ _ hA (matrixDomain_swap p.val.cols p.val.rows q hq))

theorem conjugateTranspose_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.cols p.val.rows)
    (hbody : g.val.bodyValue = matrixConjugateTransposeBody (denote p.val.matrix)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixTransposeSignature p.val.rows p.val.cols .complex) g.val.signature
    (conjugateTransposeInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [conjugateTransposeCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex

/-- The source identity formula is the size of the intersection of two singletons. -/
noncomputable def matrixIdentityEntry {M : Semantics.{u}} [S : SetSemantics M]
    (row col : M.Value) : M.Value :=
  M.number (finiteCard (S.sepValue (S.insertValue row S.emptyValue)
    (fun x => M.mem x (S.insertValue col S.emptyValue))) : ℂ)

theorem matrixIdentityEntry_inReal {M : Semantics.{u}} [S : SetSemantics M]
    (row col : M.Value) : M.mem (matrixIdentityEntry row col) (M.standard .real) := by
  exact (M.real_members _).mpr ⟨_, rfl⟩

noncomputable def matrixIdentityBody {M : Semantics.{u}} [FunctionSemantics M]
    (p : M.Value) : M.Value :=
  matrixIdentityEntry (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2

structure IdentityMatrixObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  order : Obj (M := M) α

noncomputable def identityMatrixSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : FunctionSignature M :=
  ⟨matrixDomain n n, matrixDomain_isSet n n, M.standard .real, M.standard_isSet .real⟩

noncomputable instance identityMatrixRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (IdentityMatrixObj (M := M) α) where
  wd a := In a.order N
  denote a := F.graphValue (matrixDomain a.order a.order) (M.standard .real) matrixIdentityBody
  wd_isSet _ := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun _ _ => matrixIdentityEntry_inReal _ _))

noncomputable def identityMatrix {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    Obj (M := M) (IdentityMatrixObj (M := M) α) := ⟨⟨n⟩,hn⟩

theorem identityMatrixInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (IdentityMatrixObj (M := M) α)) :
    In p (fnSet (identityMatrixSignature p.val.order)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _)

theorem identityMatrixCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (IdentityMatrixObj (M := M) α)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixIdentityBody q :=
  F.call_graphValue _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _) q hq

end Litex

namespace Litex

theorem finiteSetIntersect {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (IntersectObj (M := M) α β))
    (hA : IsFiniteSet p.val.left) (_hB : IsFiniteSet p.val.right) : IsFiniteSet p := by
  apply hA.subset
  intro x hx
  exact ((S.sep_members _ _ _).mp hx).1

theorem finiteSetIntersectFromLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (IntersectObj (M := M) α β))
    (hA : IsFiniteSet p.val.left) : IsFiniteSet p := by
  apply hA.subset
  intro x hx
  exact ((S.sep_members _ _ _).mp hx).1

theorem finiteSetIntersectFromRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (IntersectObj (M := M) α β))
    (hB : IsFiniteSet p.val.right) : IsFiniteSet p := by
  apply hB.subset
  intro x hx
  exact ((S.sep_members _ _ _).mp hx).2
end Litex

namespace Litex
theorem matrixIdentityEntrySelf {M : Semantics.{u}} [S : SetSemantics M]
    (a : M.Value) : matrixIdentityEntry a a = M.number 1 := by
  have h : memberSet (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue a S.emptyValue))) = {a} := by
    ext x
    simp only [memberSet, Set.mem_setOf_eq, S.sep_members, S.insert_members,
      S.empty_members, or_false, and_self, Set.mem_singleton_iff]
  unfold matrixIdentityEntry finiteCard
  rw [h, Set.ncard_singleton]
  norm_num

theorem matrixIdentityEntryDifferent {M : Semantics.{u}} [S : SetSemantics M]
    (a b : M.Value) (hab : a ≠ b) : matrixIdentityEntry a b = M.number 0 := by
  have h : memberSet (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue b S.emptyValue))) = ∅ := by
    ext x
    simp only [memberSet, Set.mem_setOf_eq, S.sep_members, S.insert_members,
      S.empty_members, or_false, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxa hxb
    exact hab (hxa.symm.trans hxb)
  unfold matrixIdentityEntry finiteCard
  rw [h, Set.ncard_empty]
  norm_num
end Litex

namespace Litex
inductive MatrixEntrywiseOp where
  | add
  | sub

def matrixEntrywiseValue {M : Semantics.{u}} (op : MatrixEntrywiseOp) (a b : M.Value) : M.Value :=
  match op with
  | .add => M.addValue a b
  | .sub => M.subValue a b

theorem matrixEntrywiseValue_complex {M : Semantics.{u}} (op : MatrixEntrywiseOp)
    {a b : M.Value} (ha : M.mem a (M.standard .complex)) (hb : M.mem b (M.standard .complex)) :
    M.mem (matrixEntrywiseValue op a b) (M.standard .complex) := by
  cases op with
  | add => exact M.add_closed ha hb
  | sub => exact Semantics.sub_closed ha hb

theorem matrixEntrywiseValue_real {M : Semantics.{u}} (op : MatrixEntrywiseOp)
    {a b : M.Value} (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    M.mem (matrixEntrywiseValue op a b) (M.standard .real) := by
  obtain ⟨a, rfl⟩ := (M.real_members _).mp ha
  obtain ⟨b, rfl⟩ := (M.real_members _).mp hb
  cases op with
  | add => exact (M.real_members _).mpr ⟨a+b, by
      change M.addValue _ _ = _
      rw [M.add_numbers, Complex.ofReal_add]⟩
  | sub => exact (M.real_members _).mpr ⟨a-b, by
      change M.subValue _ _ = _
      rw [M.sub_numbers, Complex.ofReal_sub]⟩

structure MatrixEntrywiseObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  operation : MatrixEntrywiseOp
  left : Obj (M := M) α
  right : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

theorem matrixDomain_repack {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain m n)) :
    M.mem (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2)
      (matrixDomain m n) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, _, b, _, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  simpa only [FiniteFunction.unpack_pack2] using hp

noncomputable def matrixEntrywiseBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (op : MatrixEntrywiseOp) (a b p : M.Value) : M.Value :=
  matrixEntrywiseValue op
    (F.callValue a (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))
    (F.callValue b (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))

noncomputable def matrixEntrywiseSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (rows : Obj (M := M) α) (cols : Obj (M := M) β) (S : StandardSetValue) : FunctionSignature M :=
  ⟨matrixDomain rows cols, matrixDomain_isSet rows cols, M.standard S, M.standard_isSet S⟩

noncomputable instance matrixEntrywiseRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixEntrywiseObj (M := M) α β γ δ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.left) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex)) ∧
    M.mem (denote a.right) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .complex)
    (matrixEntrywiseBody a.operation (denote a.left) (denote a.right))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => matrixEntrywiseValue_complex a.operation
      (F.call_mem _ _ _ _ h.2.2.1 (matrixDomain_repack a.rows a.cols q hq)) (F.call_mem _ _ _ _ h.2.2.2 (matrixDomain_repack a.rows a.cols q hq))))

noncomputable def matrixEntrywise {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (op : MatrixEntrywiseOp) (A : Obj (M := M) α) (B : Obj (M := M) β)
    (m : Obj (M := M) γ) (n : Obj (M := M) δ) (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hB : M.mem (denote B) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ) := ⟨⟨op,A,B,m,n⟩,hm,hn,hA,hB⟩

theorem matrixEntrywiseInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun q hq => matrixEntrywiseValue_complex p.val.operation
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_repack p.val.rows p.val.cols q hq)) (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols q hq)))

theorem matrixEntrywiseCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixEntrywiseBody p.val.operation (denote p.val.left) (denote p.val.right) q :=
  F.call_graphValue _ _ _ (fun x hx => matrixEntrywiseValue_complex p.val.operation
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_repack p.val.rows p.val.cols x hx)) (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols x hx))) q hq

theorem matrixEntrywiseInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ))
    (hA : M.mem (denote p.val.left) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real)))
    (hB : M.mem (denote p.val.right) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixEntrywiseInFnSet p)
  intro q hq
  rw [matrixEntrywiseCall p q hq]
  exact matrixEntrywiseValue_real _ (F.call_mem _ _ _ _ hA (matrixDomain_repack p.val.rows p.val.cols q hq)) (F.call_mem _ _ _ _ hB (matrixDomain_repack p.val.rows p.val.cols q hq))

theorem matrixEntrywise_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixEntrywiseObj (M := M) α β γ δ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixEntrywiseBody p.val.operation (denote p.val.left) (denote p.val.right)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixEntrywiseInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixEntrywiseCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
structure MatrixScaleObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  scalar : Obj (M := M) α
  matrix : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

noncomputable def matrixScaleBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (z a p : M.Value) : M.Value :=
  M.mulValue z (F.callValue a
    (FiniteFunction.pack2 (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))

noncomputable instance matrixScaleRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixScaleObj (M := M) α β γ δ) where
  wd a := In a.scalar C ∧ In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.matrix) (F.fnSetValue (matrixDomain a.rows a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .complex)
    (matrixScaleBody (denote a.scalar) (denote a.matrix))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => Semantics.mul_closed h.1
      (F.call_mem _ _ _ _ h.2.2.2 (matrixDomain_repack a.rows a.cols q hq))))

noncomputable def matrixScale {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (z : Obj (M := M) α) (A : Obj (M := M) β) (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hz : In z C) (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixScaleObj (M := M) α β γ δ) := ⟨⟨z,A,m,n⟩,hz,hm,hn,hA⟩

theorem matrixScaleInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun q hq => Semantics.mul_closed p.wd.1
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols q hq)))

theorem matrixScaleCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixScaleBody (denote p.val.scalar) (denote p.val.matrix) q :=
  F.call_graphValue _ _ _ (fun x hx => Semantics.mul_closed p.wd.1
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_repack p.val.rows p.val.cols x hx))) q hq

theorem matrixScaleInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ))
    (hA : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real)))
    (hz : In p.val.scalar R) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixScaleInFnSet p)
  intro q hq
  rw [matrixScaleCall p q hq]
  obtain ⟨z,hz⟩ := (M.real_members _).mp hz
  obtain ⟨a,ha⟩ := (M.real_members _).mp
    (F.call_mem _ _ _ _ hA (matrixDomain_repack p.val.rows p.val.cols q hq))
  exact (M.real_members _).mpr ⟨z*a, by
    change M.mulValue _ _ = _
    rw [hz, ha, M.mul_numbers, Complex.ofReal_mul]⟩

theorem matrixScale_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixScaleObj (M := M) α β γ δ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixScaleBody (denote p.val.scalar) (denote p.val.matrix)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixScaleInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixScaleCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
theorem matrixDomain_first {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain m n)) :
    M.mem (FiniteFunction.unpack2 p).1 (finiteSeqDomain m) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, ha, b, _, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  rw [FiniteFunction.unpack_pack2]
  exact (F.sep_members _ _ _).mpr ⟨ha, True.intro⟩

theorem matrixDomain_second {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (p : M.Value)
    (hp : M.mem p (matrixDomain m n)) :
    M.mem (FiniteFunction.unpack2 p).2 (finiteSeqDomain n) := by
  have base := ((F.sep_members _ _ _).mp hp).1
  obtain ⟨a, _, b, hb, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp base
  rw [FiniteFunction.unpack_pack2]
  exact (F.sep_members _ _ _).mpr ⟨hb, True.intro⟩

theorem mulValuesInReal {M : Semantics.{u}} {a b : M.Value}
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    M.mem (M.mulValue a b) (M.standard .real) := by
  obtain ⟨a,rfl⟩ := (M.real_members _).mp ha
  obtain ⟨b,rfl⟩ := (M.real_members _).mp hb
  exact (M.real_members _).mpr ⟨a*b, by rw [M.mul_numbers, Complex.ofReal_mul]⟩

structure MatrixOuterObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  left : Obj (M := M) α
  right : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

noncomputable def matrixOuterBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b p : M.Value) : M.Value :=
  M.mulValue (F.callValue a (FiniteFunction.unpack2 p).1)
    (F.callValue b (FiniteFunction.unpack2 p).2)

noncomputable instance matrixOuterRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixOuterObj (M := M) α β γ δ) where
  wd a := In a.rows N ∧ In a.cols N ∧
    M.mem (denote a.left) (F.fnSetValue (finiteSeqDomain a.rows) (M.standard .complex)) ∧
    M.mem (denote a.right) (F.fnSetValue (finiteSeqDomain a.cols) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.rows a.cols) (M.standard .complex)
    (matrixOuterBody (denote a.left) (denote a.right))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (fun q hq => Semantics.mul_closed
      (F.call_mem _ _ _ _ h.2.2.1 (matrixDomain_first a.rows a.cols q hq))
      (F.call_mem _ _ _ _ h.2.2.2 (matrixDomain_second a.rows a.cols q hq))))

noncomputable def matrixOuter {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hm : In m N) (hn : In n N)
    (hA : M.mem (denote A) (F.fnSetValue (finiteSeqDomain m) (M.standard .complex)))
    (hB : M.mem (denote B) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (MatrixOuterObj (M := M) α β γ δ) := ⟨⟨A,B,m,n⟩,hm,hn,hA,hB⟩

theorem matrixOuterInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun q hq => Semantics.mul_closed
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_first p.val.rows p.val.cols q hq))
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_second p.val.rows p.val.cols q hq)))

theorem matrixOuterCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixOuterBody (denote p.val.left) (denote p.val.right) q :=
  F.call_graphValue _ _ _ (fun x hx => Semantics.mul_closed
    (F.call_mem _ _ _ _ p.wd.2.2.1 (matrixDomain_first p.val.rows p.val.cols x hx))
    (F.call_mem _ _ _ _ p.wd.2.2.2 (matrixDomain_second p.val.rows p.val.cols x hx))) q hq

theorem matrixOuterInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ))
    (hA : M.mem (denote p.val.left) (F.fnSetValue (finiteSeqDomain p.val.rows) (M.standard .real)))
    (hB : M.mem (denote p.val.right) (F.fnSetValue (finiteSeqDomain p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixOuterInFnSet p)
  intro q hq
  rw [matrixOuterCall p q hq]
  exact mulValuesInReal
    (F.call_mem _ _ _ _ hA (matrixDomain_first p.val.rows p.val.cols q hq))
    (F.call_mem _ _ _ _ hB (matrixDomain_second p.val.rows p.val.cols q hq))

theorem matrixOuter_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixOuterObj (M := M) α β γ δ))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixOuterBody (denote p.val.left) (denote p.val.right)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixOuterInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixOuterCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
theorem tupleInFunctionSet {M : Semantics.{u}} [F : FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (s : FunctionSignature M)
    (hd : s.domain = FiniteFunction.indexSet n)
    (hc : ∀ i, M.mem (t.val.values i) s.output) : In t (fnSet s) := by
  have graph : M.mem (denote t) (F.fnSetValue (FiniteFunction.indexSet n)
      (FiniteFunction.finiteSetValue (List.ofFn t.val.values))) :=
    (F.fnSet_members _ _ _).mpr (FiniteFunction.tuple_isFunction t.val.values)
  rw [← hd] at graph
  apply F.fnSet_of_returns graph
  intro x hx
  rw [hd] at hx
  obtain ⟨i,rfl⟩ := (FiniteFunction.indexSet_members x).mp hx
  rw [tuple_coordinate]
  exact hc i
end Litex

namespace Litex
structure MatrixDiagonalObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  vector : Obj (M := M) α
  order : Obj (M := M) β

noncomputable def matrixDiagonalBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a p : M.Value) : M.Value :=
  M.mulValue (matrixIdentityEntry (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2)
    (F.callValue a (FiniteFunction.unpack2 p).1)

theorem matrixDiagonalBody_closed {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β)
    (ha : M.mem a (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (p : M.Value) (hp : M.mem p (matrixDomain n n)) :
    M.mem (matrixDiagonalBody a p) (M.standard .complex) :=
  Semantics.mul_closed (M.real_subset_complex _ (matrixIdentityEntry_inReal _ _))
    (F.call_mem _ _ _ _ ha (matrixDomain_first n n p hp))

noncomputable instance matrixDiagonalRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixDiagonalObj (M := M) α β) where
  wd a := In a.order N ∧
    M.mem (denote a.vector) (F.fnSetValue (finiteSeqDomain a.order) (M.standard .complex))
  denote a := F.graphValue (matrixDomain a.order a.order) (M.standard .complex)
    (matrixDiagonalBody (denote a.vector))
  wd_isSet {a} h := M.member_isSet (FunctionSemantics.graph_inFnSet _ _ _
    (matrixDiagonalBody_closed _ a.order h.2))

noncomputable def matrixDiagonal {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (v : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (hv : M.mem (denote v) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (MatrixDiagonalObj (M := M) α β) := ⟨⟨v,n⟩,hn,hv⟩

theorem matrixDiagonalInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  FunctionSemantics.graph_inFnSet _ _ _ (matrixDiagonalBody_closed _ p.val.order p.wd.2)

theorem matrixDiagonalCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixDiagonalBody (denote p.val.vector) q :=
  F.call_graphValue _ _ _ (matrixDiagonalBody_closed _ p.val.order p.wd.2) q hq

theorem matrixDiagonalInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β))
    (hv : M.mem (denote p.val.vector) (F.fnSetValue (finiteSeqDomain p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixDiagonalInFnSet p)
  intro q hq
  rw [matrixDiagonalCall p q hq]
  exact mulValuesInReal (matrixIdentityEntry_inReal _ _)
    (F.call_mem _ _ _ _ hv (matrixDomain_first p.val.order p.val.order q hq))

theorem matrixDiagonal_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDiagonalObj (M := M) α β)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.order p.val.order)
    (hbody : g.val.bodyValue = matrixDiagonalBody (denote p.val.vector)) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.order p.val.order .complex) g.val.signature
    (matrixDiagonalInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixDiagonalCall p q hq]
  have hg := FunctionSemantics.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
/-- Finite numerical aggregation over an explicitly represented input set. -/
structure FiniteAggregateOnObj {M : Semantics.{u}} (product : Bool)
    (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  set : Obj (M := M) α
  function : Obj (M := M) β
  input : Obj (M := M) γ
  signature : FunctionSignature M

noncomputable instance finiteAggregateOnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] (product : Bool)
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (FiniteAggregateOnObj (M := M) product α β γ) where
  wd p := IsFiniteSet p.set ∧ Subset p.set p.input ∧
    (∀ y, M.mem y p.signature.output → M.mem y (M.standard .complex)) ∧
    In p.function (fnSet p.signature) ∧
    (∀ x, M.mem x (denote p.input) → M.mem x p.signature.domain)
  denote p := M.number (finiteAggregateValue product (denote p.set)
    (fun x => NativeBridge.complexValue (F.callValue (denote p.function) x)))
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteAggregateOn {M : Semantics.{u}} [FunctionSemantics M]
    (product : Bool) {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (f : Obj (M := M) β) (input : Obj (M := M) γ)
    (s : FunctionSignature M) (hf : IsFiniteSet A) (hi : Subset A input)
    (hr : ∀ y, M.mem y s.output → M.mem y (M.standard .complex))
    (hfn : In f (fnSet s))
    (hd : ∀ x, M.mem x (denote input) → M.mem x s.domain) :
    Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ) :=
  ⟨⟨A,f,input,s⟩,hf,hi,hr,hfn,hd⟩

theorem finiteAggregateOnCallInOutput {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (x : M.Value) (hx : M.mem x (denote p.val.set)) :
    M.mem (F.callValue (denote p.val.function) x) p.val.signature.output :=
  F.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2 x (p.wd.2.1 x hx))

theorem finiteAggregateOnMember {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (A : StandardSetValue) (hs : p.val.signature.output = M.standard A) :
    In p (standardSet A) := by
  classical
  have hm : ∀ x ∈ p.wd.1.toFinset,
      M.mem (M.number (NativeBridge.complexValue (F.callValue (denote p.val.function) x)))
        (M.standard A) := by
    intro x hx
    have ho := finiteAggregateOnCallInOutput p x (p.wd.1.mem_toFinset.mp hx)
    rw [← NativeBridge.complexValue_spec _ (p.wd.2.2.1 _ ho), ← hs]
    exact ho
  change M.mem (M.number (finiteAggregateValue product _ _)) (M.standard A)
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf]
  generalize p.wd.1.toFinset = s at *
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))

theorem finiteAggregateOnListDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteAggregateOnObj (M := M) product α β γ))
    (xs : List ℂ) (value : ℂ)
    (hm : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs.map M.number)
    (hc : (if product then ∏ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))
      else ∑ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))) = value) :
    denote p = M.number value := by
  classical
  have ht : p.wd.1.toFinset = xs.toFinset.image M.number := by
    ext x
    rw [Set.Finite.mem_toFinset]
    change M.mem x (denote p.val.set) ↔ _
    rw [hm]
    simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]
  change M.number (finiteAggregateValue product _ _) = _
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf, ht]
  apply congrArg M.number
  have hi : ∀ a ∈ xs.toFinset, ∀ b ∈ xs.toFinset, M.number a = M.number b → a = b :=
    fun _ _ _ _ h => M.number_injective h
  cases product
  · simpa only [Bool.false_eq_true, ↓reduceIte, Finset.sum_image hi] using hc
  · simpa only [↓reduceIte, Finset.prod_image hi] using hc

end Litex

namespace Litex
theorem closedRangeFinite {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ClosedRangeObj (M := M) α β)) : IsFiniteSet p := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b,hb⟩ := (M.integer_members _).mp p.wd.2
  apply ((Set.finite_Icc a b).image (fun k : ℤ => M.number (k : ℂ))).subset
  intro x hx
  obtain ⟨l,r,k,hl,hr,hx,hlo,hhi⟩ := ((S.sep_members _ _ _).mp hx).2
  have left : l = a := by exact_mod_cast M.number_injective (hl.symm.trans ha)
  have right : r = b := by exact_mod_cast M.number_injective (hr.symm.trans hb)
  subst l; subst r
  exact ⟨k, ⟨hlo,hhi⟩, hx.symm⟩

theorem rangeFinite {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RangeObj (M := M) α β)) : IsFiniteSet p := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b,hb⟩ := (M.integer_members _).mp p.wd.2
  apply ((Set.finite_Icc a b).image (fun k : ℤ => M.number (k : ℂ))).subset
  intro x hx
  obtain ⟨l,r,k,hl,hr,hx,hlo,hhi⟩ := ((S.sep_members _ _ _).mp hx).2
  have left : l = a := by exact_mod_cast M.number_injective (hl.symm.trans ha)
  have right : r = b := by exact_mod_cast M.number_injective (hr.symm.trans hb)
  subst l; subst r
  exact ⟨k, ⟨hlo,hhi.le⟩, hx.symm⟩
end Litex

namespace Litex

theorem finiteAggregateValueMember {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (value : M.Value → ℂ) (S : StandardSetValue)
    (hf : (memberSet A).Finite)
    (hv : ∀ x, M.mem x A → M.mem (M.number (value x)) (M.standard S)) :
    M.mem (M.number (finiteAggregateValue product A value)) (M.standard S) := by
  classical
  unfold finiteAggregateValue
  rw [dif_pos hf]
  have hm : ∀ x ∈ hf.toFinset, M.mem (M.number (value x)) (M.standard S) :=
    fun x hx => hv x (hf.mem_toFinset.mp hx)
  generalize hf.toFinset = s at *
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) S
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember S _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) S
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember S _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))

theorem finiteAggregateValue_congr {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (f g : M.Value → ℂ) (h : ∀ x, M.mem x A → f x = g x) :
    finiteAggregateValue product A f = finiteAggregateValue product A g := by
  classical
  unfold finiteAggregateValue
  by_cases hf : (memberSet A).Finite
  · simp only [dif_pos hf]
    cases product
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Finset.sum_congr rfl (fun x hx => h x (hf.mem_toFinset.mp hx))
    · simp only [↓reduceIte]
      exact Finset.prod_congr rfl (fun x hx => h x (hf.mem_toFinset.mp hx))
  · simp only [dif_neg hf]

theorem matrixIndexFinite {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    (memberSet (matrixIndexValue n)).Finite :=
  closedRangeFinite (closedRange (number 1) n
    (NativeBridge.numberInZOfEq 1 1 (by norm_num)) (naturalToInteger n hn))

theorem matrixDomain_pair {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (a b : M.Value)
    (ha : M.mem a (matrixIndexValue m)) (hb : M.mem b (matrixIndexValue n)) :
    M.mem (FiniteFunction.pack2 a b) (matrixDomain m n) :=
  (F.sep_members _ _ _).mpr ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨a,ha,b,hb,rfl⟩,True.intro⟩

structure MatrixTraceObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β

noncomputable def matrixTraceValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) : ℂ :=
  finiteAggregateValue false (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 k k)))

noncomputable instance matrixTraceRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixTraceObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := M.number (matrixTraceValue (denote p.matrix) p.order)
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixTrace {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixTraceObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩

theorem matrixTraceInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixTraceObj (M := M) α β)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩

theorem matrixTraceInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixTraceObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) : In p R := by
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.order p.wd.1)
  intro k hk
  have hr := F.call_mem _ _ _ _ ha (matrixDomain_pair p.val.order p.val.order k k hk hk)
  rw [← NativeBridge.complexValue_spec _ (M.real_subset_complex _ hr)]
  exact hr

theorem matrixTraceFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixTraceObj (M := M) α β)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.order)
    (hb : f.val.bodyValue = fun k => F.callValue (denote p.val.matrix) (FiniteFunction.pack2 k k)) :
    denote p = M.number (finiteAggregateValue false (matrixIndexValue p.val.order)
      (fun k => NativeBridge.complexValue (F.callValue (denote f) k))) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k f.val.signature.domain := hD ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have h := F.call_graphValue _ _ _ f.wd k hd
  change F.callValue (denote f) k = f.val.bodyValue k at h
  rw [h, hb]
end Litex

namespace Litex
structure MatrixMultiplyObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) (ε : Type r) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] [Representation M ε] where
  left : Obj (M := M) α
  right : Obj (M := M) β
  rows : Obj (M := M) γ
  inner : Obj (M := M) δ
  cols : Obj (M := M) ε

noncomputable def matrixMultiplyTerm {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b q k : M.Value) : M.Value :=
  M.mulValue (F.callValue a (FiniteFunction.pack2 (FiniteFunction.unpack2 q).1 k))
    (F.callValue b (FiniteFunction.pack2 k (FiniteFunction.unpack2 q).2))

noncomputable def matrixMultiplyBody {M : Semantics.{u}} [F : FunctionSemantics M]
    {δ : Type t} [Representation M δ] (a b : M.Value) (n : Obj (M := M) δ) (q : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (F.callValue
      (F.graphValue (finiteSeqDomain n) (M.standard .complex) (matrixMultiplyTerm a b q)) k)))

noncomputable instance matrixMultiplyRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε] :
    Representation M (MatrixMultiplyObj (M := M) α β γ δ ε) where
  wd p := In p.rows N ∧ In p.inner N ∧ In p.cols N ∧
    M.mem (denote p.left) (F.fnSetValue (matrixDomain p.rows p.inner) (M.standard .complex)) ∧
    M.mem (denote p.right) (F.fnSetValue (matrixDomain p.inner p.cols) (M.standard .complex))
  denote p := F.graphValue (matrixDomain p.rows p.cols) (M.standard .complex)
    (matrixMultiplyBody (denote p.left) (denote p.right) p.inner)
  wd_isSet _ := M.member_isSet (F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩))

noncomputable def matrixMultiply {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ) (k : Obj (M := M) δ) (n : Obj (M := M) ε)
    (hm : In m N) (hk : In k N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m k) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain k n) (M.standard .complex))) :
    Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε) := ⟨⟨a,b,m,k,n⟩,hm,hk,hn,ha,hb⟩

theorem matrixMultiplyInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε)) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

theorem matrixMultiplyCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.rows p.val.cols)) :
    F.callValue (denote p) q = matrixMultiplyBody (denote p.val.left) (denote p.val.right) p.val.inner q :=
  F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) q hq

theorem matrixMultiplyInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε))
    (ha : M.mem (denote p.val.left) (F.fnSetValue (matrixDomain p.val.rows p.val.inner) (M.standard .real)))
    (hb : M.mem (denote p.val.right) (F.fnSetValue (matrixDomain p.val.inner p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.rows p.val.cols .real)) := by
  apply F.fnSet_of_returns (matrixMultiplyInFnSet p)
  intro q hq
  rw [matrixMultiplyCall p q hq]
  have hr := (F.sep_members _ _ _).mp (matrixDomain_first p.val.rows p.val.cols q hq)
  have hc := (F.sep_members _ _ _).mp (matrixDomain_second p.val.rows p.val.cols q hq)
  have ht : ∀ k, M.mem k (finiteSeqDomain p.val.inner) →
      M.mem (matrixMultiplyTerm (denote p.val.left) (denote p.val.right) q k) (M.standard .real) := by
    intro k hk
    have hi := (F.sep_members _ _ _).mp hk
    exact mulValuesInReal
      (F.call_mem _ _ _ _ ha (matrixDomain_pair p.val.rows p.val.inner _ _ hr.1 hi.1))
      (F.call_mem _ _ _ _ hb (matrixDomain_pair p.val.inner p.val.cols _ _ hi.1 hc.1))
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.inner p.wd.2.1)
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.inner) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have he := F.call_graphValue (finiteSeqDomain p.val.inner) (M.standard .complex)
    (matrixMultiplyTerm (denote p.val.left) (denote p.val.right) q)
    (fun z hz => M.real_subset_complex _ (ht z hz)) k hd
  rw [he, ← NativeBridge.complexValue_spec _ (M.real_subset_complex _ (ht k hd))]
  exact ht k hd

theorem matrixMultiply_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (MatrixMultiplyObj (M := M) α β γ δ ε))
    (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.rows p.val.cols)
    (hbody : g.val.bodyValue = matrixMultiplyBody (denote p.val.left) (denote p.val.right) p.val.inner) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.rows p.val.cols .complex) g.val.signature
    (matrixMultiplyInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixMultiplyCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
structure MatrixApplyObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    (γ : Type x) (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  matrix : Obj (M := M) α
  vector : Obj (M := M) β
  rows : Obj (M := M) γ
  cols : Obj (M := M) δ

noncomputable def matrixApplyTerm {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b q k : M.Value) : M.Value :=
  M.mulValue (F.callValue a (FiniteFunction.pack2 q k)) (F.callValue b k)
noncomputable def matrixApplyBody {M : Semantics.{u}} [F : FunctionSemantics M]
    {δ : Type t} [Representation M δ] (a b : M.Value) (n : Obj (M := M) δ) (q : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (matrixIndexValue n)
    (fun k => NativeBridge.complexValue (F.callValue
      (F.graphValue (finiteSeqDomain n) (M.standard .complex) (matrixApplyTerm a b q)) k)))
noncomputable def matrixApplySignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (rows : Obj (M := M) α) (S : StandardSetValue) : FunctionSignature M :=
  ⟨finiteSeqDomain rows,finiteSeqDomain_isSet rows,M.standard S,M.standard_isSet S⟩

noncomputable instance matrixApplyRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixApplyObj (M := M) α β γ δ) where
  wd p := In p.rows N ∧ In p.cols N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.rows p.cols) (M.standard .complex)) ∧
    M.mem (denote p.vector) (F.fnSetValue (finiteSeqDomain p.cols) (M.standard .complex))
  denote p := F.graphValue (finiteSeqDomain p.rows) (M.standard .complex)
    (matrixApplyBody (denote p.matrix) (denote p.vector) p.cols)
  wd_isSet _ := M.member_isSet (F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩))
noncomputable def matrixApply {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m : Obj (M := M) γ) (n : Obj (M := M) δ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (MatrixApplyObj (M := M) α β γ δ) := ⟨⟨a,b,m,n⟩,hm,hn,ha,hb⟩
theorem matrixApplyInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) :
    In p (fnSet (matrixApplySignature p.val.rows .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)
theorem matrixApplyCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) (q : M.Value)
    (hq : M.mem q (finiteSeqDomain p.val.rows)) :
    F.callValue (denote p) q = matrixApplyBody (denote p.val.matrix) (denote p.val.vector) p.val.cols q :=
  F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) q hq

theorem matrixApplyInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.rows p.val.cols) (M.standard .real)))
    (hb : M.mem (denote p.val.vector) (F.fnSetValue (finiteSeqDomain p.val.cols) (M.standard .real))) :
    In p (fnSet (matrixApplySignature p.val.rows .real)) := by
  apply F.fnSet_of_returns (matrixApplyInFnSet p)
  intro q hq
  rw [matrixApplyCall p q hq]
  have hr := (F.sep_members _ _ _).mp hq
  have ht : ∀ k, M.mem k (finiteSeqDomain p.val.cols) →
      M.mem (matrixApplyTerm (denote p.val.matrix) (denote p.val.vector) q k) (M.standard .real) := by
    intro k hk
    have hi := (F.sep_members _ _ _).mp hk
    exact mulValuesInReal
      (F.call_mem _ _ _ _ ha (matrixDomain_pair p.val.rows p.val.cols _ _ hr.1 hi.1))
      (F.call_mem _ _ _ _ hb hk)
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.cols p.wd.2.1)
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.cols) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have he := F.call_graphValue (finiteSeqDomain p.val.cols) (M.standard .complex)
    (matrixApplyTerm (denote p.val.matrix) (denote p.val.vector) q)
    (fun z hz => M.real_subset_complex _ (ht z hz)) k hd
  rw [he, ← NativeBridge.complexValue_spec _ (M.real_subset_complex _ (ht k hd))]
  exact ht k hd

theorem matrixApply_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixApplyObj (M := M) α β γ δ)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = finiteSeqDomain p.val.rows)
    (hbody : g.val.bodyValue = matrixApplyBody (denote p.val.matrix) (denote p.val.vector) p.val.cols) : Same p g := by
  apply functionExtOnDomain p g (matrixApplySignature p.val.rows .complex) g.val.signature
    (matrixApplyInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixApplyCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hbody q)).symm
end Litex

namespace Litex
structure FiniteInnerProductObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  left : Obj (M := M) α
  right : Obj (M := M) β
  dimension : Obj (M := M) γ
noncomputable def finiteInnerProductTerm {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b k : M.Value) : M.Value :=
  M.mulValue (complexUnaryValue (fun z : ℂ => star z) (F.callValue a k)) (F.callValue b k)
noncomputable def finiteInnerProductValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {γ : Type x} [Representation M γ] (a b : M.Value) (n : Obj (M := M) γ) : ℂ :=
  finiteAggregateValue false (matrixIndexValue n) (fun k => NativeBridge.complexValue (finiteInnerProductTerm a b k))
noncomputable instance finiteInnerProductRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (FiniteInnerProductObj (M := M) α β γ) where
  wd p := In p.dimension N ∧
    M.mem (denote p.left) (F.fnSetValue (finiteSeqDomain p.dimension) (M.standard .complex)) ∧
    M.mem (denote p.right) (F.fnSetValue (finiteSeqDomain p.dimension) (M.standard .complex))
  denote p := M.number (finiteInnerProductValue (denote p.left) (denote p.right) p.dimension)
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)
noncomputable def finiteInnerProduct {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (FiniteInnerProductObj (M := M) α β γ) := ⟨⟨a,b,n⟩,hn,ha,hb⟩
theorem finiteInnerProductInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩
theorem finiteInnerProductInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ))
    (ha : M.mem (denote p.val.left) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .real)))
    (hb : M.mem (denote p.val.right) (F.fnSetValue (finiteSeqDomain p.val.dimension) (M.standard .real))) : In p R := by
  apply finiteAggregateValueMember false _ _ .real (matrixIndexFinite p.val.dimension p.wd.1)
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.dimension) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have hr := mulValuesInReal (conjugateValueInReal _ (F.call_mem _ _ _ _ ha hd)) (F.call_mem _ _ _ _ hb hd)
  unfold finiteInnerProductTerm
  rw [← NativeBridge.complexValue_spec _ (M.real_subset_complex _ hr)]
  exact hr
theorem finiteInnerProductFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : f.val.bodyValue = finiteInnerProductTerm (denote p.val.left) (denote p.val.right)) :
    denote p = M.number (finiteAggregateValue false (matrixIndexValue p.val.dimension)
      (fun k => NativeBridge.complexValue (F.callValue (denote f) k))) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k f.val.signature.domain := hD ▸ (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have h := F.call_graphValue _ _ _ f.wd k hd
  change F.callValue (denote f) k = f.val.bodyValue k at h
  rw [h,hb]
end Litex

-- Finite Euclidean and Frobenius norms retain their source WD.
namespace Litex
theorem finiteRealSumNonnegative {M : Semantics.{u}} (A : M.Value) (f : M.Value → ℝ)
    (hf : (memberSet A).Finite) (h : ∀ x, M.mem x A → 0 ≤ f x) :
    ∃ r : ℝ, 0 ≤ r ∧ finiteAggregateValue false A (fun x => (f x : ℂ)) = (r : ℂ) := by
  classical
  refine ⟨∑ x ∈ hf.toFinset, f x, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun x hx => h x (hf.mem_toFinset.mp hx))
  · simp only [finiteAggregateValue, dif_pos hf, Bool.false_eq_true, ↓reduceIte]
    exact (map_sum Complex.ofRealHom f hf.toFinset).symm

theorem finiteMagnitudeSquareSumNonnegative {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (hf : (memberSet A).Finite) :
    ∃ r : ℝ, 0 ≤ r ∧ finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) = (r : ℂ) :=
  finiteRealSumNonnegative A (fun x => ‖f x‖ ^ 2) hf (fun x _ => sq_nonneg (‖f x‖))

theorem finiteNestedMagnitudeSquareSumNonnegative {M : Semantics.{u}}
    (A B : M.Value) (f : M.Value → M.Value → ℂ)
    (ha : (memberSet A).Finite) (hb : (memberSet B).Finite) :
    ∃ r : ℝ, 0 ≤ r ∧ finiteAggregateValue false A
      (fun x => finiteAggregateValue false B (fun y => ((‖f x y‖ ^ 2 : ℝ) : ℂ))) = (r : ℂ) := by
  classical
  have rows := fun x => finiteMagnitudeSquareSumNonnegative B (f x) hb
  choose r hr he using rows
  have same := finiteAggregateValue_congr false A
    (fun x => finiteAggregateValue false B (fun y => ((‖f x y‖ ^ 2 : ℝ) : ℂ)))
    (fun x => (r x : ℂ)) (fun x _ => he x)
  obtain ⟨s,hs,eq⟩ := finiteRealSumNonnegative A r ha (fun x _ => hr x)
  exact ⟨s,hs,same.trans eq⟩

theorem finiteMagnitudeSquareSumWD {M : Semantics.{u}} (A : M.Value)
    (f : M.Value → ℂ) (hf : (memberSet A).Finite) :
    In (number (M := M) (finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)))) R ∧
    Le (number 0) (number (M := M) (finiteAggregateValue false A (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)))) := by
  obtain ⟨r,hr,eq⟩ := finiteMagnitudeSquareSumNonnegative A f hf
  rw [eq]
  exact ⟨NativeBridge.numberInR r, 0, r, rfl, rfl, hr⟩

noncomputable def magnitudeSquareValue {M : Semantics.{u}} (a : M.Value) : M.Value :=
  M.powValue (complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) a) (M.number (2 : ℂ))

theorem magnitudeSquareValue_number {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .complex)) :
    magnitudeSquareValue a = M.number ((‖NativeBridge.complexValue a‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨z,rfl⟩ := (M.complex_members _).mp ha
  unfold magnitudeSquareValue
  rw [complexUnaryValue_number, NativeBridge.complexValue_number]
  change M.powValue (M.number (‖z‖ : ℂ)) (M.number ((2 : ℕ) : ℂ)) = _
  rw [M.pow_numbers_nat, Complex.ofReal_pow]

theorem magnitudeSquareValueInReal {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .complex)) : M.mem (magnitudeSquareValue a) (M.standard .real) := by
  rw [magnitudeSquareValue_number a ha]
  exact (M.real_members _).mpr ⟨_,rfl⟩

theorem sqrtValueRealOfNonnegative {M : Semantics.{u}} (z : ℂ)
    (h : ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)) :
    M.mem (sqrtValue (M.number z)) (M.standard .real) := by
  obtain ⟨r,_,rfl⟩ := h
  rw [sqrtValue_number]
  exact (M.real_members _).mpr ⟨_,rfl⟩

theorem sqrtValueSquareOfNonnegative {M : Semantics.{u}} (z : ℂ)
    (h : ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)) :
    M.powValue (sqrtValue (M.number z)) (M.number (2 : ℂ)) = M.number z := by
  obtain ⟨r,hr,rfl⟩ := h
  rw [sqrtValue_number]
  change M.powValue (M.number ((Real.sqrt r : ℝ) : ℂ)) (M.number ((2 : ℕ) : ℂ)) = _
  rw [M.pow_numbers_nat, ← Complex.ofReal_pow, Real.sq_sqrt hr]

structure EuclideanNormObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  vector : Obj (M := M) α
  dimension : Obj (M := M) β
noncomputable def euclideanNormSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) : ℂ :=
  finiteAggregateValue false (matrixIndexValue n)
    (fun k => ((‖NativeBridge.complexValue (F.callValue a k)‖ ^ 2 : ℝ) : ℂ))
noncomputable instance euclideanNormRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (EuclideanNormObj (M := M) α β) where
  wd p := In p.dimension N ∧
    M.mem (denote p.vector) (F.fnSetValue (finiteSeqDomain p.dimension) (M.standard .complex))
  denote p := sqrtValue (M.number (euclideanNormSum (denote p.vector) p.dimension))
  wd_isSet {p} h := M.member_isSet (sqrtValueRealOfNonnegative _
    (finiteMagnitudeSquareSumNonnegative _ _ (matrixIndexFinite p.dimension h.1)))
noncomputable def euclideanNorm {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (finiteSeqDomain n) (M.standard .complex))) :
    Obj (M := M) (EuclideanNormObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩
theorem euclideanNormInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) : In p R :=
  sqrtValueRealOfNonnegative _
    (finiteMagnitudeSquareSumNonnegative _ _ (matrixIndexFinite p.val.dimension p.wd.1))
theorem euclideanNormNonnegative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) : Le (number 0) p := by
  obtain ⟨r,_,hr⟩ := finiteMagnitudeSquareSumNonnegative (matrixIndexValue p.val.dimension)
    (fun k => NativeBridge.complexValue (F.callValue (denote p.val.vector) k)) (matrixIndexFinite p.val.dimension p.wd.1)
  refine ⟨0,Real.sqrt r,rfl,?_,Real.sqrt_nonneg r⟩
  change sqrtValue (M.number (euclideanNormSum _ _)) = _
  rw [show euclideanNormSum (denote p.val.vector) p.val.dimension = (r : ℂ) from hr, sqrtValue_number]
theorem euclideanNormSquare {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) :
    M.powValue (denote p) (M.number (2 : ℂ)) = M.number (euclideanNormSum (denote p.val.vector) p.val.dimension) :=
  sqrtValueSquareOfNonnegative _
    (finiteMagnitudeSquareSumNonnegative _ _ (matrixIndexFinite p.val.dimension p.wd.1))

theorem euclideanNormSumFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : f.val.bodyValue = fun k => magnitudeSquareValue (F.callValue (denote p.val.vector) k)) :
    euclideanNormSum (denote p.val.vector) p.val.dimension =
      finiteAggregateValue false (matrixIndexValue p.val.dimension)
        (fun k => NativeBridge.complexValue (F.callValue (denote f) k)) := by
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.dimension) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  have he := F.call_graphValue _ _ _ f.wd k (hD ▸ hd)
  change F.callValue (denote f) k = f.val.bodyValue k at he
  rw [he,hb]
  dsimp only
  rw [magnitudeSquareValue_number _ (F.call_mem _ _ _ _ p.wd.2 hd), NativeBridge.complexValue_number]

theorem euclideanNormFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.dimension)
    (hb : f.val.bodyValue = fun k => magnitudeSquareValue (F.callValue (denote p.val.vector) k)) :
    denote p = sqrtValue (M.number (finiteAggregateValue false (matrixIndexValue p.val.dimension)
      (fun k => NativeBridge.complexValue (F.callValue (denote f) k)))) :=
  congrArg (fun z => sqrtValue (M.number z)) (euclideanNormSumFormula p f hD hb)

theorem euclideanNormSquareInner {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (EuclideanNormObj (M := M) α β)) :
    M.powValue (denote p) (M.number (2 : ℂ)) =
      M.number (finiteInnerProductValue (denote p.val.vector) (denote p.val.vector) p.val.dimension) := by
  apply (euclideanNormSquare p).trans
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro k hk
  have hd : M.mem k (finiteSeqDomain p.val.dimension) := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  obtain ⟨z,hz⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2 hd)
  unfold finiteInnerProductTerm
  rw [hz,complexUnaryValue_number,M.mul_numbers,NativeBridge.complexValue_number,NativeBridge.complexValue_number]
  change ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z
  rw [mul_comm (star z) z, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

structure FrobeniusNormObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ
noncomputable def frobeniusNormSum {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} {γ : Type x} [Representation M β] [Representation M γ]
    (a : M.Value) (m : Obj (M := M) β) (n : Obj (M := M) γ) : ℂ :=
  finiteAggregateValue false (matrixIndexValue m) (fun r =>
    finiteAggregateValue false (matrixIndexValue n) (fun c =>
      ((‖NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 r c))‖ ^ 2 : ℝ) : ℂ)))
noncomputable instance frobeniusNormRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (FrobeniusNormObj (M := M) α β γ) where
  wd p := In p.rows N ∧ In p.cols N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.rows p.cols) (M.standard .complex))
  denote p := sqrtValue (M.number (frobeniusNormSum (denote p.matrix) p.rows p.cols))
  wd_isSet {p} h := M.member_isSet (sqrtValueRealOfNonnegative _
    (finiteNestedMagnitudeSquareSumNonnegative _ _ _
      (matrixIndexFinite p.rows h.1) (matrixIndexFinite p.cols h.2.1)))
noncomputable def frobeniusNorm {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (FrobeniusNormObj (M := M) α β γ) := ⟨⟨a,m,n⟩,hm,hn,ha⟩
theorem frobeniusNormInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) : In p R :=
  sqrtValueRealOfNonnegative _ (finiteNestedMagnitudeSquareSumNonnegative _ _ _
    (matrixIndexFinite p.val.rows p.wd.1) (matrixIndexFinite p.val.cols p.wd.2.1))
theorem frobeniusNormNonnegative {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) : Le (number 0) p := by
  obtain ⟨r,_,hr⟩ := finiteNestedMagnitudeSquareSumNonnegative
    (matrixIndexValue p.val.rows) (matrixIndexValue p.val.cols)
    (fun i j => NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 i j)))
    (matrixIndexFinite p.val.rows p.wd.1) (matrixIndexFinite p.val.cols p.wd.2.1)
  refine ⟨0,Real.sqrt r,rfl,?_,Real.sqrt_nonneg r⟩
  change sqrtValue (M.number (frobeniusNormSum _ _ _)) = _
  rw [show frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols = (r : ℂ) from hr, sqrtValue_number]
theorem frobeniusNormSquare {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) :
    M.powValue (denote p) (M.number (2 : ℂ)) =
      M.number (frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols) :=
  sqrtValueSquareOfNonnegative _ (finiteNestedMagnitudeSquareSumNonnegative _ _ _
    (matrixIndexFinite p.val.rows p.wd.1) (matrixIndexFinite p.val.cols p.wd.2.1))

-- The source row function calls the checked column graph inside its finite sum.
noncomputable def frobeniusNormRowValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {γ : Type x} [Representation M γ] (a : M.Value) (n : Obj (M := M) γ)
    (row : M.Value) : M.Value :=
  M.number (finiteAggregateValue false (matrixIndexValue n) (fun col =>
    NativeBridge.complexValue (F.callValue
      (F.graphValue (finiteSeqDomain n) (M.standard .real)
        (fun col => magnitudeSquareValue (F.callValue a (FiniteFunction.pack2 row col)))) col)))
theorem frobeniusNormRowValue_eq {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ))
    (row : M.Value) (hr : M.mem row (matrixIndexValue p.val.rows)) :
    frobeniusNormRowValue (denote p.val.matrix) p.val.cols row =
      M.number (finiteAggregateValue false (matrixIndexValue p.val.cols) (fun col =>
        ((‖NativeBridge.complexValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 row col))‖ ^ 2 : ℝ) : ℂ))) := by
  apply congrArg M.number
  apply finiteAggregateValue_congr
  intro col hc
  have member := fun c hc => F.call_mem _ _ _ _ p.wd.2.2
    (matrixDomain_pair p.val.rows p.val.cols row c hr hc)
  have ret : ∀ c, M.mem c (finiteSeqDomain p.val.cols) →
      M.mem (magnitudeSquareValue (F.callValue (denote p.val.matrix) (FiniteFunction.pack2 row c))) (M.standard .real) := by
    intro c hc
    exact magnitudeSquareValueInReal _ (member c ((F.sep_members _ _ _).mp hc).1)
  rw [F.call_graphValue _ _ _ ret col ((F.sep_members _ _ _).mpr ⟨hc,True.intro⟩)]
  rw [magnitudeSquareValue_number _ (member col hc), NativeBridge.complexValue_number]
theorem frobeniusNormSumFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.rows)
    (hb : f.val.bodyValue = fun row => frobeniusNormRowValue (denote p.val.matrix) p.val.cols row) :
    frobeniusNormSum (denote p.val.matrix) p.val.rows p.val.cols =
      finiteAggregateValue false (matrixIndexValue p.val.rows)
        (fun row => NativeBridge.complexValue (F.callValue (denote f) row)) := by
  apply finiteAggregateValue_congr
  intro row hr
  have hd : M.mem row (finiteSeqDomain p.val.rows) := (F.sep_members _ _ _).mpr ⟨hr,True.intro⟩
  have he := F.call_graphValue _ _ _ f.wd row (hD ▸ hd)
  change F.callValue (denote f) row = f.val.bodyValue row at he
  rw [he,hb]
  dsimp only
  rw [frobeniusNormRowValue_eq p row hr, NativeBridge.complexValue_number]
theorem frobeniusNormFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FrobeniusNormObj (M := M) α β γ)) (f : Obj (M := M) (FormulaFn M))
    (hD : f.val.signature.domain = finiteSeqDomain p.val.rows)
    (hb : f.val.bodyValue = fun row => frobeniusNormRowValue (denote p.val.matrix) p.val.cols row) :
    denote p = sqrtValue (M.number (finiteAggregateValue false (matrixIndexValue p.val.rows)
      (fun row => NativeBridge.complexValue (F.callValue (denote f) row)))) :=
  congrArg (fun z => sqrtValue (M.number z)) (frobeniusNormSumFormula p f hD hb)
end Litex

-- Determinants observe the original finite matrix on one-based source indices.
namespace Litex

theorem matrixIndexOfFin {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N)
    (i : Fin (NativeBridge.naturalValue (denote n))) :
    M.mem (FiniteFunction.index i) (matrixIndexValue n) := by
  change In (number ((i.val + 1 : ℕ) : ℂ))
    (closedRange (number 1) n (NativeBridge.numberInZOfEq 1 1 (by norm_num)) (naturalToInteger n hn))
  apply inClosedRangeOfDenote _ _ _ _ _ 1
    (NativeBridge.naturalValue (denote n)) ((i.val + 1 : ℕ) : ℤ)
  · change M.number 1 = M.number ((1 : ℤ) : ℂ)
    norm_num
  · simpa only [Complex.ofReal_intCast, Int.cast_natCast] using NativeBridge.naturalValue_spec (denote n) hn
  · change M.number ((i.val + 1 : ℕ) : ℂ) = M.number (((i.val + 1 : ℕ) : ℤ) : ℂ)
    norm_num
  · exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i.val))
  · exact_mod_cast (Nat.succ_le_of_lt i.isLt)

theorem matrixIndexNaturalNumber {M : Semantics.{u}} [FunctionSemantics M]
    (n k : ℕ) (hpos : 1 ≤ k) (hbound : k ≤ n) :
    M.mem (M.number (k : ℂ)) (matrixIndexValue (number (M := M) (n : ℂ))) := by
  let i : Fin n := ⟨k - 1, by omega⟩
  have h := matrixIndexOfFin (number (M := M) (n : ℂ)) (NativeBridge.numberInN n)
    (Fin.cast (NativeBridge.naturalValue_number (M := M) n).symm i)
  simpa [FiniteFunction.index, i, Nat.sub_add_cancel hpos] using h

noncomputable def matrixComplexOn {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (m n : ℕ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => NativeBridge.complexValue (F.callValue a (FiniteFunction.pack2 (FiniteFunction.index i) (FiniteFunction.index j)))
noncomputable def matrixComplexValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : M.Value) (m : Obj (M := M) α) (n : Obj (M := M) β) :
    Matrix (Fin (NativeBridge.naturalValue (denote m))) (Fin (NativeBridge.naturalValue (denote n))) ℂ :=
  matrixComplexOn a _ _
noncomputable def matrixDeterminantValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α) : M.Value :=
  M.number (matrixComplexValue a n n).det
structure MatrixDeterminantObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β
noncomputable instance matrixDeterminantRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixDeterminantObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := matrixDeterminantValue (denote p.matrix) p.order
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)
noncomputable def matrixDeterminant {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixDeterminantObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩
theorem matrixDeterminantInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDeterminantObj (M := M) α β)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩
theorem matrixDeterminantInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixDeterminantObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) : In p R := by
  let a := matrixComplexValue (denote p.val.matrix) p.val.order p.val.order
  have real : ∀ i j, ((a i j).re : ℂ) = a i j := by
    intro i j
    obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha
      (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.1 i) (matrixIndexOfFin _ p.wd.1 j)))
    change ((NativeBridge.complexValue _).re : ℂ) = NativeBridge.complexValue _
    rw [hr, NativeBridge.complexValue_number, Complex.ofReal_re]
  apply (M.real_members _).mpr
  refine ⟨(Matrix.det (fun i j => (a i j).re)), ?_⟩
  change M.number a.det = M.number (Complex.ofRealHom (Matrix.det (fun i j => (a i j).re)))
  apply congrArg M.number
  rw [Complex.ofRealHom.map_det]
  congr 1
  ext i j
  exact (real i j).symm

theorem matrixComplexValue_identity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    matrixComplexValue (denote (identityMatrix n hn)) n n = 1 := by
  classical
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [identityMatrixCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin n hn i) (matrixIndexOfFin n hn j))]
  simp only [matrixIdentityBody, FiniteFunction.unpack_pack2, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    rw [matrixIdentityEntrySelf, NativeBridge.complexValue_number, if_pos rfl]
  · rw [matrixIdentityEntryDifferent _ _ (fun eq => h (FiniteFunction.index_injective eq)), NativeBridge.complexValue_number, if_neg h]
theorem matrixDeterminantIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n N) :
    matrixDeterminantValue (denote (identityMatrix n hn)) n = M.number 1 := by
  unfold matrixDeterminantValue
  rw [matrixComplexValue_identity, Matrix.det_one]

theorem matrixComplexValue_transpose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixTransposeObj (M := M) α β γ)) :
    matrixComplexValue (denote p) p.val.cols p.val.rows =
      (matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols).transpose := by
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [transposeCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.2.1 i) (matrixIndexOfFin _ p.wd.1 j))]
  simp only [matrixTransposeBody, FiniteFunction.unpack_pack2, Matrix.transpose_apply]
theorem matrixDeterminantTranspose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixDeterminantValue (denote (transpose a n n hn hn ha)) n = matrixDeterminantValue (denote a) n := by
  unfold matrixDeterminantValue
  apply congrArg M.number
  exact (congrArg Matrix.det (matrixComplexValue_transpose (transpose a n n hn hn ha))).trans (Matrix.det_transpose _)

theorem matrixComplexValue_adjoint {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixConjugateTransposeObj (M := M) α β γ)) :
    matrixComplexValue (denote p) p.val.cols p.val.rows =
      (matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols).conjTranspose := by
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [conjugateTransposeCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.2.1 i) (matrixIndexOfFin _ p.wd.1 j))]
  simp only [matrixConjugateTransposeBody, matrixTransposeBody, FiniteFunction.unpack_pack2, Matrix.conjTranspose_apply]
  obtain ⟨z,hz⟩ := (M.complex_members _).mp (F.call_mem _ _ _ _ p.wd.2.2
    (matrixDomain_pair _ _ _ _ (matrixIndexOfFin _ p.wd.1 j) (matrixIndexOfFin _ p.wd.2.1 i)))
  rw [hz, complexUnaryValue_number, NativeBridge.complexValue_number, NativeBridge.complexValue_number]
theorem matrixDeterminantAdjoint {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    matrixDeterminantValue (denote (conjugateTranspose a n n hn hn ha)) n =
      complexUnaryValue (fun z : ℂ => star z) (matrixDeterminantValue (denote a) n) := by
  unfold matrixDeterminantValue
  rw [complexUnaryValue_number]
  apply congrArg M.number
  exact (congrArg Matrix.det (matrixComplexValue_adjoint (conjugateTranspose a n n hn hn ha))).trans (Matrix.det_conjTranspose _)

noncomputable def matrixEntryValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (i j : ℕ) : M.Value :=
  F.callValue a (FiniteFunction.pack2 (M.number (i : ℂ)) (M.number (j : ℂ)))
theorem matrixDeterminantValue_number {M : Semantics.{u}} [FunctionSemantics M]
    (a : M.Value) (n : ℕ) :
    matrixDeterminantValue a (number (n : ℂ)) = M.number (matrixComplexOn a n n).det := by
  unfold matrixDeterminantValue matrixComplexValue
  change M.number (matrixComplexOn a (NativeBridge.naturalValue (M.number (n : ℂ)))
    (NativeBridge.naturalValue (M.number (n : ℂ)))).det = _
  rw [NativeBridge.naturalValue_number]
theorem matrixDeterminantZero {M : Semantics.{u}} [FunctionSemantics M] (a : M.Value) :
    matrixDeterminantValue a (number 0) = M.number 1 := by
  have h := matrixDeterminantValue_number a 0
  simp only [Nat.cast_zero] at h
  rw [h, Matrix.det_fin_zero]
theorem matrixDeterminantOne {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 1) (number 1)) (M.standard .complex))) :
    matrixDeterminantValue a (number 1) = matrixEntryValue a 1 1 := by
  have h := matrixDeterminantValue_number a 1
  simp only [Nat.cast_one] at h
  rw [h, Matrix.det_fin_one]
  simp only [matrixComplexOn, matrixEntryValue, FiniteFunction.index, Fin.val_zero, zero_add, Nat.cast_one]
  symm
  apply NativeBridge.complexValue_spec
  have h1 : M.mem (M.number 1) (matrixIndexValue (number 1)) :=
    by simpa only [Nat.cast_one] using (matrixIndexNaturalNumber (M := M) 1 1 (by omega) (by omega))
  exact F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h1 h1)
theorem matrixDeterminantTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixDeterminantValue a (number 2) =
      M.subValue (M.mulValue (matrixEntryValue a 1 1) (matrixEntryValue a 2 2))
        (M.mulValue (matrixEntryValue a 1 2) (matrixEntryValue a 2 1)) := by
  have h1 : M.mem (M.number 1) (matrixIndexValue (number 2)) :=
    by simpa only [Nat.cast_one, Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 1 (by omega) (by omega))
  have h2 : M.mem (M.number 2) (matrixIndexValue (number 2)) :=
    by simpa only [Nat.cast_one, Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 2 (by omega) (by omega))
  have h11 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h1 h1))
  have h12 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h1 h2))
  have h21 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h2 h1))
  have h22 := NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha (matrixDomain_pair _ _ _ _ h2 h2))
  have h := matrixDeterminantValue_number a 2
  simp only [Nat.cast_ofNat] at h
  rw [h, Matrix.det_fin_two]
  change M.number (NativeBridge.complexValue (matrixEntryValue a 1 1) * NativeBridge.complexValue (matrixEntryValue a 2 2) -
    NativeBridge.complexValue (matrixEntryValue a 1 2) * NativeBridge.complexValue (matrixEntryValue a 2 1)) = _
  simp only [matrixEntryValue, Nat.cast_one, Nat.cast_ofNat] at ⊢
  exact (M.sub_numbers _ _).symm.trans (congrArg₂ M.subValue
    ((M.mul_numbers _ _).symm.trans (congrArg₂ M.mulValue h11.symm h22.symm))
    ((M.mul_numbers _ _).symm.trans (congrArg₂ M.mulValue h12.symm h21.symm)))
end Litex

namespace Litex
noncomputable def matrixPowerValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) : ℕ → M.Value
  | 0 => F.graphValue (matrixDomain n n) (M.standard .real) matrixIdentityBody
  | k + 1 => F.graphValue (matrixDomain n n) (M.standard .complex)
      (matrixMultiplyBody (matrixPowerValue a n k) a n)

theorem matrixPowerValue_inFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β) (k : ℕ) :
    M.mem (matrixPowerValue a n k) (F.fnSetValue (matrixDomain n n) (M.standard .complex)) := by
  cases k with
  | zero =>
    exact F.fnSet_of_returns
      (F.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _))
      (fun q hq => M.real_subset_complex _ (F.call_mem _ _ _ _
        (F.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _)) hq))
  | succ k => exact F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

theorem matrixPowerValue_inRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (a : M.Value) (n : Obj (M := M) β)
    (hn : In n N)
    (ha : M.mem a (F.fnSetValue (matrixDomain n n) (M.standard .real))) (k : ℕ) :
    M.mem (matrixPowerValue a n k) (F.fnSetValue (matrixDomain n n) (M.standard .real)) := by
  induction k with
  | zero => exact F.graph_inFnSet _ _ _ (fun _ _ => matrixIdentityEntry_inReal _ _)
  | succ k ih =>
    let prev := semanticObject (matrixPowerValue a n k) (M.member_isSet ih)
    let input := semanticObject a (M.member_isSet ha)
    have hprev : In prev (fnSet (matrixEntrywiseSignature n n .real)) := ih
    have hinput : In input (fnSet (matrixEntrywiseSignature n n .real)) := ha
    exact matrixMultiplyInRealFnSet
      (matrixMultiply prev input n n n hn hn hn
        (functionRealToComplex hprev) (functionRealToComplex hinput)) hprev hinput

structure MatrixPowerObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β
  exponent : Obj (M := M) γ

noncomputable instance matrixPowerRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixPowerObj (M := M) α β γ) where
  wd p := In p.order N ∧ In p.exponent N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := matrixPowerValue (denote p.matrix) p.order (NativeBridge.naturalValue (denote p.exponent))
  wd_isSet _ := M.member_isSet (matrixPowerValue_inFnSet _ _ _)

noncomputable def matrixPower {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (k : Obj (M := M) γ)
    (hn : In n N) (hk : In k N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixPowerObj (M := M) α β γ) := ⟨⟨a,n,k⟩,hn,hk,ha⟩

theorem matrixPowerInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixPowerObj (M := M) α β γ)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  matrixPowerValue_inFnSet _ _ _

theorem matrixPowerInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixPowerObj (M := M) α β γ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) :=
  matrixPowerValue_inRealFnSet _ _ p.wd.1 ha _

theorem matrixPowerZero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) :
    matrixPowerValue (denote a) n (NativeBridge.naturalValue (M.number 0)) =
      F.graphValue (matrixDomain n n) (M.standard .real) matrixIdentityBody := by
  have h := NativeBridge.naturalValue_number (M := M) 0
  simp only [Nat.cast_zero] at h
  rw [h]
  rfl

theorem matrixPowerSuccessor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (k : Obj (M := M) γ) (hk : In k N) :
    matrixPowerValue (denote a) n (NativeBridge.naturalValue (M.addValue (denote k) (M.number 1))) =
      F.graphValue (matrixDomain n n) (M.standard .complex)
        (matrixMultiplyBody (matrixPowerValue (denote a) n (NativeBridge.naturalValue (denote k))) (denote a) n) := by
  have h : NativeBridge.naturalValue (M.addValue (denote k) (M.number 1)) =
      NativeBridge.naturalValue (denote k) + 1 := by
    conv_lhs => rw [NativeBridge.naturalValue_spec (denote k) hk, M.add_numbers]
    have hn := NativeBridge.naturalValue_number (M := M) (NativeBridge.naturalValue (denote k) + 1)
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  rw [h]
  rfl
end Litex

namespace Litex
theorem matrixMinorIndexFloor (n r k : ℤ) (hn : 0 < n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hk : 1 ≤ k) (hkn : k < n) :
    (k : ℝ) + (⌊((k : ℝ) + n - r) / n⌋ : ℤ) =
      ((if k < r then k else k + 1 : ℤ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrnR : (r : ℝ) ≤ n := by exact_mod_cast hrn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  by_cases hkr : k < r
  · have hkrR : (k : ℝ) < r := by exact_mod_cast hkr
    have hf : ⌊((k : ℝ) + n - r) / n⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num only [Int.cast_zero]
        apply div_nonneg _ (le_of_lt hnR)
        linarith
      · rw [div_lt_iff₀ hnR]
        norm_num
        linarith
    simp only [if_pos hkr, hf, Int.cast_zero, add_zero]
  · have hkrR : (r : ℝ) ≤ k := by exact_mod_cast (le_of_not_gt hkr)
    have hf : ⌊((k : ℝ) + n - r) / n⌋ = (1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · rw [le_div_iff₀ hnR]
        norm_num
        linarith
      · rw [div_lt_iff₀ hnR]
        norm_num
        linarith
    simp only [if_neg hkr, hf, Int.cast_add, Int.cast_one]
theorem matrixMinorIndexBounds (n r k : ℤ) (hk : 1 ≤ k) (hkn : k < n) :
    let shifted := if k < r then k else k + 1
    1 ≤ shifted ∧ shifted ≤ n ∧ shifted ≠ r := by
  dsimp only
  split_ifs <;> omega
end Litex

namespace Litex
/-- The existing integer interval predicate, expressed directly on denotations. -/
def closedRangeValue {M : Semantics.{u}} [S : SetSemantics M]
    (a b : M.Value) : M.Value :=
  S.sepValue (M.standard .integer) (fun value =>
    ∃ lower upper k : ℤ, a = M.number (lower : ℂ) ∧ b = M.number (upper : ℂ) ∧
      value = M.number (k : ℂ) ∧ lower ≤ k ∧ k ≤ upper)

theorem closedRangeValue_members {M : Semantics.{u}} [S : SetSemantics M]
    (lower upper : ℤ) (x : M.Value) :
    M.mem x (closedRangeValue (M.number (lower : ℂ)) (M.number (upper : ℂ))) ↔
      ∃ k : ℤ, x = M.number (k : ℂ) ∧ lower ≤ k ∧ k ≤ upper := by
  rw [closedRangeValue, S.sep_members]
  constructor
  · rintro ⟨_, l, u, k, hl, hu, hx, hlo, hhi⟩
    have hle : lower = l := by exact_mod_cast M.number_injective hl
    have hue : upper = u := by exact_mod_cast M.number_injective hu
    subst l u
    exact ⟨k,hx,hlo,hhi⟩
  · rintro ⟨k,hx,hlo,hhi⟩
    exact ⟨(M.integer_members _).mpr ⟨k,hx⟩,lower,upper,k,rfl,rfl,hx,hlo,hhi⟩

noncomputable def matrixMinorShift {M : Semantics.{u}} (n deleted k : M.Value) : M.Value :=
  M.addValue k (roundingValue false (M.divValue (M.subValue (M.addValue k n) deleted) n))

theorem matrixMinorShift_numbers {M : Semantics.{u}} (n r k : ℤ) (hn : 0 < n)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hk : 1 ≤ k) (hkn : k < n) :
    matrixMinorShift (M.number (n : ℂ)) (M.number (r : ℂ)) (M.number (k : ℂ)) =
      M.number ((if k < r then k else k + 1 : ℤ) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  unfold matrixMinorShift
  rw [M.add_numbers, M.sub_numbers, M.div_numbers _ _ hnC]
  have hrnd := roundingValue_number (M := M) false (((k : ℝ) + n - r) / n)
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_intCast] at hrnd
  rw [hrnd, M.add_numbers]
  apply congrArg M.number
  have h := congrArg (fun z : ℝ => (z : ℂ)) (matrixMinorIndexFloor n r k hn hr hrn hk hkn)
  simpa only [Complex.ofReal_add, Complex.ofReal_intCast] using h

noncomputable def matrixMinorIndexValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : M.Value :=
  closedRangeValue (M.number 1) (M.subValue (denote n) (M.number 1))

theorem matrixMinorShift_mem {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n NPos)
    (r k : M.Value) (hr : M.mem r (matrixIndexValue n))
    (hk : M.mem k (matrixMinorIndexValue n)) :
    M.mem (matrixMinorShift (denote n) r k) (matrixIndexValue n) := by
  obtain ⟨nz, hnz, hnpos⟩ := integerWitnessOfNPos n hn
  change M.mem r (closedRangeValue (M.number 1) (denote n)) at hr
  change M.mem k (closedRangeValue (M.number 1) (M.subValue (denote n) (M.number 1))) at hk
  change M.mem _ (closedRangeValue (M.number 1) (denote n))
  rw [hnz] at hr hk ⊢
  rw [M.sub_numbers] at hk
  have hR := closedRangeValue_members (M := M) 1 nz r
  have hK := closedRangeValue_members (M := M) 1 (nz - 1) k
  simp only [Int.cast_one] at hR
  simp only [Int.cast_sub, Int.cast_one] at hK
  obtain ⟨rz,hrz,hrlo,hrhi⟩ := hR.mp hr
  obtain ⟨kz,hkz,hklo,hkhi⟩ := hK.mp hk
  rw [hrz, hkz, matrixMinorShift_numbers nz rz kz hnpos hrlo hrhi hklo (by omega)]
  have hOut := closedRangeValue_members (M := M) 1 nz (M.number ((if kz < rz then kz else kz+1 : ℤ) : ℂ))
  simp only [Int.cast_one] at hOut
  have bounds := matrixMinorIndexBounds nz rz kz hklo (by omega)
  exact hOut.mpr ⟨_,rfl,bounds.1,bounds.2.1⟩
end Litex

namespace Litex
noncomputable def matrixMinorDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![matrixMinorIndexValue n, matrixMinorIndexValue n]) (fun _ => True)

theorem matrixMinorDomain_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) : M.isSet (matrixMinorDomain n) :=
  F.sep_isSet _ _ (FiniteFunction.cart_isSet _ (by
    intro i; fin_cases i <;> exact F.sep_isSet _ _ (M.standard_isSet .integer)))

noncomputable def matrixMinorSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (scalar : StandardSetValue) : FunctionSignature M :=
  ⟨matrixMinorDomain n, matrixMinorDomain_isSet n, M.standard scalar, M.standard_isSet scalar⟩

noncomputable def matrixMinorBody {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n r c q : M.Value) : M.Value :=
  F.callValue a (FiniteFunction.pack2
    (matrixMinorShift n r (FiniteFunction.unpack2 q).1)
    (matrixMinorShift n c (FiniteFunction.unpack2 q).2))

theorem matrixMinorBody_mem {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n NPos)
    (a r c : M.Value) (hr : M.mem r (matrixIndexValue n)) (hc : M.mem c (matrixIndexValue n))
    (scalar : StandardSetValue) (ha : M.mem a (F.fnSetValue (matrixDomain n n) (M.standard scalar)))
    (q : M.Value) (hq : M.mem q (matrixMinorDomain n)) :
    M.mem (matrixMinorBody a (denote n) r c q) (M.standard scalar) := by
  obtain ⟨x,hx,y,hy,rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp ((F.sep_members _ _ _).mp hq).1
  unfold matrixMinorBody
  rw [FiniteFunction.unpack_pack2]
  exact F.call_mem _ _ _ _ ha (matrixDomain_pair n n _ _
    (matrixMinorShift_mem n hn r x hr hx) (matrixMinorShift_mem n hn c y hc hy))

structure MatrixMinorObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type t)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β
  row : Obj (M := M) γ
  col : Obj (M := M) δ

noncomputable instance matrixMinorRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixMinorObj (M := M) α β γ δ) where
  wd p := In p.order NPos ∧ M.mem (denote p.row) (matrixIndexValue p.order) ∧
    M.mem (denote p.col) (matrixIndexValue p.order) ∧ In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := F.graphValue (matrixMinorDomain p.order) (M.standard .complex)
    (matrixMinorBody (denote p.matrix) (denote p.order) (denote p.row) (denote p.col))
  wd_isSet {p} h := M.member_isSet (F.graph_inFnSet _ _ _
    (matrixMinorBody_mem p.order h.1 _ _ _ h.2.1 h.2.2.1 .complex h.2.2.2.2))

noncomputable def matrixMinor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (r : Obj (M := M) γ) (c : Obj (M := M) δ)
    (hp : In n NPos) (hr : M.mem (denote r) (matrixIndexValue n)) (hc : M.mem (denote c) (matrixIndexValue n))
    (hn : In n N) (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixMinorObj (M := M) α β γ δ) := ⟨⟨a,n,r,c⟩,hp,hr,hc,hn,ha⟩

theorem matrixMinorInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ)) :
    In p (fnSet (matrixMinorSignature p.val.order .complex)) :=
  F.graph_inFnSet _ _ _ (matrixMinorBody_mem p.val.order p.wd.1 _ _ _ p.wd.2.1 p.wd.2.2.1 .complex p.wd.2.2.2.2)

theorem matrixMinorCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ)) (q : M.Value) (hq : M.mem q (matrixMinorDomain p.val.order)) :
    F.callValue (denote p) q = matrixMinorBody (denote p.val.matrix) (denote p.val.order) (denote p.val.row) (denote p.val.col) q :=
  F.call_graphValue _ _ _ (matrixMinorBody_mem p.val.order p.wd.1 _ _ _ p.wd.2.1 p.wd.2.2.1 .complex p.wd.2.2.2.2) q hq

theorem matrixMinorInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixMinorSignature p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixMinorInFnSet p)
  intro q hq
  rw [matrixMinorCall p q hq]
  exact matrixMinorBody_mem p.val.order p.wd.1 _ _ _ p.wd.2.1 p.wd.2.2.1 .real ha q hq

theorem matrixMinor_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixMinorDomain p.val.order)
    (hb : g.val.bodyValue = matrixMinorBody (denote p.val.matrix) (denote p.val.order) (denote p.val.row) (denote p.val.col)) : Same p g := by
  apply functionExtOnDomain p g (matrixMinorSignature p.val.order .complex) g.val.signature
    (matrixMinorInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixMinorCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hb q)).symm
end Litex

namespace Litex

theorem matrixPredecessorNatural {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α) (hn : In n NPos) :
    M.mem (M.subValue (denote n) (M.number 1)) (M.standard .natural) := by
  obtain ⟨z,hz,hpos⟩ := integerWitnessOfNPos n hn
  rw [hz, M.sub_numbers]
  apply (M.natural_members _).mpr
  refine ⟨(z-1).toNat, congrArg M.number ?_⟩
  have h : ((z-1).toNat : ℤ) = z-1 := Int.toNat_of_nonneg (by omega)
  exact_mod_cast h.symm

noncomputable def matrixCofactorRawValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n r c : M.Value) : M.Value :=
  let indices := closedRangeValue (M.number 1) (M.subValue n (M.number 1))
  let domain := F.sepValue (FiniteFunction.cartValue ![indices, indices]) (fun _ => True)
  let minor := F.graphValue domain (M.standard .complex) (matrixMinorBody a n r c)
  let size := NativeBridge.naturalValue (M.subValue n (M.number 1))
  M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue r c) * (matrixComplexOn minor size size).det)


noncomputable def matrixCofactorValue {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α) (r c : M.Value) : M.Value :=
  matrixCofactorRawValue a (denote n) r c

structure MatrixCofactorObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x) (δ : Type t)
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    extends MatrixMinorObj (M := M) α β γ δ

noncomputable instance matrixCofactorRepresentation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ] :
    Representation M (MatrixCofactorObj (M := M) α β γ δ) where
  wd p := WD (M := M) p.toMatrixMinorObj
  denote p := matrixCofactorValue (denote p.matrix) p.order (denote p.row) (denote p.col)
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixCofactor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (r : Obj (M := M) γ) (c : Obj (M := M) δ)
    (hp : In n NPos) (hr : M.mem (denote r) (matrixIndexValue n)) (hc : M.mem (denote c) (matrixIndexValue n))
    (hn : In n N) (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixCofactorObj (M := M) α β γ δ) := ⟨⟨⟨a,n,r,c⟩⟩,hp,hr,hc,hn,ha⟩

theorem matrixCofactorInC {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixCofactorObj (M := M) α β γ δ)) : In p C :=
  (M.complex_members _).mpr ⟨_,rfl⟩

theorem matrixCofactorInR {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MatrixCofactorObj (M := M) α β γ δ))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) : In p R := by
  let minor : Obj (M := M) (MatrixMinorObj (M := M) α β γ δ) := ⟨p.val.toMatrixMinorObj,p.wd⟩
  have hn := matrixPredecessorNatural p.val.order p.wd.1
  let dim := semanticObject (M.subValue (denote p.val.order) (M.number 1)) (M.member_isSet hn)
  let det := matrixDeterminant minor dim hn (matrixMinorInFnSet minor)
  obtain ⟨value,hvalue⟩ := (M.real_members _).mp (matrixDeterminantInR det (matrixMinorInRealFnSet minor ha))
  have hdet : (matrixComplexOn (denote minor) (NativeBridge.naturalValue (denote dim)) (NativeBridge.naturalValue (denote dim))).det = (value : ℂ) := M.number_injective hvalue
  apply (M.real_members _).mpr
  refine ⟨(-1 : ℝ) ^ NativeBridge.naturalValue (M.addValue (denote p.val.row) (denote p.val.col)) * value, ?_⟩
  have h := congrArg (fun z : ℂ => M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue (denote p.val.row) (denote p.val.col)) * z)) hdet
  exact h.trans (by congr 1; push_cast; rfl)

theorem matrixCofactorOne {M : Semantics.{u}} [FunctionSemantics M] (a : M.Value) :
    matrixCofactorValue a (number 1) (M.number 1) (M.number 1) = M.number 1 := by
  unfold matrixCofactorValue matrixCofactorRawValue
  change M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue (M.number 1) (M.number 1)) *
    (matrixComplexOn _ (NativeBridge.naturalValue (M.subValue (M.number 1) (M.number 1))) _).det) = _
  rw [M.add_numbers, M.sub_numbers]
  simp only [one_add_one_eq_two]
  have h0 : NativeBridge.naturalValue (M.number ((1 : ℂ) - 1)) = 0 := by
    simpa only [sub_self, Nat.cast_zero] using (NativeBridge.naturalValue_number (M := M) 0)
  have h2 := NativeBridge.naturalValue_number (M := M) 2
  norm_num only [Nat.cast_ofNat] at h2
  rw [h0,h2,Matrix.det_fin_zero]
  norm_num

theorem matrixEntryValue_spec {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (n r c : ℕ)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number (n : ℂ)) (number (n : ℂ))) (M.standard .complex)))
    (hr : 1 ≤ r) (hrn : r ≤ n) (hc : 1 ≤ c) (hcn : c ≤ n) :
    matrixEntryValue a r c = M.number (NativeBridge.complexValue (matrixEntryValue a r c)) :=
  NativeBridge.complexValue_spec _ (F.call_mem _ _ _ _ ha
    (matrixDomain_pair _ _ _ _ (matrixIndexNaturalNumber n r hr hrn) (matrixIndexNaturalNumber n c hc hcn)))

theorem matrixCofactorTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r c : ℕ) (hr : r=1 ∨ r=2) (hc : c=1 ∨ c=2)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number (r : ℂ)) (M.number (c : ℂ)) =
      M.number ((-1 : ℂ) ^ (r+c) * NativeBridge.complexValue (matrixEntryValue a (3-r) (3-c))) := by
  have hsize : NativeBridge.naturalValue (M.subValue (M.number 2) (M.number 1)) = 1 := by
    rw [M.sub_numbers]
    rw [show (2 : ℂ) - 1 = 1 by norm_num]
    simpa only [Nat.cast_one] using (NativeBridge.naturalValue_number (M := M) 1)
  have hsum : NativeBridge.naturalValue (M.addValue (M.number (r : ℂ)) (M.number (c : ℂ))) = r+c := by
    rw [M.add_numbers, ← Nat.cast_add, NativeBridge.naturalValue_number]
  unfold matrixCofactorValue matrixCofactorRawValue
  change M.number ((-1 : ℂ) ^ NativeBridge.naturalValue (M.addValue (M.number (r : ℂ)) (M.number (c : ℂ))) *
    (matrixComplexOn _ (NativeBridge.naturalValue (M.subValue (M.number 2) (M.number 1))) _).det) = _
  rw [hsum,hsize,Matrix.det_fin_one]
  simp only [matrixComplexOn, FiniteFunction.index, Fin.val_zero, zero_add, Nat.cast_one]
  apply congrArg M.number
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (r+c) * z)
  apply congrArg (NativeBridge.complexValue (M := M))
  have hp := numberInNPosOfEq (M := M) 2 2 (by norm_num) (by omega)
  have hri : M.mem (M.number (r : ℂ)) (matrixIndexValue (number 2)) := by
    simpa only [Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 r (by omega) (by omega))
  have hci : M.mem (M.number (c : ℂ)) (matrixIndexValue (number 2)) := by
    simpa only [Nat.cast_ofNat] using (matrixIndexNaturalNumber (M := M) 2 c (by omega) (by omega))
  have hdim : matrixMinorIndexValue (number (M := M) 2) = matrixIndexValue (number 1) := by
    change closedRangeValue (M.number 1) (M.subValue (M.number 2) (M.number 1)) = closedRangeValue (M.number 1) (M.number 1)
    rw [M.sub_numbers]
    norm_num
  have hi : M.mem (M.number 1) (matrixIndexValue (number 1)) := by
    simpa only [Nat.cast_one] using (matrixIndexNaturalNumber (M := M) 1 1 (by omega) (by omega))
  have hq : M.mem (FiniteFunction.pack2 (M.number 1) (M.number 1)) (matrixMinorDomain (number 2)) := by
    unfold matrixMinorDomain
    rw [hdim]
    exact matrixDomain_pair _ _ _ _ hi hi
  change F.callValue (F.graphValue (matrixMinorDomain (number 2)) (M.standard .complex)
    (matrixMinorBody a (denote (number 2)) (M.number (r : ℂ)) (M.number (c : ℂ))))
    (FiniteFunction.pack2 (M.number 1) (M.number 1)) = matrixEntryValue a (3-r) (3-c)
  rw [F.call_graphValue _ _ _ (matrixMinorBody_mem (number 2) hp a _ _ hri hci .complex ha) _ hq]
  unfold matrixMinorBody
  rw [FiniteFunction.unpack_pack2]
  have hs : ∀ k : ℕ, k=1 ∨ k=2 →
      matrixMinorShift (M.number 2) (M.number (k : ℂ)) (M.number 1) = M.number ((3-k : ℕ) : ℂ) := by
    intro k hk
    rcases hk with rfl | rfl
    · have h := matrixMinorShift_numbers (M := M) 2 1 1 (by omega) (by omega) (by omega) (by omega) (by omega)
      norm_num at h ⊢
      exact h
    · have h := matrixMinorShift_numbers (M := M) 2 2 1 (by omega) (by omega) (by omega) (by omega) (by omega)
      norm_num at h ⊢
      exact h
  change F.callValue a (FiniteFunction.pack2 (matrixMinorShift (M.number 2) (M.number (r : ℂ)) (M.number 1)) (matrixMinorShift (M.number 2) (M.number (c : ℂ)) (M.number 1))) = _
  rw [hs r hr,hs c hc]
  rfl

theorem matrixCofactorTwo11 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 1) (M.number 1) = matrixEntryValue a 2 2 := by
  have h := matrixCofactorTwo a 1 1 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 2 2 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans he.symm

theorem matrixCofactorTwo12 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 1) (M.number 2) = M.negValue (matrixEntryValue a 2 1) := by
  have h := matrixCofactorTwo a 1 2 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 2 1 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans ((congrArg M.negValue he).trans (M.neg_numbers _)).symm

theorem matrixCofactorTwo21 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 2) (M.number 1) = M.negValue (matrixEntryValue a 1 2) := by
  have h := matrixCofactorTwo a 2 1 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 1 2 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans ((congrArg M.negValue he).trans (M.neg_numbers _)).symm

theorem matrixCofactorTwo22 {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value)
    (ha : M.mem a (F.fnSetValue (matrixDomain (number 2) (number 2)) (M.standard .complex))) :
    matrixCofactorValue a (number 2) (M.number 2) (M.number 2) = matrixEntryValue a 1 1 := by
  have h := matrixCofactorTwo a 2 2 (by decide) (by decide) ha
  have he := matrixEntryValue_spec a 2 1 1 ha (by omega) (by omega) (by omega) (by omega)
  norm_num at h
  exact h.trans he.symm
end Litex

namespace Litex
theorem matrixIndexPositiveOrder {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (n : Obj (M := M) α)
    (r : M.Value) (hr : M.mem r (matrixIndexValue n)) : In n NPos := by
  obtain ⟨_, lower, upper, k, hl, hu, _, hlo, hhi⟩ := (F.sep_members _ _ _).mp hr
  change M.number 1 = M.number (lower : ℂ) at hl
  have hlower : lower = 1 := by
    have h := M.number_injective hl
    exact_mod_cast h.symm
  exact integerPositiveOfWitness n upper hu (by omega)

noncomputable def matrixAdjugateBody {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (q : M.Value) : M.Value :=
  matrixCofactorValue a n (FiniteFunction.unpack2 q).2 (FiniteFunction.unpack2 q).1

structure MatrixAdjugateObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β

noncomputable instance matrixAdjugateRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixAdjugateObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex))
  denote p := F.graphValue (matrixDomain p.order p.order) (M.standard .complex)
    (matrixAdjugateBody (denote p.matrix) p.order)
  wd_isSet {_} _ := M.member_isSet (F.graph_inFnSet _ _ _
    (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩))

noncomputable def matrixAdjugate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex))) :
    Obj (M := M) (MatrixAdjugateObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha⟩

theorem matrixAdjugateInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  F.graph_inFnSet _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩)

theorem matrixAdjugateCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixAdjugateBody (denote p.val.matrix) p.val.order q :=
  F.call_graphValue _ _ _ (fun _ _ => (M.complex_members _).mpr ⟨_,rfl⟩) q hq

theorem matrixAdjugateInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixAdjugateInFnSet p)
  intro q hq
  rw [matrixAdjugateCall p q hq]
  have hr := ((F.sep_members _ _ _).mp (matrixDomain_first p.val.order p.val.order q hq)).1
  have hc := ((F.sep_members _ _ _).mp (matrixDomain_second p.val.order p.val.order q hq)).1
  let r := semanticObject (FiniteFunction.unpack2 q).1 (M.member_isSet hr)
  let c := semanticObject (FiniteFunction.unpack2 q).2 (M.member_isSet hc)
  let cofactor := matrixCofactor p.val.matrix p.val.order c r
    (matrixIndexPositiveOrder p.val.order _ hr) hc hr p.wd.1 p.wd.2
  exact matrixCofactorInR cofactor ha

theorem matrixAdjugate_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixAdjugateObj (M := M) α β)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.order p.val.order)
    (hb : g.val.bodyValue = matrixAdjugateBody (denote p.val.matrix) p.val.order) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.order p.val.order .complex) g.val.signature
    (matrixAdjugateInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixAdjugateCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hb q)).symm
end Litex

namespace Litex

noncomputable def matrixInverseBody {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (q : M.Value) : M.Value :=
  M.divValue (matrixAdjugateBody a n q) (matrixDeterminantValue a n)

theorem matrixInverseBody_closed {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : M.Value) (n : Obj (M := M) α)
    (hd : matrixDeterminantValue a n ≠ M.number 0) (q : M.Value) :
    M.mem (matrixInverseBody a n q) (M.standard .complex) :=
  M.div_closed ((M.complex_members _).mpr ⟨_,rfl⟩)
    ((M.complex_members _).mpr ⟨_,rfl⟩) hd

structure MatrixInverseObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  matrix : Obj (M := M) α
  order : Obj (M := M) β

noncomputable instance matrixInverseRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MatrixInverseObj (M := M) α β) where
  wd p := In p.order N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.order p.order) (M.standard .complex)) ∧
    matrixDeterminantValue (denote p.matrix) p.order ≠ M.number 0
  denote p := F.graphValue (matrixDomain p.order p.order) (M.standard .complex)
    (matrixInverseBody (denote p.matrix) p.order)
  wd_isSet {p} h := M.member_isSet (F.graph_inFnSet _ _ _
    (fun q _ => matrixInverseBody_closed _ p.order h.2.2 q))

noncomputable def matrixInverse {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    Obj (M := M) (MatrixInverseObj (M := M) α β) := ⟨⟨a,n⟩,hn,ha,hd⟩

theorem matrixInverseInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β)) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .complex)) :=
  F.graph_inFnSet _ _ _ (fun q _ => matrixInverseBody_closed _ p.val.order p.wd.2.2 q)

theorem matrixInverseCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β)) (q : M.Value)
    (hq : M.mem q (matrixDomain p.val.order p.val.order)) :
    F.callValue (denote p) q = matrixInverseBody (denote p.val.matrix) p.val.order q :=
  F.call_graphValue _ _ _ (fun q _ => matrixInverseBody_closed _ p.val.order p.wd.2.2 q) q hq

theorem matrixInverseInRealFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β))
    (ha : M.mem (denote p.val.matrix) (F.fnSetValue (matrixDomain p.val.order p.val.order) (M.standard .real))) :
    In p (fnSet (matrixEntrywiseSignature p.val.order p.val.order .real)) := by
  apply F.fnSet_of_returns (matrixInverseInFnSet p)
  intro q hq
  rw [matrixInverseCall p q hq]
  let adj := matrixAdjugate p.val.matrix p.val.order p.wd.1 p.wd.2.1
  have haR := F.call_mem _ _ _ q (matrixAdjugateInRealFnSet adj ha) hq
  rw [matrixAdjugateCall adj q hq] at haR
  let det := matrixDeterminant p.val.matrix p.val.order p.wd.1 p.wd.2.1
  let numerator := semanticObject (matrixAdjugateBody (denote p.val.matrix) p.val.order q) (M.member_isSet haR)
  exact divInR numerator det haR (matrixDeterminantInR det ha) p.wd.2.2

theorem matrixInverse_eq_formula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MatrixInverseObj (M := M) α β)) (g : Obj (M := M) (FormulaFn M))
    (hD : g.val.signature.domain = matrixDomain p.val.order p.val.order)
    (hb : g.val.bodyValue = matrixInverseBody (denote p.val.matrix) p.val.order) : Same p g := by
  apply functionExtOnDomain p g
    (matrixEntrywiseSignature p.val.order p.val.order .complex) g.val.signature
    (matrixInverseInFnSet p) (formulaFnInFnSet g) hD.symm
  intro q hq
  rw [matrixInverseCall p q hq]
  have hg := F.call_graphValue _ _ _ g.wd q (hD.symm ▸ hq)
  change F.callValue (denote g) q = g.val.bodyValue q at hg
  exact (hg.trans (congrFun hb q)).symm
end Litex

namespace Litex

noncomputable def matrixRankValue {M : Semantics.{u}} [FunctionSemantics M]
    (a m n : M.Value) : M.Value :=
  M.number ((matrixComplexOn a (NativeBridge.naturalValue m)
    (NativeBridge.naturalValue n)).rank : ℂ)

structure MatrixRankObj {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  matrix : Obj (M := M) α
  rows : Obj (M := M) β
  cols : Obj (M := M) γ

noncomputable instance matrixRankRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (MatrixRankObj (M := M) α β γ) where
  wd p := In p.rows N ∧ In p.cols N ∧
    M.mem (denote p.matrix) (F.fnSetValue (matrixDomain p.rows p.cols) (M.standard .complex))
  denote p := matrixRankValue (denote p.matrix) (denote p.rows) (denote p.cols)
  wd_isSet _ := M.member_isSet ((M.natural_members _).mpr ⟨_,rfl⟩)

noncomputable def matrixRank {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (hm : In m N) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain m n) (M.standard .complex))) :
    Obj (M := M) (MatrixRankObj (M := M) α β γ) := ⟨⟨a,m,n⟩,hm,hn,ha⟩

theorem matrixRankInN {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixRankObj (M := M) α β γ)) : In p N :=
  (M.natural_members _).mpr ⟨_,rfl⟩

theorem matrixRankLeRows {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixRankObj (M := M) α β γ)) : Le p p.val.rows := by
  let a := matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols
  refine NativeBridge.leOfDenoteReal p p.val.rows (a.rank : ℝ)
    (NativeBridge.naturalValue (denote p.val.rows) : ℝ) ?_ ?_ ?_
  · change M.number (a.rank : ℂ) = _
    simp only [Complex.ofReal_natCast]
  · simpa only [Complex.ofReal_natCast] using NativeBridge.naturalValue_spec (denote p.val.rows) p.wd.1
  · exact_mod_cast Matrix.rank_le_height a

theorem matrixRankLeCols {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MatrixRankObj (M := M) α β γ)) : Le p p.val.cols := by
  let a := matrixComplexValue (denote p.val.matrix) p.val.rows p.val.cols
  refine NativeBridge.leOfDenoteReal p p.val.cols (a.rank : ℝ)
    (NativeBridge.naturalValue (denote p.val.cols) : ℝ) ?_ ?_ ?_
  · change M.number (a.rank : ℂ) = _
    simp only [Complex.ofReal_natCast]
  · simpa only [Complex.ofReal_natCast] using NativeBridge.naturalValue_spec (denote p.val.cols) p.wd.2.1
  · exact_mod_cast Matrix.rank_le_width a

theorem matrixComplexValue_zero {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N) :
    matrixComplexValue (denote (zeroMatrix m n hm hn)) m n = 0 := by
  ext i j
  unfold matrixComplexValue matrixComplexOn
  rw [zeroMatrixCall _ _ (matrixDomain_pair _ _ _ _ (matrixIndexOfFin m hm i) (matrixIndexOfFin n hn j))]
  exact NativeBridge.complexValue_number 0

theorem matrixRankZero {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (m : Obj (M := M) α) (n : Obj (M := M) β) (hm : In m N) (hn : In n N) :
    matrixRankValue (denote (zeroMatrix m n hm hn)) (denote m) (denote n) = M.number 0 := by
  change M.number ((matrixComplexValue (denote (zeroMatrix m n hm hn)) m n).rank : ℂ) = M.number 0
  rw [matrixComplexValue_zero m n hm hn, Matrix.rank_zero]
  simp only [Nat.cast_zero]

theorem matrixRankIdentity {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (n : Obj (M := M) α) (hn : In n N) :
    matrixRankValue (denote (identityMatrix n hn)) (denote n) (denote n) = denote n := by
  change M.number ((matrixComplexValue (denote (identityMatrix n hn)) n n).rank : ℂ) = denote n
  rw [matrixComplexValue_identity n hn, Matrix.rank_one, Fintype.card_fin]
  exact (NativeBridge.naturalValue_spec (denote n) hn).symm

end Litex


namespace Litex

/-- A bound quantifies over source members. Real carriers are checked separately
by the source predicate's WD, so the empty set needs no nonempty premise. -/
def RealUpperBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  ∀ x : M.Value, M.mem x A →
    ∃ r s : ℝ, x = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s

def RealLowerBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  ∀ x : M.Value, M.mem x A →
    ∃ r s : ℝ, b = M.number (r : ℂ) ∧ x = M.number (s : ℂ) ∧ r ≤ s

def RealUpperBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealUpperBoundValue M (denote A) (denote b)

def RealLowerBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealLowerBoundValue M (denote A) (denote b)

def RealBoundedAboveValue (M : Semantics.{u}) (A : M.Value) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealUpperBoundValue M A (denote b)

def RealBoundedAbove {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := RealBoundedAboveValue M (denote A)

def RealBoundedBelowValue (M : Semantics.{u}) (A : M.Value) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealLowerBoundValue M A (denote b)

def RealBoundedBelow {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := RealBoundedBelowValue M (denote A)

def RealBoundedValue (M : Semantics.{u}) (A : M.Value) : Prop :=
  RealBoundedBelowValue M A ∧ RealBoundedAboveValue M A

def RealBounded {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := RealBoundedValue M (denote A)

theorem realUpperBoundOfForall {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (h : ∀ {γ : Type u} [Representation M γ], (x : Obj (M := M) γ) → In x A → Le x b) :
    RealUpperBound A b := fun x hx => h (semanticObject x (M.member_isSet hx)) hx

theorem realLowerBoundOfForall {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (h : ∀ {γ : Type u} [Representation M γ], (x : Obj (M := M) γ) → In x A → Le b x) :
    RealLowerBound A b := fun x hx => h (semanticObject x (M.member_isSet hx)) hx

end Litex

namespace Litex

/-- The ordinary real set observed from the source membership relation. -/
def realMemberSet (M : Semantics.{u}) (A : M.Value) : Set ℝ :=
  {r | M.mem (M.number (r : ℂ)) A}

theorem realUpperBound_iff_upperBounds {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) :
    RealUpperBound A b ↔ NativeBridge.asReal b hb ∈ upperBounds (realMemberSet M (denote A)) := by
  constructor
  · intro h r hr
    exact (NativeBridge.le_iff_ofDenoteReal (number (M := M) (r : ℂ)) b r
      (NativeBridge.asReal b hb) rfl (NativeBridge.asReal_spec b hb)).mp
      (h (M.number (r : ℂ)) hr)
  · intro h x hx
    obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
    exact ⟨r, NativeBridge.asReal b hb, hr, NativeBridge.asReal_spec b hb,
      h (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩

theorem realLowerBound_iff_lowerBounds {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) :
    RealLowerBound A b ↔ NativeBridge.asReal b hb ∈ lowerBounds (realMemberSet M (denote A)) := by
  constructor
  · intro h r hr
    exact (NativeBridge.le_iff_ofDenoteReal b (number (M := M) (r : ℂ))
      (NativeBridge.asReal b hb) r (NativeBridge.asReal_spec b hb) rfl).mp
      (h (M.number (r : ℂ)) hr)
  · intro h x hx
    obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
    exact ⟨NativeBridge.asReal b hb, r, NativeBridge.asReal_spec b hb, hr,
      h (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩

theorem realBoundedAbove_iff_bddAbove {M : Semantics.{u}} {α : Type v}
    [Representation M α] (A : Obj (M := M) α) (hA : Subset A R) :
    RealBoundedAbove A ↔ BddAbove (realMemberSet M (denote A)) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨NativeBridge.asReal b hb, (realUpperBound_iff_upperBounds A b hA hb).mp h⟩
  · rintro ⟨b, hb⟩
    refine ⟨semanticObject (M.number (b : ℂ)) (isSet (number (M := M) (b : ℂ))), ?_, ?_⟩
    · exact (M.real_members _).mpr ⟨b, rfl⟩
    · intro x hx
      obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
      exact ⟨r,b,hr,rfl,hb (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩

theorem realBoundedBelow_iff_bddBelow {M : Semantics.{u}} {α : Type v}
    [Representation M α] (A : Obj (M := M) α) (hA : Subset A R) :
    RealBoundedBelow A ↔ BddBelow (realMemberSet M (denote A)) := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨NativeBridge.asReal b hb, (realLowerBound_iff_lowerBounds A b hA hb).mp h⟩
  · rintro ⟨b, hb⟩
    refine ⟨semanticObject (M.number (b : ℂ)) (isSet (number (M := M) (b : ℂ))), ?_, ?_⟩
    · exact (M.real_members _).mpr ⟨b, rfl⟩
    · intro x hx
      obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
      exact ⟨b,r,rfl,hr,hb (by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx)⟩
end Litex

namespace Litex

/-- Nonemptiness observed through membership; no universal source set is used. -/
theorem realMemberSet_nonempty {M : Semantics.{u}} {α : Type v}
    [Representation M α] (A : Obj (M := M) α)
    (hA : Subset A R) (hne : IsNonempty A) :
    (realMemberSet M (denote A)).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr⟩ := (M.real_members x).mp (hA x hx)
  exact ⟨r, by change M.mem (M.number (r : ℂ)) (denote A); rw [← hr]; exact hx⟩

/-- The reserved source certificate includes a nonempty real carrier. -/
def RealLeastUpperBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  (∀ x, M.mem x A → M.mem x (M.standard .real)) ∧
  (∃ x, M.mem x A) ∧ ∃ r : ℝ, b = M.number (r : ℂ) ∧ IsLUB (realMemberSet M A) r

def RealLeastUpperBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealLeastUpperBoundValue M (denote A) (denote b)

def RealSupremumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealLeastUpperBound A b

noncomputable def supremumValue {M : Semantics.{u}} (A : M.Value) : M.Value :=
  M.number ((sSup (realMemberSet M A) : ℝ) : ℂ)

structure SupremumObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance supremumRepresentation {M : Semantics.{u}}
    {α : Type v} [Representation M α] : Representation M (SupremumObj (M := M) α) where
  wd p := Subset p.set R ∧ RealSupremumExists p.set
  denote p := supremumValue (denote p.set)
  wd_isSet _ := M.member_isSet ((M.real_members _).mpr ⟨_,rfl⟩)

noncomputable def supremum {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (h : RealSupremumExists A) :
    Obj (M := M) (SupremumObj (M := M) α) := ⟨⟨A⟩,hA,h⟩

theorem supremumInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SupremumObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨_,rfl⟩

theorem realSupremumExistsOfCertificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealLeastUpperBound A b) :
    RealSupremumExists A := by
  refine ⟨semanticObject (denote b) (isSet b), ?_, h⟩
  obtain ⟨r,hr,_⟩ := h.2.2
  exact (M.real_members _).mpr ⟨r,hr⟩

theorem realSupremumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (hne : IsNonempty A)
    (hb : RealBoundedAbove A) : RealSupremumExists A := by
  let r := sSup (realMemberSet M (denote A))
  refine ⟨semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ))),
    (M.real_members _).mpr ⟨r,rfl⟩, hA, hne, r, rfl, ?_⟩
  exact isLUB_csSup (realMemberSet_nonempty A hA hne)
    ((realBoundedAbove_iff_bddAbove A hA).mp hb)

theorem supremumValue_eq_certificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealLeastUpperBound A b) :
    supremumValue (denote A) = denote b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  rw [supremumValue, he.csSup_eq (realMemberSet_nonempty A h.1 h.2.1)]
  exact hr.symm

theorem supremumSelected {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SupremumObj (M := M) α)) : RealLeastUpperBound p.val.set p := by
  obtain ⟨b,_,hb⟩ := p.wd.2
  change RealLeastUpperBoundValue M (denote p.val.set) (supremumValue (denote p.val.set))
  rw [supremumValue_eq_certificate p.val.set b hb]
  exact hb

/-- The reserved source certificate includes a nonempty real carrier. -/
def RealGreatestLowerBoundValue (M : Semantics.{u}) (A b : M.Value) : Prop :=
  (∀ x, M.mem x A → M.mem x (M.standard .real)) ∧
  (∃ x, M.mem x A) ∧ ∃ r : ℝ, b = M.number (r : ℂ) ∧ IsGLB (realMemberSet M A) r

def RealGreatestLowerBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) : Prop :=
  RealGreatestLowerBoundValue M (denote A) (denote b)

def RealInfimumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop :=
  ∃ b : Obj (M := M) M.Value, ∃ _ : In b R, RealGreatestLowerBound A b

noncomputable def infimumValue {M : Semantics.{u}} (A : M.Value) : M.Value :=
  M.number ((sInf (realMemberSet M A) : ℝ) : ℂ)

structure InfimumObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance infimumRepresentation {M : Semantics.{u}}
    {α : Type v} [Representation M α] : Representation M (InfimumObj (M := M) α) where
  wd p := Subset p.set R ∧ RealInfimumExists p.set
  denote p := infimumValue (denote p.set)
  wd_isSet _ := M.member_isSet ((M.real_members _).mpr ⟨_,rfl⟩)

noncomputable def infimum {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (h : RealInfimumExists A) :
    Obj (M := M) (InfimumObj (M := M) α) := ⟨⟨A⟩,hA,h⟩

theorem infimumInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (InfimumObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨_,rfl⟩

theorem realInfimumExistsOfCertificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealGreatestLowerBound A b) :
    RealInfimumExists A := by
  refine ⟨semanticObject (denote b) (isSet b), ?_, h⟩
  obtain ⟨r,hr,_⟩ := h.2.2
  exact (M.real_members _).mpr ⟨r,hr⟩

theorem realInfimumExists {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (hA : Subset A R) (hne : IsNonempty A)
    (hb : RealBoundedBelow A) : RealInfimumExists A := by
  let r := sInf (realMemberSet M (denote A))
  refine ⟨semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ))),
    (M.real_members _).mpr ⟨r,rfl⟩, hA, hne, r, rfl, ?_⟩
  exact isGLB_csInf (realMemberSet_nonempty A hA hne)
    ((realBoundedBelow_iff_bddBelow A hA).mp hb)

theorem infimumValue_eq_certificate {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (h : RealGreatestLowerBound A b) :
    infimumValue (denote A) = denote b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  rw [infimumValue, he.csInf_eq (realMemberSet_nonempty A h.1 h.2.1)]
  exact hr.symm

theorem infimumSelected {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (InfimumObj (M := M) α)) : RealGreatestLowerBound p.val.set p := by
  obtain ⟨b,_,hb⟩ := p.wd.2
  change RealGreatestLowerBoundValue M (denote p.val.set) (infimumValue (denote p.val.set))
  rw [infimumValue_eq_certificate p.val.set b hb]
  exact hb

end Litex

-- Explicit extremal-certificate releases, preserving their source premises.
namespace Litex

theorem realLeastUpperBoundFromDefinition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le z b))
    (hext : ∀ {γ : Type u} [Representation M γ], (c : Obj (M := M) γ) → In c R →
      RealUpperBound A c → Le b c) : RealLeastUpperBound A b := by
  refine ⟨hA, hne, NativeBridge.asReal b hb, NativeBridge.asReal_spec b hb, ?_, ?_⟩
  · exact (realUpperBound_iff_upperBounds A b hA hb).mp
      (realUpperBoundOfForall A b hbound)
  · intro r hr
    let c := semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ)))
    have hc : In c R := (M.real_members _).mpr ⟨r,rfl⟩
    have hcval : NativeBridge.asReal c hc = r := by
      have h := NativeBridge.asReal_spec c hc
      change M.number (r : ℂ) = M.number ((NativeBridge.asReal c hc : ℝ) : ℂ) at h
      have h' := M.number_injective h
      exact_mod_cast h'.symm
    have bound : RealUpperBound A c := (realUpperBound_iff_upperBounds A c hA hc).mpr (hcval.symm ▸ hr)
    have h := hext c hc bound
    exact (NativeBridge.le_iff_ofDenoteReal b c (NativeBridge.asReal b hb) r (NativeBridge.asReal_spec b hb) rfl).mp h

theorem realLeastUpperBoundUpperBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (_hb : In b R) (h : RealLeastUpperBound A b) : RealUpperBound A b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  intro z hz
  obtain ⟨s,hs⟩ := (M.real_members z).mp (hA z hz)
  exact ⟨s,r,hs,hr, he.1 (by change M.mem (M.number (s : ℂ)) (denote A); rw [← hs]; exact hz)⟩

theorem realLeastUpperBoundExists {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le z b)) : RealSupremumExists A :=
  realSupremumExists A hA hne
    ⟨semanticObject (denote b) (isSet b), hb, realUpperBoundOfForall A b hbound⟩

theorem realLeastUpperBoundUnique {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (_hA : Subset A R) (_hb : In b R) (hbcert : RealLeastUpperBound A b)
    (_hc : In c R) (hccert : RealLeastUpperBound A c) : Same b c :=
  (supremumValue_eq_certificate A b hbcert).symm.trans
    (supremumValue_eq_certificate A c hccert)

theorem realLeastUpperBoundMember {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (hb : In b R) (hcert : RealLeastUpperBound A b)
    (hc : In c A) : Le c b :=
  realLeastUpperBoundUpperBound A b hA hb hcert (denote c) hc

theorem realLeastUpperBoundCompareBound {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealLeastUpperBound A b)
    (hc : In c R) (hbound : (∀ {δ : Type u} [Representation M δ], (z : Obj (M := M) δ) → In z A → Le z c)) : Le b c := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have bound := (realUpperBound_iff_upperBounds A c hA hc).mp
    (realUpperBoundOfForall A c hbound)
  exact ⟨r,NativeBridge.asReal c hc,hr,NativeBridge.asReal_spec c hc,he.2 bound⟩

theorem realLeastUpperBoundCrosses {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealLeastUpperBound A b)
    (hc : In c R) (hlt : Lt c b) :
    ∃ z : Obj (M := M) M.Value, ∃ _ : In z A, Lt c z := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have cmp := (NativeBridge.lt_iff_ofDenoteReal c b (NativeBridge.asReal c hc) r (NativeBridge.asReal_spec c hc) hr).mp hlt
  have hne := realMemberSet_nonempty A hA hcert.2.1
  rw [← he.csSup_eq hne] at cmp
  obtain ⟨s,hs,hslt⟩ := exists_lt_of_lt_csSup hne cmp
  refine ⟨semanticObject (M.number (s : ℂ)) (isSet (number (M := M) (s : ℂ))), hs, ?_⟩
  exact ⟨NativeBridge.asReal c hc,s,NativeBridge.asReal_spec c hc,rfl,hslt⟩

theorem realGreatestLowerBoundFromDefinition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le b z))
    (hext : ∀ {γ : Type u} [Representation M γ], (c : Obj (M := M) γ) → In c R →
      RealLowerBound A c → Le c b) : RealGreatestLowerBound A b := by
  refine ⟨hA, hne, NativeBridge.asReal b hb, NativeBridge.asReal_spec b hb, ?_, ?_⟩
  · exact (realLowerBound_iff_lowerBounds A b hA hb).mp
      (realLowerBoundOfForall A b hbound)
  · intro r hr
    let c := semanticObject (M.number (r : ℂ)) (isSet (number (M := M) (r : ℂ)))
    have hc : In c R := (M.real_members _).mpr ⟨r,rfl⟩
    have hcval : NativeBridge.asReal c hc = r := by
      have h := NativeBridge.asReal_spec c hc
      change M.number (r : ℂ) = M.number ((NativeBridge.asReal c hc : ℝ) : ℂ) at h
      have h' := M.number_injective h
      exact_mod_cast h'.symm
    have bound : RealLowerBound A c := (realLowerBound_iff_lowerBounds A c hA hc).mpr (hcval.symm ▸ hr)
    have h := hext c hc bound
    exact (NativeBridge.le_iff_ofDenoteReal c b r (NativeBridge.asReal b hb) rfl (NativeBridge.asReal_spec b hb)).mp h

theorem realGreatestLowerBoundLowerBound {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (_hb : In b R) (h : RealGreatestLowerBound A b) : RealLowerBound A b := by
  obtain ⟨r,hr,he⟩ := h.2.2
  intro z hz
  obtain ⟨s,hs⟩ := (M.real_members z).mp (hA z hz)
  exact ⟨r,s,hr,hs, he.1 (by change M.mem (M.number (s : ℂ)) (denote A); rw [← hs]; exact hz)⟩

theorem realGreatestLowerBoundExists {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (b : Obj (M := M) β)
    (hA : Subset A R) (hb : In b R) (hne : IsNonempty A)
    (hbound : (∀ {γ : Type u} [Representation M γ], (z : Obj (M := M) γ) → In z A → Le b z)) : RealInfimumExists A :=
  realInfimumExists A hA hne
    ⟨semanticObject (denote b) (isSet b), hb, realLowerBoundOfForall A b hbound⟩

theorem realGreatestLowerBoundUnique {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (_hA : Subset A R) (_hb : In b R) (hbcert : RealGreatestLowerBound A b)
    (_hc : In c R) (hccert : RealGreatestLowerBound A c) : Same b c :=
  (infimumValue_eq_certificate A b hbcert).symm.trans
    (infimumValue_eq_certificate A c hccert)

theorem realGreatestLowerBoundMember {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (hb : In b R) (hcert : RealGreatestLowerBound A b)
    (hc : In c A) : Le b c :=
  realGreatestLowerBoundLowerBound A b hA hb hcert (denote c) hc

theorem realGreatestLowerBoundCompareBound {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealGreatestLowerBound A b)
    (hc : In c R) (hbound : (∀ {δ : Type u} [Representation M δ], (z : Obj (M := M) δ) → In z A → Le c z)) : Le c b := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have bound := (realLowerBound_iff_lowerBounds A c hA hc).mp
    (realLowerBoundOfForall A c hbound)
  exact ⟨NativeBridge.asReal c hc,r,NativeBridge.asReal_spec c hc,hr,he.2 bound⟩

theorem realGreatestLowerBoundCrosses {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hA : Subset A R) (_hb : In b R) (hcert : RealGreatestLowerBound A b)
    (hc : In c R) (hlt : Lt b c) :
    ∃ z : Obj (M := M) M.Value, ∃ _ : In z A, Lt z c := by
  obtain ⟨r,hr,he⟩ := hcert.2.2
  have cmp := (NativeBridge.lt_iff_ofDenoteReal b c r (NativeBridge.asReal c hc) hr (NativeBridge.asReal_spec c hc)).mp hlt
  have hne := realMemberSet_nonempty A hA hcert.2.1
  rw [← he.csInf_eq hne] at cmp
  obtain ⟨s,hs,hslt⟩ := exists_lt_of_csInf_lt hne cmp
  refine ⟨semanticObject (M.number (s : ℂ)) (isSet (number (M := M) (s : ℂ))), hs, ?_⟩
  exact ⟨s,NativeBridge.asReal c hc,rfl,NativeBridge.asReal_spec c hc,hslt⟩
end Litex

-- Sequence monotonicity and boundedness, retaining positive-natural indexing.
namespace Litex

def SequenceOrderValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (strict reverse : Bool) (a : M.Value) : Prop :=
  ∀ m, M.mem m (denote (NPos (M := M))) →
    ∀ n, M.mem n (denote (NPos (M := M))) →
      (∃ r s : ℝ, m = M.number (r : ℂ) ∧ n = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)) →
      ∃ r s : ℝ,
        F.callValue a (if reverse then n else m) = M.number (r : ℂ) ∧
        F.callValue a (if reverse then m else n) = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)

/-- Consume the source's universal proof at its own two host universe levels. -/
theorem sequenceOrderOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (strict reverse : Bool) (a : Obj (M := M) α)
    (h : ∀ {β : Type w} [Representation M β], (m : Obj (M := M) β) → In m NPos →
      ∀ {γ : Type x} [Representation M γ], (n : Obj (M := M) γ) → In n NPos →
      (∃ r s : ℝ, denote m = M.number (r : ℂ) ∧ denote n = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)) →
      ∃ r s : ℝ,
        F.callValue (denote a) (if reverse then denote n else denote m) = M.number (r : ℂ) ∧
        F.callValue (denote a) (if reverse then denote m else denote n) = M.number (s : ℂ) ∧
        (if strict then r < s else r ≤ s)) : SequenceOrderValue M strict reverse (denote a) :=
  forallMembersOfRepresentations NPos (fun m hm =>
    forallMembersOfRepresentations NPos (fun n hn => h m hm n hn))

def SequenceNondecreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M false false a

def SequenceNondecreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceNondecreasingValue M (denote a)

def SequenceNonincreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M false true a

def SequenceNonincreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceNonincreasingValue M (denote a)

def SequenceStrictlyIncreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M true false a

def SequenceStrictlyIncreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceStrictlyIncreasingValue M (denote a)

def SequenceStrictlyDecreasingValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := SequenceOrderValue M true true a

def SequenceStrictlyDecreasing {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceStrictlyDecreasingValue M (denote a)

def SequenceBoundedAboveValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := RealBoundedAboveValue M (FunctionSemantics.rangeValue a)

def SequenceBoundedAbove {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceBoundedAboveValue M (denote a)

def SequenceBoundedBelowValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := RealBoundedBelowValue M (FunctionSemantics.rangeValue a)

def SequenceBoundedBelow {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceBoundedBelowValue M (denote a)

def SequenceBoundedValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop := RealBoundedValue M (FunctionSemantics.rangeValue a)

def SequenceBounded {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceBoundedValue M (denote a)

end Litex

namespace Litex

theorem negationWeakOrder {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (NegObj (M := M) α)) (q : Obj (M := M) (NegObj (M := M) β))
    (h : Le q.val.arg p.val.arg) : Le p q := by
  obtain ⟨r,s,hr,hs,h⟩ := h
  refine ⟨-s,-r,?_,?_,neg_le_neg h⟩
  · change M.negValue (denote p.val.arg) = _
    rw [hs,M.neg_numbers,Complex.ofReal_neg]
  · change M.negValue (denote q.val.arg) = _
    rw [hr,M.neg_numbers,Complex.ofReal_neg]

theorem negationStrictOrder {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (NegObj (M := M) α)) (q : Obj (M := M) (NegObj (M := M) β))
    (h : Lt q.val.arg p.val.arg) : Lt p q := by
  obtain ⟨r,s,hr,hs,h⟩ := h
  refine ⟨-s,-r,?_,?_,neg_lt_neg h⟩
  · change M.negValue (denote p.val.arg) = _
    rw [hs,M.neg_numbers,Complex.ofReal_neg]
  · change M.negValue (denote q.val.arg) = _
    rw [hr,M.neg_numbers,Complex.ofReal_neg]
end Litex


namespace Litex

/-- The source tail keeps its positive-natural carrier and cutoff comparison. -/
def sequenceTailValue {M : Semantics.{u}} [SetSemantics M] (cutoff : M.Value) : M.Value :=
  SetSemantics.sepValue (denote (NPos (M := M))) (fun n =>
    ∃ _ : M.mem n (denote (NPos (M := M))),
      ∃ r s : ℝ, cutoff = M.number (r : ℂ) ∧ n = M.number (s : ℂ) ∧ r ≤ s)

def sequenceEpsilonBallValue {M : Semantics.{u}} [SetSemantics M]
    (value epsilon : M.Value) : M.Value :=
  SetSemantics.sepValue (denote (R (M := M))) (fun y =>
    ∃ _ : M.mem y (denote (R (M := M))),
      ∃ r s : ℝ, absValue (M.subValue y value) = M.number (r : ℂ) ∧
        epsilon = M.number (s : ℂ) ∧ r < s)

def SequenceLimitTailValue (M : Semantics.{u}) [FunctionSemantics M]
    (a value epsilon cutoff : M.Value) : Prop :=
  ∀ n, M.mem n (sequenceTailValue cutoff) →
    M.mem n (FunctionSemantics.preimageValue a
      (fun y => M.mem y (sequenceEpsilonBallValue value epsilon)))

def SequenceCauchyTailValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (a epsilon cutoff : M.Value) : Prop :=
  ∀ p, M.mem p (FiniteFunction.cartValue ![sequenceTailValue cutoff, sequenceTailValue cutoff]) →
    M.mem p (SetSemantics.sepValue
      (FiniteFunction.cartValue ![denote (NPos (M := M)), denote (NPos (M := M))])
      (fun q => ∃ _ : M.mem q (FiniteFunction.cartValue
        ![denote (NPos (M := M)), denote (NPos (M := M))]),
        ∃ r s : ℝ,
          absValue (M.subValue
            (F.callValue a (F.callValue q (M.number 1)))
            (F.callValue a (F.callValue q (M.number 2)))) = M.number (r : ℂ) ∧
          epsilon = M.number (s : ℂ) ∧ r < s))

def HasSequenceLimitValue (M : Semantics.{u}) [FunctionSemantics M]
    (a value : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceLimitTailValue M a value epsilon (denote cutoff)

def HasSequenceLimit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) : Prop :=
  HasSequenceLimitValue M (denote a) (denote value)

def SequenceCauchyValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceCauchyTailValue M a epsilon (denote cutoff)

def SequenceCauchy {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceCauchyValue M (denote a)

def SequenceConvergentValue (M : Semantics.{u}) [FunctionSemantics M]
    (a : M.Value) : Prop :=
  ∃ value : Obj (M := M) M.Value, ∃ _ : In value R,
    HasSequenceLimitValue M a (denote value)

def SequenceConvergent {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) : Prop :=
  SequenceConvergentValue M (denote a)

theorem sequenceLimitOfForall {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β)
    (h : ∀ {γ : Type x} [Representation M γ], (epsilon : Obj (M := M) γ) →
      In epsilon RPos → ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
        SequenceLimitTailValue M (denote a) (denote value) (denote epsilon) (denote cutoff)) :
    HasSequenceLimit a value := forallMembersOfRepresentations RPos h

theorem sequenceCauchyOfForall {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (h : ∀ {γ : Type w} [Representation M γ], (epsilon : Obj (M := M) γ) →
      In epsilon RPos → ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
        SequenceCauchyTailValue M (denote a) (denote epsilon) (denote cutoff)) :
    SequenceCauchy a := forallMembersOfRepresentations RPos h
end Litex

namespace Litex

-- A single tail bound yields the native metric bound at a positive natural index.
theorem sequenceLimitAtIndex {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r epsilon : ℝ) (cutoff : Obj (M := M) M.Value)
    (n : ℕ) (hn : 0 < n)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hcut : In cutoff NPos)
    (horder : NativeBridge.asNat cutoff (inNPos_natural cutoff hcut) ≤ n)
    (htail : SequenceLimitTailValue M a (M.number (r : ℂ)) (M.number (epsilon : ℂ)) (denote cutoff)) :
    ∃ v : ℝ, F.callValue a (M.number (n : ℂ)) = M.number (v : ℂ) ∧ |v-r| < epsilon := by
  let cut := NativeBridge.asNat cutoff (inNPos_natural cutoff hcut)
  have hcutval : denote cutoff = M.number ((cut : ℕ) : ℂ) := NativeBridge.asNat_spec cutoff (inNPos_natural cutoff hcut)
  have hnmem : M.mem (M.number (n : ℂ)) (denote (NPos (M := M))) := numberInNPosOfEq (M := M) (n : ℂ) n rfl hn
  have htailmem : M.mem (M.number (n : ℂ)) (sequenceTailValue (denote cutoff)) := by
    apply (F.sep_members _ _ _).mpr
    refine ⟨hnmem, hnmem, (cut : ℝ), (n : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_natCast] using hcutval
    · simp only [Complex.ofReal_natCast]
    · exact_mod_cast horder
  have himage := htail _ htailmem
  have hdomain := isSet (NPos (M := M))
  have hp := ((FunctionSemantics.preimage_mem_iff (fun y => M.mem y (sequenceEpsilonBallValue (M.number (r : ℂ)) (M.number (epsilon : ℂ)))) hdomain hf).mp himage).2
  obtain ⟨hvR, _, t, e, hdist, heps, hlt⟩ := (F.sep_members _ _ _).mp hp
  obtain ⟨v, hv⟩ := (M.real_members _).mp hvR
  have he : e = epsilon := Complex.ofReal_injective (M.number_injective heps).symm
  have ht : t = |v-r| := by
    have hden : absValue (M.subValue (F.callValue a (M.number (n : ℂ))) (M.number (r : ℂ))) = M.number ((|v-r| : ℝ) : ℂ) := by
      rw [hv, M.sub_numbers, ← Complex.ofReal_sub, absValue_number]
    exact Complex.ofReal_injective (M.number_injective (hdist.symm.trans hden))
  refine ⟨v, hv, ?_⟩
  simpa only [ht, he] using hlt

theorem sequenceLimitUnique {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r s : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hr : HasSequenceLimitValue M a (M.number (r : ℂ)))
    (hs : HasSequenceLimitValue M a (M.number (s : ℂ))) : r = s := by
  by_contra hne
  have hd : 0 < |r-s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let epsilon : ℝ := |r-s| / 2
  have heps : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsmem : M.mem (M.number (epsilon : ℂ)) (denote (RPos (M := M))) := numberInRPos epsilon heps
  obtain ⟨c1,hc1,ht1⟩ := hr (M.number (epsilon : ℂ)) hepsmem
  obtain ⟨c2,hc2,ht2⟩ := hs (M.number (epsilon : ℂ)) hepsmem
  let n1 := NativeBridge.asNat c1 (inNPos_natural c1 hc1)
  let n2 := NativeBridge.asNat c2 (inNPos_natural c2 hc2)
  let n := Nat.max n1 n2 + 1
  have hn : 0 < n := by dsimp [n]; omega
  have h1 : n1 ≤ n := Nat.le_trans (Nat.le_max_left n1 n2) (Nat.le_succ _)
  have h2 : n2 ≤ n := Nat.le_trans (Nat.le_max_right n1 n2) (Nat.le_succ _)
  obtain ⟨v,hv,hvr⟩ := sequenceLimitAtIndex a r epsilon c1 n hn hf hc1 h1 ht1
  obtain ⟨w,hw,hws⟩ := sequenceLimitAtIndex a s epsilon c2 n hn hf hc2 h2 ht2
  have heq : v = w := Complex.ofReal_injective (M.number_injective (hv.symm.trans hw))
  subst w
  have htri : |r-s| ≤ |r-v| + |v-s| := abs_sub_le r v s
  rw [abs_sub_comm r v] at htri
  dsimp [epsilon] at hvr hws
  linarith
end Litex
namespace Litex

noncomputable def sequenceLimitValue {M : Semantics.{u}} [FunctionSemantics M] (a : M.Value) : M.Value := by
  classical
  exact if h : SequenceConvergentValue M a then denote (Classical.choose h) else M.number 0

theorem sequenceLimitValueOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    (a : M.Value) (r : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hr : HasSequenceLimitValue M a (M.number (r : ℂ))) :
    sequenceLimitValue a = M.number (r : ℂ) := by
  classical
  have hm : M.mem (M.number (r : ℂ)) (denote (R (M := M))) := (M.real_members _).mpr ⟨r,rfl⟩
  let v : Obj (M := M) M.Value := semanticObject (M.number (r : ℂ)) (M.member_isSet hm)
  have hc : SequenceConvergentValue M a := ⟨v, hm, hr⟩
  let selected := Classical.choose hc
  have hs := Classical.choose_spec hc
  obtain ⟨s, hselected⟩ := (M.real_members _).mp hs.1
  have heq : s = r := sequenceLimitUnique a s r hf (hselected ▸ hs.2) hr
  unfold sequenceLimitValue
  rw [dif_pos hc]
  exact hselected.trans (congrArg (fun x : ℝ => M.number (x : ℂ)) heq)

structure SequenceLimitObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  sequence : Obj (M := M) α

noncomputable instance sequenceLimitRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (SequenceLimitObj (M := M) α) where
  wd p := M.mem (denote p.sequence) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) ∧
    SequenceConvergentValue M (denote p.sequence)
  denote p := sequenceLimitValue (denote p.sequence)
  wd_isSet {p} hp := by
    classical
    unfold sequenceLimitValue
    rw [dif_pos hp.2]
    exact M.member_isSet (Classical.choose_spec hp.2).1
end Litex
namespace Litex

noncomputable def sequenceLimit {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hc : SequenceConvergentValue M (denote a)) : Obj (M := M) (SequenceLimitObj (M := M) α) :=
  ⟨⟨a⟩, ha, hc⟩

theorem sequenceConvergentOfCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) (hR : In value R)
    (h : HasSequenceLimit a value) : SequenceConvergentValue M (denote a) := by
  let v : Obj (M := M) M.Value := semanticObject (denote value) (isSet value)
  exact ⟨v, hR, h⟩

theorem sequenceLimitEqCandidate {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (SequenceLimitObj (M := M) α)) (value : Obj (M := M) β)
    (hR : In value R) (h : HasSequenceLimit p.val.sequence value) : Same p value := by
  let r := NativeBridge.asReal value hR
  have hr := NativeBridge.asReal_spec value hR
  change sequenceLimitValue (denote p.val.sequence) = denote value
  exact (sequenceLimitValueOfCandidate (denote p.val.sequence) r p.wd.1 (hr ▸ h)).trans hr.symm

theorem sequenceLimitInR {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (SequenceLimitObj (M := M) α)) : In p R := by
  classical
  change M.mem (sequenceLimitValue (denote p.val.sequence)) (denote R)
  unfold sequenceLimitValue
  rw [dif_pos p.wd.2]
  exact (Classical.choose_spec p.wd.2).1
end Litex

namespace Litex
theorem unguardedFunctionDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B)
    (h : In a (fnSet (FunctionSignature.withGuard D B hD hB (fun _ => True)))) :
    M.mem (denote a) (F.fnSetValue D B) := by
  have heq : F.sepValue D (fun _ => True) = D := by
    apply F.ext _ _ (F.sep_isSet D _ hD) hD
    intro x
    simp only [F.sep_members, and_true]
  change M.mem (denote a) (F.fnSetValue (F.sepValue D (fun _ => True)) B) at h
  simpa only [heq] using h
end Litex

namespace Litex
theorem sequenceLimitCandidatesEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (v : Obj (M := M) β) (w : Obj (M := M) γ)
    (hdom : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In v R) (hw : In w R) (h1 : HasSequenceLimit a v) (h2 : HasSequenceLimit a w) : Same v w := by
  let r := NativeBridge.asReal v hv
  let s := NativeBridge.asReal w hw
  have hr := NativeBridge.asReal_spec v hv
  have hs := NativeBridge.asReal_spec w hw
  have heq : r = s := sequenceLimitUnique (denote a) r s hdom (hr ▸ h1) (hs ▸ h2)
  exact hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ)) heq).trans hs.symm)
end Litex
