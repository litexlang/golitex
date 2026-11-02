import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

