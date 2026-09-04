import Litex.Core
import Litex.Rules

/-!
# Thin native bridges for the legacy Litex ABI

This module is deliberately small.  Litex facts remain expressed with
`Litex.In`, `Litex.Subset`, `Litex.Same`, and the existing LUB proposition.  A
bridge rule opens a temporary native view, lets Mathlib work on that view, and
then returns to a Litex proposition.  It is a compatibility slice for the
legacy `Core` ABI; the same interface can later be implemented for the direct
`Obj`-mirroring `Litex.Object`.
-/

namespace Litex.Bridge

/-! `Litex.In` in the legacy ABI is a `Prop` existential.  Lean can open it
    inside another proposition, but cannot eliminate it into a data structure
    in `Type` without a choice principle.  This compatibility bridge therefore
    keeps the native witness as a proposition, `Litex.AsReal source value`, and
    opens it locally with `rcases`.  A future Core can replace this with a
    Type-valued evidence view. -/

abbrev AsReal {α : Type} (source : α) (value : ℝ) : Prop :=
  Litex.AsReal source value

abbrev AsComplex {α : Type} (source : α) (value : ℂ) : Prop :=
  @Litex.Same α ℂ
    (Litex.ComplexObserver.none α)
    (Litex.ComplexObserver.none ℂ)
    source value

theorem asReal
    {α : Type}
    (source : α)
    (value : ℝ)
    (membership : Litex.AsReal source value) :
    AsReal source value :=
  membership

theorem asRealOfMembership
    {α : Type}
    (source : α)
    (membership : Litex.In source Litex.R) :
    ∃ value : ℝ, AsReal source value := by
  rcases membership with ⟨value, sourceSame⟩
  exact ⟨value, Litex.Same.withoutObservation sourceSame⟩

theorem asRealOfSubset
    (set : Litex.Set)
    (subset : Litex.Subset set Litex.R)
    {α : Type}
    (source : α)
    (membership : Litex.In source set) :
    ∃ value : ℝ, AsReal source value := by
  rcases subset source membership with ⟨value, sourceSame⟩
  exact ⟨value, Litex.Same.withoutObservation sourceSame⟩

theorem asComplex
    {α : Type}
    (source : α)
    (value : ℂ)
    (membership : @Litex.Same α ℂ
      (Litex.ComplexObserver.none α)
      (Litex.ComplexObserver.none ℂ)
      source value) :
    AsComplex source value :=
  membership

theorem asComplexOfMembership
    {α : Type}
    (source : α)
    (membership : Litex.In source Litex.C) :
    ∃ value : ℂ, AsComplex source value := by
  rcases membership with ⟨value, sourceSame⟩
  exact ⟨value, Litex.Same.withoutObservation sourceSame⟩

/-- The canonical native-real set used by the current LUB bridge. -/
def asRealSet
    (set : Litex.Set)
    (subset : Litex.Subset set Litex.R) :
    _root_.Set ℝ :=
  Litex.realSubsetMemberValues set subset

/-- Convert a native Mathlib LUB proof back into the current Litex LUB fact.
    The equality hypothesis states that the compiler used the same native set
    as the Litex-side membership view. -/
theorem realLeastUpperBoundBack
    (set : Litex.Set)
    (subset : Litex.Subset set Litex.R)
    (candidate : ℝ)
    (native_lub : IsLUB (asRealSet set subset) candidate) :
    Litex.RealLeastUpperBound set (candidate : ℂ) := by
  refine ⟨subset, ?_⟩
  simpa [asRealSet, Litex.realSubsetMemberValues, Litex.OrderValue] using native_lub

/-! This is the concrete completeness-shaped entry point.  The native rule
    proves nonemptiness and boundedness in Mathlib, obtains `sSup`, and this
    theorem reifies that exact native certificate as the Litex LUB fact. -/

theorem realLeastUpperBoundBackOfCsSup
    (set : Litex.Set)
    (subset : Litex.Subset set Litex.R)
    (valuesNonempty : (asRealSet set subset).Nonempty)
    (valuesBounded : BddAbove (asRealSet set subset)) :
    Litex.RealLeastUpperBound set ((sSup (asRealSet set subset) : ℝ) : ℂ) := by
  apply realLeastUpperBoundBack set subset (sSup (asRealSet set subset))
  exact isLUB_csSup valuesNonempty valuesBounded

/-- A subset member can be consumed by native real order without selecting a
    `Subset.rep`.  The returned `AsReal` proof is retained for a later Litex
    reification rule. -/
theorem memberRealLeOfLUB
    (set : Litex.Set)
    (subset : Litex.Subset set Litex.R)
    (candidate : ℝ)
    (native_lub : IsLUB (asRealSet set subset) candidate)
    {α : Type}
    (source : α)
    (membership : Litex.In source set) :
    ∃ sourceReal : ℝ,
      AsReal source sourceReal ∧
      sourceReal ≤ candidate := by
  rcases subset source membership with ⟨sourceReal, sourceSame⟩
  have source_in_set : Litex.In sourceReal set := by
    exact (Litex.In.congr sourceSame set).mp membership
  have source_in_values : sourceReal ∈ asRealSet set subset := by
    change Litex.In sourceReal set
    exact source_in_set
  exact ⟨sourceReal, Litex.Same.withoutObservation sourceSame,
    native_lub.1 source_in_values⟩

/-- A complete native-use example: heterogeneous Litex membership is lowered
    to one real witness, and that witness is consumed by Mathlib's supremum
    order.  No `In.rep` or `Subset.rep` occurs in the generated proof. -/
theorem memberRealLeCsSup
    (set : Litex.Set)
    (subset : Litex.Subset set Litex.R)
    (valuesNonempty : (asRealSet set subset).Nonempty)
    (valuesBounded : BddAbove (asRealSet set subset))
    {α : Type}
    (source : α)
    (membership : Litex.In source set) :
    ∃ sourceReal : ℝ,
      AsReal source sourceReal ∧
      sourceReal ≤ sSup (asRealSet set subset) := by
  exact memberRealLeOfLUB set subset (sSup (asRealSet set subset))
    (isLUB_csSup valuesNonempty valuesBounded) source membership

end Litex.Bridge
