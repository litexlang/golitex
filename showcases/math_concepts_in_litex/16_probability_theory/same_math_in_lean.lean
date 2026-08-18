import Mathlib

/-!
The same probability-theory interfaces as `main.lit`, expressed in Lean 4.

This is handwritten comparison code, not generated Litex-to-Lean output.
-/

universe u v

namespace ProbabilityTheorySameMathInLean

noncomputable section

abbrev Event (Omega : Type u) := Set Omega

def countableUnion (family : Nat -> Event Omega) : Event Omega :=
  Set.iUnion family

structure SigmaAlgebraSetting (Omega : Type u) where
  events : Set (Event Omega)
  empty_mem : events ∅
  universe_mem : events Set.univ
  complement_mem : forall {A}, events A -> events A.compl
  intersection_mem : forall {A B}, events A -> events B -> events (A ∩ B)
  countableUnion_mem : forall (family : Nat -> Event Omega),
    (forall n, events (family n)) -> events (countableUnion family)

abbrev MeasurableEvent {Omega : Type u} (S : SigmaAlgebraSetting Omega) :=
  {A : Event Omega // S.events A}

def eventIntersection {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (A B : MeasurableEvent S) : MeasurableEvent S :=
  ⟨A.1 ∩ B.1, S.intersection_mem A.2 B.2⟩

def eventCountableUnion {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (family : Nat -> MeasurableEvent S) : MeasurableEvent S :=
  ⟨countableUnion (fun n => (family n).1),
    S.countableUnion_mem (fun n => (family n).1) (fun n => (family n).2)⟩

def PairwiseDisjointEvents {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (family : Nat -> MeasurableEvent S) : Prop :=
  Pairwise (fun left right => Disjoint (family left).1 (family right).1)

structure ProbabilitySpaceSetting (Omega : Type u) where
  sigma : SigmaAlgebraSetting Omega
  probability : MeasurableEvent sigma -> Real
  empty_probability : probability ⟨∅, sigma.empty_mem⟩ = 0
  universe_probability : probability ⟨Set.univ, sigma.universe_mem⟩ = 1
  nonnegative : forall A, 0 <= probability A
  countably_additive : forall (family : Nat -> MeasurableEvent sigma),
    PairwiseDisjointEvents sigma family ->
      HasSum (fun n => probability (family n))
        (probability (eventCountableUnion sigma family))

theorem kolmogorovCountableAdditivity {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega)
    (eventSequence : Nat -> MeasurableEvent P.sigma)
    (disjoint : PairwiseDisjointEvents P.sigma eventSequence) :
    HasSum (fun n => P.probability (eventSequence n))
      (P.probability (eventCountableUnion P.sigma eventSequence)) :=
  P.countably_additive eventSequence disjoint

def conditionalProbability {Omega : Type u} (P : ProbabilitySpaceSetting Omega)
    (A B : MeasurableEvent P.sigma) (_positive : 0 < P.probability B) : Real :=
  P.probability (eventIntersection P.sigma A B) / P.probability B

def AreIndependent {Omega : Type u} (P : ProbabilitySpaceSetting Omega)
    (A B : MeasurableEvent P.sigma) : Prop :=
  P.probability (eventIntersection P.sigma A B) =
    P.probability A * P.probability B

theorem independentEventConditionalProbability {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma)
    (independent : AreIndependent P A B) (positive : 0 < P.probability B) :
    conditionalProbability P A B positive = P.probability A := by
  rw [conditionalProbability, independent]
  field_simp

def IsMeasurableMap {Source : Type u} {Target : Type v}
    (source : SigmaAlgebraSetting Source) (target : SigmaAlgebraSetting Target)
    (f : Source -> Target) : Prop :=
  forall B : MeasurableEvent target, source.events (f ⁻¹' B.1)

def IsRandomVariable {Omega : Type u} (source : SigmaAlgebraSetting Omega)
    (realEvents : SigmaAlgebraSetting Real) (X : Omega -> Real) : Prop :=
  IsMeasurableMap source realEvents X

def IsDistributionOf {Omega : Type u} {Target : Type v}
    (P : ProbabilitySpaceSetting Omega) (target : SigmaAlgebraSetting Target)
    (X : Omega -> Target) (distribution : MeasurableEvent target -> Real) : Prop :=
  forall B : MeasurableEvent target,
    exists measurablePreimage : P.sigma.events (X ⁻¹' B.1),
      distribution B = P.probability ⟨X ⁻¹' B.1, measurablePreimage⟩

theorem distributionOfHasMeasurableMap {Omega : Type u} {Target : Type v}
    (P : ProbabilitySpaceSetting Omega) (target : SigmaAlgebraSetting Target)
    (X : Omega -> Target) (distribution : MeasurableEvent target -> Real)
    (isDistribution : IsDistributionOf P target X distribution) :
    IsMeasurableMap P.sigma target X := by
  intro B
  exact (isDistribution B).choose

end

end ProbabilityTheorySameMathInLean
