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

def emptyEvent {Omega : Type u} (S : SigmaAlgebraSetting Omega) :
    MeasurableEvent S :=
  ⟨∅, S.empty_mem⟩

def universeEvent {Omega : Type u} (S : SigmaAlgebraSetting Omega) :
    MeasurableEvent S :=
  ⟨Set.univ, S.universe_mem⟩

def eventComplement {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (A : MeasurableEvent S) : MeasurableEvent S :=
  ⟨A.1ᶜ, S.complement_mem A.2⟩

def eventDifference {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (A B : MeasurableEvent S) : MeasurableEvent S :=
  eventIntersection S A (eventComplement S B)

def twoEventSequence {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (A B : MeasurableEvent S) : Nat -> MeasurableEvent S :=
  fun n => if n = 0 then A else if n = 1 then B else emptyEvent S

def eventUnion {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (A B : MeasurableEvent S) : MeasurableEvent S :=
  eventCountableUnion S (twoEventSequence S A B)

theorem eventUnion_coe {Omega : Type u} (S : SigmaAlgebraSetting Omega)
    (A B : MeasurableEvent S) :
    (eventUnion S A B).1 = A.1 ∪ B.1 := by
  ext point
  simp only [eventUnion, eventCountableUnion, countableUnion, Set.mem_iUnion,
    Set.mem_union]
  constructor
  · rintro ⟨i, membership⟩
    by_cases i0 : i = 0
    · left
      simpa [twoEventSequence, i0] using membership
    · by_cases i1 : i = 1
      · right
        simpa [twoEventSequence, i0, i1] using membership
      · simp [twoEventSequence, i0, i1, emptyEvent] at membership
  · intro membership
    rcases membership with inA | inB
    · exact ⟨0, by simpa [twoEventSequence] using inA⟩
    · exact ⟨1, by simpa [twoEventSequence] using inB⟩

theorem twoEventSequencePairwiseDisjoint {Omega : Type u}
    (S : SigmaAlgebraSetting Omega) (A B : MeasurableEvent S)
    (disjoint : Disjoint A.1 B.1) :
    PairwiseDisjointEvents S (twoEventSequence S A B) := by
  intro i j different
  by_cases i0 : i = 0
  · subst i
    have j0 : j ≠ 0 := Ne.symm different
    by_cases j1 : j = 1
    · subst j
      simpa [twoEventSequence] using disjoint
    · simp [twoEventSequence, j0, j1, emptyEvent]
  · by_cases i1 : i = 1
    · subst i
      have j1 : j ≠ 1 := Ne.symm different
      by_cases j0 : j = 0
      · subst j
        simpa [twoEventSequence] using disjoint.symm
      · simp [twoEventSequence, j0, j1, emptyEvent]
    · simp [twoEventSequence, i0, i1, emptyEvent]

theorem twoEventProbabilityHasSum {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma) :
    HasSum (fun n => P.probability (twoEventSequence P.sigma A B n))
      (P.probability A + P.probability B) := by
  have sequence_eq :
      (fun n => P.probability (twoEventSequence P.sigma A B n)) =
        (fun n : Nat =>
          (if n = 0 then P.probability A else 0) +
          (if n = 1 then P.probability B else 0)) := by
    funext n
    by_cases n0 : n = 0
    · simp [twoEventSequence, n0]
    · by_cases n1 : n = 1
      · simp [twoEventSequence, n1]
      · simp [twoEventSequence, n0, n1, emptyEvent, P.empty_probability]
  rw [sequence_eq]
  exact
    (hasSum_ite_eq (0 : Nat) (P.probability A)).add
      (hasSum_ite_eq (1 : Nat) (P.probability B))

/- Binary finite additivity is a theorem obtained by padding with empty events;
it is not an additional field of `ProbabilitySpaceSetting`. -/
theorem probabilityOfDisjointUnion {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma)
    (disjoint : Disjoint A.1 B.1) :
    P.probability (eventUnion P.sigma A B) =
      P.probability A + P.probability B := by
  exact
    (P.countably_additive (twoEventSequence P.sigma A B)
      (twoEventSequencePairwiseDisjoint P.sigma A B disjoint)).unique
      (twoEventProbabilityHasSum P A B)

theorem eventUnionComplement_eq_universe {Omega : Type u}
    (S : SigmaAlgebraSetting Omega) (A : MeasurableEvent S) :
    eventUnion S A (eventComplement S A) = universeEvent S := by
  apply Subtype.ext
  rw [eventUnion_coe]
  simp [eventComplement, universeEvent]

theorem probabilityOfEventComplement {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A : MeasurableEvent P.sigma) :
    P.probability (eventComplement P.sigma A) = 1 - P.probability A := by
  have disjoint : Disjoint A.1 (eventComplement P.sigma A).1 := by
    apply Set.disjoint_left.mpr
    intro point inA inComplement
    exact inComplement inA
  have additivity :=
    probabilityOfDisjointUnion P A (eventComplement P.sigma A) disjoint
  rw [eventUnionComplement_eq_universe] at additivity
  have universe_probability : P.probability (universeEvent P.sigma) = 1 := by
    simpa [universeEvent] using P.universe_probability
  rw [universe_probability] at additivity
  linarith

theorem eventUnionDifference_eq_left {Omega : Type u}
    (S : SigmaAlgebraSetting Omega) (A B : MeasurableEvent S)
    (subset : B.1 ⊆ A.1) :
    eventUnion S B (eventDifference S A B) = A := by
  apply Subtype.ext
  rw [eventUnion_coe]
  ext point
  constructor
  · intro membership
    rcases membership with inB | inDifference
    · exact subset inB
    · exact inDifference.1
  · intro inA
    by_cases inB : point ∈ B.1
    · exact Or.inl inB
    · exact Or.inr ⟨inA, inB⟩

theorem probabilityOfDifferenceUnderSubset {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma)
    (subset : B.1 ⊆ A.1) :
    P.probability (eventDifference P.sigma A B) =
      P.probability A - P.probability B := by
  have disjoint : Disjoint B.1 (eventDifference P.sigma A B).1 := by
    apply Set.disjoint_left.mpr
    intro point inB inDifference
    exact inDifference.2 inB
  have additivity :=
    probabilityOfDisjointUnion P B (eventDifference P.sigma A B) disjoint
  rw [eventUnionDifference_eq_left P.sigma A B subset] at additivity
  linarith

theorem probabilityMono {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma)
    (subset : A.1 ⊆ B.1) :
    P.probability A <= P.probability B := by
  have difference := probabilityOfDifferenceUnderSubset P B A subset
  have nonnegative := P.nonnegative (eventDifference P.sigma B A)
  linarith

theorem eventDifference_subset_left {Omega : Type u}
    (S : SigmaAlgebraSetting Omega) (A B : MeasurableEvent S) :
    (eventDifference S A B).1 ⊆ A.1 := by
  intro point membership
  exact membership.1

theorem eventUnionDifference_eq_union {Omega : Type u}
    (S : SigmaAlgebraSetting Omega) (A B : MeasurableEvent S) :
    eventUnion S A (eventDifference S B A) = eventUnion S A B := by
  apply Subtype.ext
  rw [eventUnion_coe, eventUnion_coe]
  ext point
  constructor
  · intro membership
    rcases membership with inA | inDifference
    · exact Or.inl inA
    · exact Or.inr inDifference.1
  · intro membership
    rcases membership with inA | inB
    · exact Or.inl inA
    · by_cases inA : point ∈ A.1
      · exact Or.inl inA
      · exact Or.inr ⟨inB, inA⟩

theorem eventDifferenceIntersection_eq {Omega : Type u}
    (S : SigmaAlgebraSetting Omega) (A B : MeasurableEvent S) :
    eventDifference S B (eventIntersection S A B) =
      eventDifference S B A := by
  apply Subtype.ext
  ext point
  constructor
  · intro membership
    exact ⟨membership.1, fun inA => membership.2 ⟨inA, membership.1⟩⟩
  · intro membership
    exact ⟨membership.1, fun inIntersection => membership.2 inIntersection.1⟩

theorem probabilityInclusionExclusion {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma) :
    P.probability (eventUnion P.sigma A B) =
      P.probability A + P.probability B -
        P.probability (eventIntersection P.sigma A B) := by
  have intersection_subset :
      (eventIntersection P.sigma A B).1 ⊆ B.1 := by
    intro point membership
    exact membership.2
  have difference_probability :=
    probabilityOfDifferenceUnderSubset P B
      (eventIntersection P.sigma A B) intersection_subset
  rw [eventDifferenceIntersection_eq P.sigma A B] at difference_probability
  have disjoint : Disjoint A.1 (eventDifference P.sigma B A).1 := by
    apply Set.disjoint_left.mpr
    intro point inA inDifference
    exact inDifference.2 inA
  have additivity :=
    probabilityOfDisjointUnion P A (eventDifference P.sigma B A) disjoint
  rw [eventUnionDifference_eq_union P.sigma A B] at additivity
  linarith

theorem probabilityUnionBound {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A B : MeasurableEvent P.sigma) :
    P.probability (eventUnion P.sigma A B) <=
      P.probability A + P.probability B := by
  have intersection_nonnegative :=
    P.nonnegative (eventIntersection P.sigma A B)
  have inclusion_exclusion := probabilityInclusionExclusion P A B
  linarith

theorem probabilityBetweenZeroAndOne {Omega : Type u}
    (P : ProbabilitySpaceSetting Omega) (A : MeasurableEvent P.sigma) :
    0 <= P.probability A ∧ P.probability A <= 1 := by
  constructor
  · exact P.nonnegative A
  · have complement_nonnegative := P.nonnegative (eventComplement P.sigma A)
    rw [probabilityOfEventComplement P A] at complement_nonnegative
    linarith

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

/-! ## Borel events, event limits, and concrete measure constructions

The Litex development stays real-valued because a probability is finite.  For
the library comparison below we use Mathlib's native `Measure`, whose values
are extended nonnegative reals, and expose the corresponding checked standard
theorems and constructors.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

abbrev realBorelMeasurableSpace : MeasurableSpace Real := borel Real

theorem realBorelGeneratedByBoundedOpenIntervals :
    borel Real = MeasurableSpace.generateFrom
      (⋃ (a : Rat) (b : Rat) (_ : a < b), {Set.Ioo (a : Real) (b : Real)}) :=
  Real.borel_eq_generateFrom_Ioo_rat

theorem realOpenIntervalMeasurable (left right : Real) :
    MeasurableSet (Set.Ioo left right) :=
  measurableSet_Ioo

def eventTailUnion (events : Nat -> Set Omega) (skipped : Nat) : Set Omega :=
  ⋃ offset, events (skipped + offset)

def eventTailIntersection (events : Nat -> Set Omega) (skipped : Nat) : Set Omega :=
  ⋂ offset, events (skipped + offset)

def eventLimsup (events : Nat -> Set Omega) : Set Omega :=
  Filter.limsup events Filter.atTop

def eventLiminf (events : Nat -> Set Omega) : Set Omega :=
  Filter.liminf events Filter.atTop

theorem eventCountableIntersectionMeasurable [MeasurableSpace Omega]
    (events : Nat -> Set Omega) (measurable : forall n, MeasurableSet (events n)) :
    MeasurableSet (⋂ n, events n) :=
  MeasurableSet.iInter measurable

theorem eventTailUnionMeasurable [MeasurableSpace Omega]
    (events : Nat -> Set Omega) (measurable : forall n, MeasurableSet (events n))
    (skipped : Nat) : MeasurableSet (eventTailUnion events skipped) := by
  exact MeasurableSet.iUnion fun offset => measurable (skipped + offset)

theorem eventTailIntersectionMeasurable [MeasurableSpace Omega]
    (events : Nat -> Set Omega) (measurable : forall n, MeasurableSet (events n))
    (skipped : Nat) : MeasurableSet (eventTailIntersection events skipped) := by
  exact MeasurableSet.iInter fun offset => measurable (skipped + offset)

theorem eventLimsupMeasurable [MeasurableSpace Omega]
    (events : Nat -> Set Omega) (measurable : forall n, MeasurableSet (events n)) :
    MeasurableSet (eventLimsup events) := by
  exact MeasurableSet.measurableSet_limsup measurable

theorem eventLiminfMeasurable [MeasurableSpace Omega]
    (events : Nat -> Set Omega) (measurable : forall n, MeasurableSet (events n)) :
    MeasurableSet (eventLiminf events) := by
  exact MeasurableSet.measurableSet_liminf measurable

theorem probabilityContinuousFromBelow [MeasurableSpace Omega]
    (mu : Measure Omega) (events : Nat -> Set Omega) (increasing : Monotone events) :
    Tendsto (fun n => mu (events n)) atTop (nhds (mu (⋃ n, events n))) := by
  simpa [Function.comp_def] using
    (tendsto_measure_iUnion_atTop (μ := mu) increasing)

theorem probabilityContinuousFromAbove [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (events : Nat -> Set Omega)
    (measurable : forall n, MeasurableSet (events n)) (decreasing : Antitone events) :
    Tendsto (fun n => mu (events n)) atTop (nhds (mu (⋂ n, events n))) := by
  simpa [Function.comp_def] using
    (tendsto_measure_iInter_atTop (μ := mu)
      (fun n => (measurable n).nullMeasurableSet) decreasing
      ⟨0, measure_ne_top mu (events 0)⟩)

theorem probabilityCountableSubadditivity [MeasurableSpace Omega]
    (mu : Measure Omega) (events : Nat -> Set Omega) :
    mu (⋃ n, events n) <= ∑' n, mu (events n) :=
  measure_iUnion_le events

def IsNullEvent [MeasurableSpace Omega] (mu : Measure Omega)
    (event : Set Omega) : Prop :=
  mu event = 0

def IsAlmostSureEvent [MeasurableSpace Omega] (mu : Measure Omega)
    (event : Set Omega) : Prop :=
  mu event = 1

theorem countableUnionOfNullEventsIsNull [MeasurableSpace Omega]
    (mu : Measure Omega) (events : Nat -> Set Omega)
    (nullEvents : forall n, IsNullEvent mu (events n)) :
    IsNullEvent mu (⋃ n, events n) := by
  exact measure_iUnion_null nullEvents

theorem almostSureEventIffNullComplement [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (event : Set Omega)
    (measurable : MeasurableSet event) :
    IsAlmostSureEvent mu event <-> IsNullEvent mu eventᶜ := by
  exact (prob_compl_eq_zero_iff measurable).symm

theorem firstBorelCantelli [MeasurableSpace Omega]
    (mu : Measure Omega) (events : Nat -> Set Omega)
    (summableProbabilities : (∑' n, mu (events n)) ≠ ∞) :
    IsNullEvent mu (eventLimsup events) := by
  exact measure_limsup_atTop_eq_zero summableProbabilities

def diracProbability [MeasurableSpace Omega] (point : Omega) : Measure Omega :=
  Measure.dirac point

theorem diracProbabilityIsProbabilitySpace [MeasurableSpace Omega]
    (point : Omega) : IsProbabilityMeasure (diracProbability point) := by
  change IsProbabilityMeasure (Measure.dirac point)
  infer_instance

def conditionedProbabilityMeasure [MeasurableSpace Omega]
    (mu : Measure Omega) (evidence : Set Omega) : Measure Omega :=
  ProbabilityTheory.cond mu evidence

theorem conditionedProbabilityIsProbabilitySpace [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu] (evidence : Set Omega)
    (positive : mu evidence ≠ 0) :
    IsProbabilityMeasure (conditionedProbabilityMeasure mu evidence) :=
  ProbabilityTheory.cond_isProbabilityMeasure positive

def pushforwardProbabilityMeasure {Source : Type u} {Target : Type v}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu : Measure Source) (f : Source -> Target) : Measure Target :=
  mu.map f

theorem pushforwardProbabilityMeasure_apply {Source : Type u} {Target : Type v}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu : Measure Source) (f : Source -> Target) (measurable : Measurable f)
    {event : Set Target} (event_measurable : MeasurableSet event) :
    pushforwardProbabilityMeasure mu f event = mu (f ⁻¹' event) := by
  exact Measure.map_apply measurable event_measurable

theorem pushforwardProbabilityIsProbabilitySpace
    {Source : Type u} {Target : Type v}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu : Measure Source) [IsProbabilityMeasure mu]
    (f : Source -> Target) (measurable : Measurable f) :
    IsProbabilityMeasure (pushforwardProbabilityMeasure mu f) := by
  exact Measure.isProbabilityMeasure_map measurable.aemeasurable

def finiteAtomicProbability [MeasurableSpace Omega] {Index : Type*}
    (weight : Index -> ENNReal) (atom : Index -> Omega) : Measure Omega :=
  Measure.sum fun index => weight index • Measure.dirac (atom index)

theorem finiteAtomicProbabilityIsProbabilitySpace [MeasurableSpace Omega]
    {Index : Type*} [Fintype Index] (weight : Index -> ENNReal)
    (atom : Index -> Omega) (normalized : ∑ index, weight index = 1) :
    IsProbabilityMeasure (finiteAtomicProbability weight atom) := by
  apply HasSum.isProbabilityMeasure_sum_dirac_ennreal
  rw [← normalized]
  exact hasSum_fintype weight

end

end ProbabilityTheorySameMathInLean
