import Litex.MultivariableContinuity

namespace Litex
universe u

theorem multivariableDistancePositiveOfNe {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b n : M.Value) (hn : M.mem n (M.standard .natural))
    (ha : M.mem a (realVectorSetValue n)) (hb : M.mem b (realVectorSetValue n))
    (hne : a ≠ b) : RealLtValue M (M.number 0) (multivariableDistanceValue a b n) := by
  classical
  by_contra hnot
  apply hne
  apply realVectorValueExt a b n ha hb
  intro index hi
  obtain ⟨r,s,t,hr,hs,hd,hbound⟩ := multivariableDistanceCoordinateBound a b n index hn ha hb hi
  have nonpositive : t ≤ 0 := le_of_not_gt (fun ht => hnot ⟨0,t,rfl,hd,ht⟩)
  have zero : |r-s|=0 := le_antisymm (hbound.trans nonpositive) (abs_nonneg _)
  have same : r=s := sub_eq_zero.mp (abs_eq_zero.mp zero)
  rw [hr,hs,same]

theorem multivariableDistanceSelf {M : Semantics.{u}} [F : FunctionSemantics M]
    (a n : M.Value) (ha : M.mem a (realVectorSetValue n)) :
    multivariableDistanceValue a a n=M.number 0 := by
  classical
  let A := closedRangeValue (M.number 1) n
  let D := F.sepValue A (fun _ => True)
  have returns : ∀ k, M.mem k D → M.mem
      (M.subValue (F.callValue a k) (F.callValue a k)) (M.standard .real) := by
    intro k hk
    obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha hk)
    rw [hr,M.sub_numbers,sub_self]
    exact (M.real_members _).mpr ⟨0,by rfl⟩
  have integrand : ∀ k, M.mem k A →
      ((‖NativeBridge.complexValue (F.callValue (multivariableDifferenceValue a a n) k)‖ ^ 2 : ℝ) : ℂ)=0 := by
    intro k hk
    have hkD : M.mem k D := (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
    have call := F.call_graphValue D (M.standard .real)
      (fun i => M.subValue (F.callValue a i) (F.callValue a i)) returns k hkD
    change F.callValue (multivariableDifferenceValue a a n) k = _ at call
    obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha hkD)
    rw [call,hr,M.sub_numbers,sub_self,NativeBridge.complexValue_number,norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0),Complex.ofReal_zero]
  have sumZero : finiteAggregateValue false A
      (fun k => ((‖NativeBridge.complexValue (F.callValue (multivariableDifferenceValue a a n) k)‖ ^ 2 : ℝ) : ℂ))=0 := by
    rw [finiteAggregateValue_congr false A _ (fun _ => (0 : ℂ)) integrand]
    by_cases finite : (memberSet A).Finite
    · simp only [finiteAggregateValue,dif_pos finite,Bool.false_eq_true,↓reduceIte,Finset.sum_const_zero]
    · simp only [finiteAggregateValue,dif_neg finite,Bool.false_eq_true,↓reduceIte]
  unfold multivariableDistanceValue
  change sqrtValue (M.number (finiteAggregateValue false A _))=M.number 0
  rw [sumZero]
  change sqrtValue (M.number ((0 : ℝ) : ℂ))=M.number 0
  rw [sqrtValue_number,Real.sqrt_zero,Complex.ofReal_zero]

private theorem positiveRealAboveZero {M : Semantics.{u}} [SetSemantics M] (epsilon : M.Value)
    (h : M.mem epsilon (denote (RPos (M := M)))) : RealLtValue M (M.number 0) epsilon := by
  obtain ⟨_,e,he,hpositive⟩ := (positiveReal_members _).mp h
  exact ⟨0,e,rfl,he,hpositive⟩

theorem scalarContinuityToMultivariableLimit {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n : M.Value) (hv : M.mem (F.callValue f point) (M.standard .real))
    (hc : ScalarMultivariableContinuousAtValue M f point n)
    (ha : MultivariableAccumulationValue M (F.domainValue f) point n) :
    HasMultivariableScalarLimitValue M f point n (F.callValue f point) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  refine ⟨r,hr,ha,?_⟩
  intro epsilon he
  obtain ⟨delta,hd,hcontrol⟩ := hc epsilon he
  exact ⟨delta,hd,fun input hi _ hclose => hcontrol input hi hclose⟩

theorem vectorContinuityToMultivariableLimit {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m : M.Value) (hv : M.mem (F.callValue f point) (realVectorSetValue m))
    (hc : VectorMultivariableContinuousAtValue M f point n m)
    (ha : MultivariableAccumulationValue M (F.domainValue f) point n) :
    HasMultivariableVectorLimitValue M f point n m (F.callValue f point) := by
  refine ⟨hv,ha,?_⟩
  intro epsilon he
  obtain ⟨delta,hd,hcontrol⟩ := hc epsilon he
  exact ⟨delta,hd,fun input hi _ hclose => hcontrol input hi hclose⟩

theorem scalarMultivariableLimitToContinuity {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (hf : RealMultivariableFunctionValue M f n)
    (hn : M.mem n (M.standard .natural)) (hp : M.mem point (realVectorSetValue n))
    (hl : HasMultivariableScalarLimitValue M f point n value) (heq : F.callValue f point=value) :
    ScalarMultivariableContinuousAtValue M f point n := by
  classical
  obtain ⟨signature,hfn,hinputs,_⟩ := hf
  obtain ⟨r,hr,_,he⟩ := hl
  intro epsilon h_epsilon
  obtain ⟨delta,hd,hcontrol⟩ := he epsilon h_epsilon
  refine ⟨delta,hd,?_⟩
  intro input hi hclose
  by_cases same : input=point
  · subst input
    rw [heq,hr,scalarError_numbers,sub_self,abs_zero,Complex.ofReal_zero]
    exact positiveRealAboveZero epsilon h_epsilon
  · have hv : M.mem input (realVectorSetValue n) :=
      hinputs input ((F.domainValue_eq signature.domain_isSet hfn) ▸ hi)
    have positive := multivariableDistancePositiveOfNe input point n hn hv hp same
    simpa only [heq] using hcontrol input hi positive hclose

theorem vectorMultivariableLimitToContinuity {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value : M.Value) (hf : VectorMultivariableFunctionValue M f n m)
    (hn : M.mem n (M.standard .natural)) (hp : M.mem point (realVectorSetValue n))
    (hl : HasMultivariableVectorLimitValue M f point n m value) (heq : F.callValue f point=value) :
    VectorMultivariableContinuousAtValue M f point n m := by
  classical
  obtain ⟨signature,hfn,hinputs,_⟩ := hf
  intro epsilon h_epsilon
  obtain ⟨delta,hd,hcontrol⟩ := hl.2.2 epsilon h_epsilon
  refine ⟨delta,hd,?_⟩
  intro input hi hclose
  by_cases same : input=point
  · subst input
    rw [heq,multivariableDistanceSelf value m hl.1]
    exact positiveRealAboveZero epsilon h_epsilon
  · have hv : M.mem input (realVectorSetValue n) :=
      hinputs input ((F.domainValue_eq signature.domain_isSet hfn) ▸ hi)
    have positive := multivariableDistancePositiveOfNe input point n hn hv hp same
    simpa only [heq] using hcontrol input hi positive hclose

end Litex
