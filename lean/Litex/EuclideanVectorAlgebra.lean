import Litex.MultivariableContinuity
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Litex
universe u

private noncomputable def vectorObserved {M : Semantics.{u}} [F : FunctionSemantics M]
    (s : Finset M.Value) (a : M.Value) : EuclideanSpace ℝ s :=
  WithLp.toLp 2 (fun k => observeRealValue (F.callValue a k))

private theorem observedReal_spec {M : Semantics.{u}} (a : M.Value)
    (ha : M.mem a (M.standard .real)) : a=M.number (observeRealValue a : ℂ) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  rw [hr,observeRealValue_number]

private theorem vectorDistanceObserved {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b m : M.Value)
    (finiteIndices : (memberSet (closedRangeValue (M.number 1) m)).Finite)
    (ha : M.mem a (realVectorSetValue m)) (hb : M.mem b (realVectorSetValue m)) :
    multivariableDistanceValue a b m = M.number
      (dist (vectorObserved finiteIndices.toFinset a)
        (vectorObserved finiteIndices.toFinset b) : ℂ) := by
  classical
  let D := F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)
  have returns : ∀ k, M.mem k D → M.mem
      (M.subValue (F.callValue a k) (F.callValue b k)) (M.standard .real) := by
    intro k hk
    obtain ⟨r,hr⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ ha hk)
    obtain ⟨s,hs⟩ := (M.real_members _).mp (F.call_mem _ _ _ _ hb hk)
    rw [hr,hs,M.sub_numbers,←Complex.ofReal_sub]
    exact (M.real_members _).mpr ⟨r-s,rfl⟩
  have entry : ∀ k ∈ finiteIndices.toFinset,
      NativeBridge.complexValue (F.callValue (multivariableDifferenceValue a b m) k) =
        ((observeRealValue (F.callValue a k)-observeRealValue (F.callValue b k) : ℝ) : ℂ) := by
    intro k hk
    have hd : M.mem k D := (F.sep_members _ _ _).mpr ⟨finiteIndices.mem_toFinset.mp hk,True.intro⟩
    rw [multivariableDifferenceValue,F.call_graphValue _ _ _ returns _ hd,
      observedReal_spec _ (F.call_mem _ _ _ _ ha hd),
      observedReal_spec _ (F.call_mem _ _ _ _ hb hd),M.sub_numbers,
      NativeBridge.complexValue_number,←Complex.ofReal_sub]
    simp only [observeRealValue_number]
  have sumEq : finiteAggregateValue false (closedRangeValue (M.number 1) m)
      (fun k => ((‖NativeBridge.complexValue (F.callValue (multivariableDifferenceValue a b m) k)‖^2 : ℝ) : ℂ)) =
      ((∑ k : finiteIndices.toFinset,
        dist (vectorObserved finiteIndices.toFinset a k)
          (vectorObserved finiteIndices.toFinset b k)^2 : ℝ) : ℂ) := by
    unfold finiteAggregateValue
    rw [dif_pos finiteIndices]
    simp only [Bool.false_eq_true,↓reduceIte,vectorObserved,WithLp.ofLp_toLp,Real.dist_eq]
    rw [Finset.sum_coe_sort finiteIndices.toFinset
      (fun k => |observeRealValue (F.callValue a k)-observeRealValue (F.callValue b k)|^2)]
    calc
      _ = ∑ k ∈ finiteIndices.toFinset,
          (((|observeRealValue (F.callValue a k)-observeRealValue (F.callValue b k)|^2 : ℝ)) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [entry k hk,Complex.norm_real,Real.norm_eq_abs]
      _ = _ := (map_sum Complex.ofRealHom _ finiteIndices.toFinset).symm
  unfold multivariableDistanceValue
  rw [sumEq,sqrtValue_number,EuclideanSpace.dist_eq]

private def vectorBinaryEntry {M : Semantics.{u}} (subtract : Bool) (a b : M.Value) : M.Value :=
  if subtract then M.subValue a b else M.addValue a b

private theorem vectorObservedBinary {M : Semantics.{u}} [F : FunctionSemantics M]
    (subtract : Bool) (s : Finset M.Value) (a b c m : M.Value)
    (hs : ∀ k ∈ s, M.mem k (closedRangeValue (M.number 1) m))
    (ha : M.mem a (realVectorSetValue m)) (hb : M.mem b (realVectorSetValue m))
    (formula : ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue c k=vectorBinaryEntry subtract (F.callValue a k) (F.callValue b k)) :
    vectorObserved s c =
      if subtract then vectorObserved s a-vectorObserved s b
      else vectorObserved s a+vectorObserved s b := by
  apply PiLp.ext
  intro k
  have hd : M.mem (k : M.Value)
      (F.sepValue (closedRangeValue (M.number 1) m) (fun _ => True)) :=
    (F.sep_members _ _ _).mpr ⟨hs k k.property,True.intro⟩
  cases subtract
  · change observeRealValue (F.callValue c k)=
      observeRealValue (F.callValue a k)+observeRealValue (F.callValue b k)
    rw [formula _ (hs k k.property)]
    simp only [vectorBinaryEntry,Bool.false_eq_true,↓reduceIte]
    rw [observedReal_spec _ (F.call_mem _ _ _ _ ha hd),
      observedReal_spec _ (F.call_mem _ _ _ _ hb hd),M.add_numbers,
      ←Complex.ofReal_add,observeRealValue_number]
    simp only [observeRealValue_number]
  · change observeRealValue (F.callValue c k)=
      observeRealValue (F.callValue a k)-observeRealValue (F.callValue b k)
    rw [formula _ (hs k k.property)]
    simp only [vectorBinaryEntry,↓reduceIte]
    rw [observedReal_spec _ (F.call_mem _ _ _ _ ha hd),
      observedReal_spec _ (F.call_mem _ _ _ _ hb hd),M.sub_numbers,
      ←Complex.ofReal_sub,observeRealValue_number]
    simp only [observeRealValue_number]

private def vectorControl {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain f point n m value : M.Value) (allowed : M.Value → Prop) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, In delta RPos ∧
      ∀ x, M.mem x domain → allowed x →
        RealLtValue M (multivariableDistanceValue x point n) (denote delta) →
        RealLtValue M (multivariableDistanceValue (F.callValue f x) value m) epsilon

private theorem vectorRadiusMonotone {M : Semantics.{u}} {distance : M.Value} {r s : ℝ}
    (h : r≤s) (near : RealLtValue M distance (M.number (r : ℂ))) :
    RealLtValue M distance (M.number (s : ℂ)) := by
  obtain ⟨a,b,ha,hb,hab⟩ := near
  have hb' : b=r := Complex.ofReal_injective (M.number_injective hb).symm
  exact ⟨a,s,ha,rfl,(hb' ▸ hab).trans_le h⟩

private theorem vectorControlBinary {M : Semantics.{u}} [F : FunctionSemantics M]
    (subtract : Bool) (domain f g h point n m a b c : M.Value) (allowed : M.Value → Prop)
    (hm : M.mem m (M.standard .natural))
    (hf : ∀ x, M.mem x domain → M.mem (F.callValue f x) (realVectorSetValue m))
    (hg : ∀ x, M.mem x domain → M.mem (F.callValue g x) (realVectorSetValue m))
    (hh : ∀ x, M.mem x domain → M.mem (F.callValue h x) (realVectorSetValue m))
    (ha : M.mem a (realVectorSetValue m)) (hb : M.mem b (realVectorSetValue m))
    (hc : M.mem c (realVectorSetValue m))
    (formula : ∀ x, M.mem x domain → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=vectorBinaryEntry subtract
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (target : ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue c k=vectorBinaryEntry subtract (F.callValue a k) (F.callValue b k))
    (first : vectorControl domain f point n m a allowed)
    (second : vectorControl domain g point n m b allowed) :
    vectorControl domain h point n m c allowed := by
  classical
  let length := semanticObject m (M.member_isSet hm)
  have finiteIndices : (memberSet (closedRangeValue (M.number 1) m)).Finite :=
    matrixIndexFinite length hm
  let s := finiteIndices.toFinset
  have hs : ∀ k ∈ s, M.mem k (closedRangeValue (M.number 1) m) :=
    fun _ hk => finiteIndices.mem_toFinset.mp hk
  intro epsilon he
  obtain ⟨_,e,he,hepos⟩ := (positiveReal_members _).mp he
  have halfMem : M.mem (M.number ((e/2 : ℝ) : ℂ)) (denote (RPos (M := M))) :=
    (positiveReal_members _).mpr
      ⟨(M.real_members _).mpr ⟨e/2,rfl⟩,e/2,rfl,half_pos hepos⟩
  obtain ⟨d,hd,hfirst⟩ := first _ halfMem
  obtain ⟨eta,heta,hsecond⟩ := second _ halfMem
  obtain ⟨_,dr,hdr,hdpos⟩ := (positiveReal_members _).mp hd
  obtain ⟨_,er,her,hepos'⟩ := (positiveReal_members _).mp heta
  let radius := Min.min dr er
  have radiusPos : 0<radius := lt_min hdpos hepos'
  have radiusMem : M.mem (M.number (radius : ℂ)) (M.standard .real) :=
    (M.real_members _).mpr ⟨radius,rfl⟩
  let delta := semanticObject (M.number (radius : ℂ)) (M.member_isSet radiusMem)
  refine ⟨delta,(positiveReal_members _).mpr ⟨radiusMem,radius,rfl,radiusPos⟩,?_⟩
  intro x hx hallowed near
  have nearFirst : RealLtValue M (multivariableDistanceValue x point n) (denote d) := by
    rw [hdr]
    exact vectorRadiusMonotone (min_le_left dr er) near
  have nearSecond : RealLtValue M (multivariableDistanceValue x point n) (denote eta) := by
    rw [her]
    exact vectorRadiusMonotone (min_le_right dr er) near
  have boundFirst := hfirst x hx hallowed nearFirst
  have boundSecond := hsecond x hx hallowed nearSecond
  rw [vectorDistanceObserved _ _ m finiteIndices (hf x hx) ha,realLtValue_numbers] at boundFirst
  rw [vectorDistanceObserved _ _ m finiteIndices (hg x hx) hb,realLtValue_numbers] at boundSecond
  rw [he,vectorDistanceObserved _ _ m finiteIndices (hh x hx) hc,realLtValue_numbers]
  have formulaObserved := vectorObservedBinary subtract s _ _ _ m hs (hf x hx) (hg x hx) (formula x hx)
  have targetObserved := vectorObservedBinary subtract s a b c m hs ha hb target
  change dist (vectorObserved s (F.callValue h x)) (vectorObserved s c)<e
  rw [formulaObserved,targetObserved]
  have triangle : (if subtract then
      dist (vectorObserved s (F.callValue f x)-vectorObserved s (F.callValue g x))
        (vectorObserved s a-vectorObserved s b)
    else dist (vectorObserved s (F.callValue f x)+vectorObserved s (F.callValue g x))
        (vectorObserved s a+vectorObserved s b)) ≤
      dist (vectorObserved s (F.callValue f x)) (vectorObserved s a)+
        dist (vectorObserved s (F.callValue g x)) (vectorObserved s b) := by
    cases subtract
    · exact dist_add_add_le _ _ _ _
    · exact dist_sub_sub_le _ _ _ _
  cases subtract <;> simp only [Bool.false_eq_true,↓reduceIte] at * <;>
    linarith only [triangle,boundFirst,boundSecond]

private theorem vectorLimitBinary {M : Semantics.{u}} [F : FunctionSemantics M]
    (subtract : Bool) (f g h point n m a b c : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (domainF : F.domainValue f=F.domainValue h) (domainG : F.domainValue g=F.domainValue h)
    (hc : M.mem c (realVectorSetValue m))
    (formula : ∀ x, M.mem x (F.domainValue h) → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=vectorBinaryEntry subtract
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (target : ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue c k=vectorBinaryEntry subtract (F.callValue a k) (F.callValue b k))
    (first : HasMultivariableVectorLimitValue M f point n m a)
    (second : HasMultivariableVectorLimitValue M g point n m b) :
    HasMultivariableVectorLimitValue M h point n m c := by
  refine ⟨hc,domainF ▸ first.2.1,?_⟩
  have controlF : vectorControl (F.domainValue h) f point n m a
      (fun x => RealLtValue M (M.number 0) (multivariableDistanceValue x point n)) := by
    intro epsilon he
    obtain ⟨delta,hd,hcontrol⟩ := first.2.2 epsilon he
    exact ⟨delta,hd,fun x hx positive near => hcontrol x (domainF.symm ▸ hx) positive near⟩
  have controlG : vectorControl (F.domainValue h) g point n m b
      (fun x => RealLtValue M (M.number 0) (multivariableDistanceValue x point n)) := by
    intro epsilon he
    obtain ⟨delta,hd,hcontrol⟩ := second.2.2 epsilon he
    exact ⟨delta,hd,fun x hx positive near => hcontrol x (domainG.symm ▸ hx) positive near⟩
  exact vectorControlBinary subtract (F.domainValue h) f g h point n m a b c _ hm
    (fun x hx => multivariableVectorFunctionReturns f n m x hf (domainF.symm ▸ hx))
    (fun x hx => multivariableVectorFunctionReturns g n m x hg (domainG.symm ▸ hx))
    (fun x hx => multivariableVectorFunctionReturns h n m x hh hx)
    first.1 second.1 hc formula target controlF controlG

private theorem vectorContinuousBinary {M : Semantics.{u}} [F : FunctionSemantics M]
    (subtract : Bool) (f g h point n m : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (domainF : F.domainValue f=F.domainValue h) (domainG : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=vectorBinaryEntry subtract
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (first : VectorMultivariableContinuousAtValue M f point n m)
    (second : VectorMultivariableContinuousAtValue M g point n m) :
    VectorMultivariableContinuousAtValue M h point n m := by
  have controlF : vectorControl (F.domainValue h) f point n m (F.callValue f point) (fun _ => True) := by
    intro epsilon he
    obtain ⟨delta,hd,hcontrol⟩ := first epsilon he
    exact ⟨delta,hd,fun x hx _ near => hcontrol x (domainF.symm ▸ hx) near⟩
  have controlG : vectorControl (F.domainValue h) g point n m (F.callValue g point) (fun _ => True) := by
    intro epsilon he
    obtain ⟨delta,hd,hcontrol⟩ := second epsilon he
    exact ⟨delta,hd,fun x hx _ near => hcontrol x (domainG.symm ▸ hx) near⟩
  have control := vectorControlBinary subtract (F.domainValue h) f g h point n m
    (F.callValue f point) (F.callValue g point) (F.callValue h point) (fun _ => True) hm
    (fun x hx => multivariableVectorFunctionReturns f n m x hf (domainF.symm ▸ hx))
    (fun x hx => multivariableVectorFunctionReturns g n m x hg (domainG.symm ▸ hx))
    (fun x hx => multivariableVectorFunctionReturns h n m x hh hx)
    (multivariableVectorFunctionReturns f n m point hf (domainF.symm ▸ hp))
    (multivariableVectorFunctionReturns g n m point hg (domainG.symm ▸ hp))
    (multivariableVectorFunctionReturns h n m point hh hp)
    formula (formula point hp) controlF controlG
  intro epsilon he
  obtain ⟨delta,hd,hcontrol⟩ := control epsilon he
  exact ⟨delta,hd,fun x hx near => hcontrol x hx True.intro near⟩

theorem vectorMultivariableLimitAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (domainF : F.domainValue f=F.domainValue h) (domainG : F.domainValue g=F.domainValue h)
    (hc : M.mem c (realVectorSetValue m))
    (formula : ∀ x, M.mem x (F.domainValue h) → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=M.addValue
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (target : ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue c k=M.addValue (F.callValue a k) (F.callValue b k))
    (first : HasMultivariableVectorLimitValue M f point n m a)
    (second : HasMultivariableVectorLimitValue M g point n m b) :
    HasMultivariableVectorLimitValue M h point n m c :=
  vectorLimitBinary false f g h point n m a b c hm hf hg hh domainF domainG hc
    formula target first second

theorem vectorMultivariableLimitSubtract {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m a b c : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (domainF : F.domainValue f=F.domainValue h) (domainG : F.domainValue g=F.domainValue h)
    (hc : M.mem c (realVectorSetValue m))
    (formula : ∀ x, M.mem x (F.domainValue h) → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=M.subValue
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (target : ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue c k=M.subValue (F.callValue a k) (F.callValue b k))
    (first : HasMultivariableVectorLimitValue M f point n m a)
    (second : HasMultivariableVectorLimitValue M g point n m b) :
    HasMultivariableVectorLimitValue M h point n m c :=
  vectorLimitBinary true f g h point n m a b c hm hf hg hh domainF domainG hc
    formula target first second

theorem vectorMultivariableContinuousAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (domainF : F.domainValue f=F.domainValue h) (domainG : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=M.addValue
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (first : VectorMultivariableContinuousAtValue M f point n m)
    (second : VectorMultivariableContinuousAtValue M g point n m) :
    VectorMultivariableContinuousAtValue M h point n m :=
  vectorContinuousBinary false f g h point n m hm hf hg hh domainF domainG hp
    formula first second

theorem vectorMultivariableContinuousSubtract {M : Semantics.{u}} [F : FunctionSemantics M]
    (f g h point n m : M.Value)
    (hm : M.mem m (M.standard .natural))
    (hf : VectorMultivariableFunctionValue M f n m)
    (hg : VectorMultivariableFunctionValue M g n m)
    (hh : VectorMultivariableFunctionValue M h n m)
    (domainF : F.domainValue f=F.domainValue h) (domainG : F.domainValue g=F.domainValue h)
    (hp : M.mem point (F.domainValue h))
    (formula : ∀ x, M.mem x (F.domainValue h) → ∀ k, M.mem k (closedRangeValue (M.number 1) m) →
      F.callValue (F.callValue h x) k=M.subValue
        (F.callValue (F.callValue f x) k) (F.callValue (F.callValue g x) k))
    (first : VectorMultivariableContinuousAtValue M f point n m)
    (second : VectorMultivariableContinuousAtValue M g point n m) :
    VectorMultivariableContinuousAtValue M h point n m :=
  vectorContinuousBinary true f g h point n m hm hf hg hh domainF domainG hp
    formula first second

end Litex
