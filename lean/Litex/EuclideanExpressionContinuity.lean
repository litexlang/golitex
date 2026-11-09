import Litex.MultivariableContinuityLimit

open Filter
open scoped Topology

namespace Litex
universe u

private def euclideanNeighborhood {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (radius : ℝ) : Set M.Value :=
  {x | M.mem x domain ∧
    RealLtValue M (multivariableDistanceValue x point dimension) (M.number (radius : ℂ))}

/-- The unpunctured neighborhood filter on the actual source domain. -/
def EuclideanSourceFilter {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) : Filter M.Value :=
  ⨅ radius : ℝ, ⨅ (_ : 0 < radius),
    Filter.principal (euclideanNeighborhood domain point dimension radius)

private theorem euclideanRadiusMono {M : Semantics.{u}} {distance : M.Value} {r s : ℝ}
    (h : r ≤ s) (near : RealLtValue M distance (M.number (r : ℂ))) :
    RealLtValue M distance (M.number (s : ℂ)) := by
  obtain ⟨a,b,ha,hb,hab⟩ := near
  have hb' : b = r := Complex.ofReal_injective (M.number_injective hb).symm
  exact ⟨a,s,ha,rfl,(hb' ▸ hab).trans_le h⟩

private theorem euclideanSourceBasis {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) :
    (EuclideanSourceFilter domain point dimension).HasBasis (fun radius : ℝ => 0 < radius)
      (euclideanNeighborhood domain point dimension) := by
  apply Filter.hasBasis_biInf_principal'
  · intro r hr s hs
    refine ⟨Min.min r s,lt_min hr hs,?_,?_⟩
    · intro x hx
      exact ⟨hx.1,euclideanRadiusMono (min_le_left r s) hx.2⟩
    · intro x hx
      exact ⟨hx.1,euclideanRadiusMono (min_le_right r s) hx.2⟩
  · exact ⟨1,zero_lt_one⟩

/-- A real-valued expression has joint continuity on the exact source domain.
The value at the point is retained separately, including for an empty filter. -/
def SemanticEuclideanContinuousAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value) : Prop :=
  ∃ native : M.Value → ℝ,
    raw =ᶠ[EuclideanSourceFilter domain point dimension] (fun x => M.number (native x : ℂ)) ∧
    raw point = M.number (native point : ℂ) ∧
    Tendsto native (EuclideanSourceFilter domain point dimension) (𝓝 (native point))

theorem semanticEuclideanContinuousRealAtPoint {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    M.mem (raw point) (M.standard .real) := by
  obtain ⟨native,_,hp,_⟩ := h
  exact (M.real_members _).mpr ⟨native point,hp⟩

private theorem euclideanObserveRealSpec {M : Semantics.{u}} (value : M.Value)
    (h : M.mem value (M.standard .real)) : value = M.number (observeRealValue value : ℂ) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp h
  rw [hr,observeRealValue_number]

theorem semanticEuclideanContinuousConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension value : M.Value) (real : M.mem value (M.standard .real)) :
    SemanticEuclideanContinuousAtValue M domain point dimension (fun _ => value) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp real
  exact ⟨fun _ => r,Filter.Eventually.of_forall (fun _ => hr),hr,tendsto_const_nhds⟩

theorem semanticEuclideanContinuousCoordinate {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension index : M.Value)
    (hn : M.mem dimension (M.standard .natural))
    (hp : M.mem point (realVectorSetValue dimension))
    (hinputs : ∀ x, M.mem x domain → M.mem x (realVectorSetValue dimension))
    (hk : M.mem index (closedRangeValue (M.number 1) dimension)) :
    SemanticEuclideanContinuousAtValue M domain point dimension (fun x => F.callValue x index) := by
  have indexMember : M.mem index
      (F.sepValue (closedRangeValue (M.number 1) dimension) (fun _ => True)) :=
    (F.sep_members _ _ _).mpr ⟨hk,True.intro⟩
  refine ⟨fun x => observeRealValue (F.callValue x index),?_,?_,?_⟩
  · apply (euclideanSourceBasis domain point dimension).eventually_iff.mpr
    refine ⟨1,zero_lt_one,?_⟩
    intro x hx
    exact euclideanObserveRealSpec _ (F.call_mem _ _ _ _ (hinputs x hx.1) indexMember)
  · exact euclideanObserveRealSpec _ (F.call_mem _ _ _ _ hp indexMember)
  · rw [Metric.tendsto_nhds]
    intro epsilon he
    apply (euclideanSourceBasis domain point dimension).eventually_iff.mpr
    refine ⟨epsilon,he,?_⟩
    intro x hx
    obtain ⟨r,s,t,hr,hs,hd,hbound⟩ :=
      multivariableDistanceCoordinateBound x point dimension index hn (hinputs x hx.1) hp hk
    have ht : t < epsilon := (realLtValue_numbers _ _).mp (hd ▸ hx.2)
    simpa only [hr,hs,observeRealValue_number,Real.dist_eq] using hbound.trans_lt ht

theorem semanticEuclideanContinuousUnary {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (operation : M.Value → M.Value) (native : ℝ → ℝ)
    (law : ∀ r : ℝ, operation (M.number (r : ℂ)) = M.number (native r : ℂ))
    (continuous : ContinuousAt native (observeRealValue (raw point)))
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension (fun x => operation (raw x)) := by
  obtain ⟨f,hf,hp,hc⟩ := h
  have hp' : observeRealValue (raw point) = f point := by rw [hp,observeRealValue_number]
  rw [hp'] at continuous
  refine ⟨fun x => native (f x),?_,?_,continuous.tendsto.comp hc⟩
  · exact hf.mono fun x hx => by dsimp only; rw [hx,law]
  · dsimp only
    rw [hp,law]

theorem semanticEuclideanContinuousNeg {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension (fun x => M.negValue (raw x)) := by
  apply semanticEuclideanContinuousUnary domain point dimension raw M.negValue (fun r => -r)
  · intro r; rw [M.neg_numbers,←Complex.ofReal_neg]
  · exact continuousAt_id.neg
  · exact h

theorem semanticEuclideanContinuousExp {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => realUnaryValue Real.exp (raw x)) :=
  semanticEuclideanContinuousUnary domain point dimension raw (realUnaryValue Real.exp) Real.exp
    (realUnaryValue_number Real.exp) Real.continuous_exp.continuousAt h

theorem semanticEuclideanContinuousSin {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => realUnaryValue Real.sin (raw x)) :=
  semanticEuclideanContinuousUnary domain point dimension raw (realUnaryValue Real.sin) Real.sin
    (realUnaryValue_number Real.sin) Real.continuous_sin.continuousAt h

theorem semanticEuclideanContinuousCos {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => realUnaryValue Real.cos (raw x)) :=
  semanticEuclideanContinuousUnary domain point dimension raw (realUnaryValue Real.cos) Real.cos
    (realUnaryValue_number Real.cos) Real.continuous_cos.continuousAt h

theorem semanticEuclideanContinuousLn {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (positive : M.mem (raw point) (denote (RPos (M := M))))
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => realUnaryValue Real.log (raw x)) := by
  apply semanticEuclideanContinuousUnary domain point dimension raw (realUnaryValue Real.log) Real.log
    (realUnaryValue_number Real.log) _ h
  obtain ⟨_,r,hr,hrpos⟩ := (positiveReal_members _).mp positive
  have hp : observeRealValue (raw point) = r := by rw [hr,observeRealValue_number]
  rw [hp]
  exact Real.continuousAt_log (ne_of_gt hrpos)

theorem semanticEuclideanContinuousSqrt {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension (fun x => sqrtValue (raw x)) :=
  semanticEuclideanContinuousUnary domain point dimension raw sqrtValue Real.sqrt sqrtValue_number
    Real.continuous_sqrt.continuousAt h

theorem semanticEuclideanContinuousAdd {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw other : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw)
    (k : SemanticEuclideanContinuousAtValue M domain point dimension other) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => M.addValue (raw x) (other x)) := by
  obtain ⟨f,hf,hp,hc⟩ := h
  obtain ⟨g,hg,hq,hd⟩ := k
  refine ⟨fun x => f x + g x,?_,?_,hc.add hd⟩
  · exact (hf.and hg).mono fun x hx => by
      dsimp only; rw [hx.1,hx.2,M.add_numbers,←Complex.ofReal_add]
  · dsimp only
    rw [hp,hq,M.add_numbers,←Complex.ofReal_add]

theorem semanticEuclideanContinuousSub {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw other : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw)
    (k : SemanticEuclideanContinuousAtValue M domain point dimension other) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => M.subValue (raw x) (other x)) := by
  obtain ⟨f,hf,hp,hc⟩ := h
  obtain ⟨g,hg,hq,hd⟩ := k
  refine ⟨fun x => f x - g x,?_,?_,hc.sub hd⟩
  · exact (hf.and hg).mono fun x hx => by
      dsimp only; rw [hx.1,hx.2,M.sub_numbers,←Complex.ofReal_sub]
  · dsimp only
    rw [hp,hq,M.sub_numbers,←Complex.ofReal_sub]

theorem semanticEuclideanContinuousMul {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw other : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw)
    (k : SemanticEuclideanContinuousAtValue M domain point dimension other) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => M.mulValue (raw x) (other x)) := by
  obtain ⟨f,hf,hp,hc⟩ := h
  obtain ⟨g,hg,hq,hd⟩ := k
  refine ⟨fun x => f x * g x,?_,?_,hc.mul hd⟩
  · exact (hf.and hg).mono fun x hx => by
      dsimp only; rw [hx.1,hx.2,M.mul_numbers,←Complex.ofReal_mul]
  · dsimp only
    rw [hp,hq,M.mul_numbers,←Complex.ofReal_mul]

theorem semanticEuclideanContinuousDiv {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw other : M.Value → M.Value)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw)
    (k : SemanticEuclideanContinuousAtValue M domain point dimension other)
    (nonzero : other point ≠ M.number 0) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => M.divValue (raw x) (other x)) := by
  obtain ⟨f,hf,hp,hc⟩ := h
  obtain ⟨g,hg,hq,hd⟩ := k
  have hgp : g point ≠ 0 := by
    intro hz
    apply nonzero
    rw [hq,hz,Complex.ofReal_zero]
  refine ⟨fun x => f x / g x,?_,?_,hc.div hd hgp⟩
  · filter_upwards [hf,hg,hd.eventually (eventually_ne_nhds hgp)] with x hx hy hn
    rw [hx,hy,M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hn),←Complex.ofReal_div]
  · dsimp only
    rw [hp,hq,M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hgp),←Complex.ofReal_div]

theorem semanticEuclideanContinuousPower {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value) (raw : M.Value → M.Value)
    (exponent : M.Value) (power : ℕ) (hn : exponent = M.number (power : ℂ))
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    SemanticEuclideanContinuousAtValue M domain point dimension
      (fun x => M.powValue (raw x) exponent) := by
  obtain ⟨f,hf,hp,hc⟩ := h
  refine ⟨fun x => f x ^ power,?_,?_,hc.pow power⟩
  · exact hf.mono fun x hx => by
      dsimp only; rw [hx,hn,M.pow_numbers_nat,←Complex.ofReal_pow]
  · dsimp only
    rw [hp,hn,M.pow_numbers_nat,←Complex.ofReal_pow]

/-- Convert the checked expression through the original all-domain call equation. -/
theorem scalarMultivariableContinuousOfExpression {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain f point dimension : M.Value) (raw : M.Value → M.Value)
    (hDomain : F.domainValue f = domain) (hp : M.mem point domain)
    (formula : ∀ x, M.mem x domain → F.callValue f x = raw x)
    (h : SemanticEuclideanContinuousAtValue M domain point dimension raw) :
    ScalarMultivariableContinuousAtValue M f point dimension := by
  obtain ⟨native,hraw,hpoint,hlimit⟩ := h
  intro epsilon he
  obtain ⟨_,e,he,hepos⟩ := (positiveReal_members _).mp he
  have near : ∀ᶠ x in EuclideanSourceFilter domain point dimension,
      dist (native x) (native point) < e := (Metric.tendsto_nhds.mp hlimit) e hepos
  obtain ⟨d,hd,hcontrol⟩ :=
    (euclideanSourceBasis domain point dimension).eventually_iff.mp (hraw.and near)
  let delta := semanticObject (M.number (d : ℂ)) (M.member_isSet (numberInRPos (M := M) d hd))
  refine ⟨delta,numberInRPos (M := M) d hd,?_⟩
  intro x hx hclose
  have hxDomain : M.mem x domain := hDomain ▸ hx
  obtain ⟨hxRaw,hbound⟩ := hcontrol ⟨hxDomain,hclose⟩
  rw [formula x hxDomain,formula point hp,hxRaw,hpoint,scalarError_numbers,he,realLtValue_numbers]
  simpa only [Real.dist_eq] using hbound

/-- An actual coordinate gives arbitrarily close distinct points inside an interior ball. -/
theorem multivariableAccumulationOfInterior {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension axis : M.Value)
    (hn : M.mem dimension (M.standard .natural))
    (hp : M.mem point (realVectorSetValue dimension))
    (hk : M.mem axis (closedRangeValue (M.number 1) dimension))
    (hInterior : MultivariableInteriorValue domain point dimension) :
    MultivariableAccumulationValue M domain point dimension := by
  obtain ⟨interiorRadius,hi,interior⟩ := hInterior
  obtain ⟨_,s,hs,hspos⟩ := (positiveReal_members _).mp hi
  intro radius hr
  obtain ⟨_,r,hr,hrpos⟩ := (positiveReal_members _).mp hr
  let step : ℝ := Min.min r s / 2
  have hstep : 0 < step := div_pos (lt_min hrpos hspos) (by norm_num)
  have stepSmall : step < Min.min r s := by dsimp only [step]; linarith [lt_min hrpos hspos]
  have stepR : step < r := stepSmall.trans_le (min_le_left r s)
  have stepS : step < s := stepSmall.trans_le (min_le_right r s)
  let input := coordinatePathValue point dimension axis (M.number (step : ℂ))
  have inputVector : M.mem input (realVectorSetValue dimension) :=
    coordinatePathValueInVector point dimension axis _ hn hp hk ((M.real_members _).mpr ⟨step,rfl⟩)
  have distance : multivariableDistanceValue input point dimension = M.number (step : ℂ) := by
    rw [coordinatePathDistance point dimension axis step hn hp hk,abs_of_pos hstep]
  refine ⟨semanticObject input (M.member_isSet inputVector),?_,?_,?_⟩
  · apply interior input inputVector
    rw [distance,hs]
    exact (realLtValue_numbers _ _).mpr stepS
  · change RealLtValue M (M.number 0) (multivariableDistanceValue input point dimension)
    rw [distance]
    exact ⟨0,step,by simp,rfl,hstep⟩
  · change RealLtValue M (multivariableDistanceValue input point dimension) radius
    rw [distance,hr]
    exact (realLtValue_numbers _ _).mpr stepR

/-- Positive dimension is necessary: a zero-dimensional space has no distinct nearby point. -/
theorem multivariableAccumulationOfVectorDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain point dimension : M.Value)
    (hn : M.mem dimension (denote (NPos (M := M))))
    (hp : M.mem point (realVectorSetValue dimension))
    (hDomain : domain = realVectorSetValue dimension) :
    MultivariableAccumulationValue M domain point dimension := by
  have nat : M.mem dimension (M.standard .natural) := ((F.sep_members _ _ _).mp hn).1
  obtain ⟨size,hsize⟩ := (M.natural_members _).mp nat
  obtain ⟨value,hvalue,hvaluepos⟩ := ((F.sep_members _ _ _).mp hn).2
  have valueSize : value = (size : ℝ) := by
    apply Complex.ofReal_injective
    exact (M.number_injective (hvalue.symm.trans hsize)).trans (Complex.ofReal_natCast size).symm
  have sizePositive : 0 < size := by exact_mod_cast valueSize ▸ hvaluepos
  have axis : M.mem (M.number 1) (closedRangeValue (M.number 1) dimension) := by
    rw [hsize]
    have h := (closedRangeValue_members (M := M) 1 (size : ℤ) (M.number 1)).mpr
      ⟨1,by norm_num,le_rfl,by exact_mod_cast sizePositive⟩
    simpa only [Int.cast_one,Int.cast_natCast] using h
  apply multivariableAccumulationOfInterior domain point dimension (M.number 1) nat hp axis
  refine ⟨semanticObject (M.number 1) (M.member_isSet (numberInRPos (M := M) 1 (by norm_num))),
    numberInRPos (M := M) 1 (by norm_num),?_⟩
  intro input hinput _
  exact hDomain.symm ▸ hinput

end Litex
