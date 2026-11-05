import Litex.Analysis

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem darbouxNativeEnclosureSums {f p lower upper : M.Value} {a b : ℝ} {n : ℕ}
    (h : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number (n : ℂ)) p lower upper) :
    (darbouxNativeEnclosure h).lowerSum=observeRealValue (riemannStepSumValue (M.number (n : ℂ)) p lower) ∧
    (darbouxNativeEnclosure h).upperSum=observeRealValue (riemannStepSumValue (M.number (n : ℂ)) p upper) := by
  constructor
  · rw [riemannStepSumValue_nat h.2.2.1 h.2.2.2.1,observeRealValue_number]
    rfl
  · rw [riemannStepSumValue_nat h.2.2.1 h.2.2.2.2.1,observeRealValue_number]
    rfl

theorem darbouxEnclosureNativeCompare {f n p lower upper : M.Value} {a b : ℝ}
    (h : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ)) n p lower upper)
    (e : RiemannGeometry.Enclosure (observeRealFunction f) a b) :
    observeRealValue (riemannStepSumValue n p lower) ≤ e.upperSum ∧
    e.lowerSum ≤ observeRealValue (riemannStepSumValue n p upper) := by
  have hn := inNPos_natural (semanticObject n (M.member_isSet h.2.1)) h.2.1
  obtain ⟨nr,hnr⟩ := (M.natural_members n).mp hn
  rw [hnr] at h
  rw [hnr,←(darbouxNativeEnclosureSums h).1,←(darbouxNativeEnclosureSums h).2]
  exact ⟨(darbouxNativeEnclosure h).compare e,e.compare (darbouxNativeEnclosure h)⟩

theorem darbouxApproximationNativeBounds {f v : M.Value} {a b : ℝ}
    (order : a<b)
    (h : DarbouxApproximationValue f (M.number (a : ℂ)) (M.number (b : ℂ)) v)
    (e : RiemannGeometry.Enclosure (observeRealFunction f) a b) :
    e.lowerSum ≤ observeRealValue v ∧ observeRealValue v ≤ e.upperSum := by
  have approximate (epsilon : ℝ) (positive : 0<epsilon) :
      observeRealValue v < e.upperSum+epsilon ∧ e.lowerSum < observeRealValue v+epsilon := by
    obtain ⟨n,_,p,_,l,_,u,_,ls,hls,us,hus,enclosure,lowerEq,upperEq,below,above,gap⟩ :=
      h (M.number (epsilon : ℂ)) (numberInRPos epsilon positive) ((realLtValue_numbers _ _).mpr order)
    have cross := darbouxEnclosureNativeCompare enclosure e
    rw [←lowerEq,←upperEq] at cross
    have below := riemannRealLeObserve below
    have above := riemannRealLeObserve above
    have gap := riemannRealLtObserve gap
    rw [riemannObserveSub hus hls,observeRealValue_number] at gap
    constructor <;> linarith [cross.1,cross.2]
  constructor
  · by_contra below
    have positive : 0<(e.lowerSum-observeRealValue v)/2 := by linarith
    have := (approximate _ positive).2
    linarith
  · by_contra above
    have positive : 0<(observeRealValue v-e.upperSum)/2 := by linarith
    have := (approximate _ positive).1
    linarith

theorem darbouxApproximationAbsBound {f v : M.Value} {a b bound : ℝ}
    (order : a<b)
    (h : DarbouxApproximationValue f (M.number (a : ℂ)) (M.number (b : ℂ)) v)
    (bounded : ∀ x, x ∈ Set.Icc a b → |observeRealFunction f x| ≤ bound) :
    |observeRealValue v| ≤ bound*(b-a) := by
  let e : RiemannGeometry.Enclosure (observeRealFunction f) a b := {
    n := 1
    points := fun k => a+(k : ℝ)*(b-a)
    lower := fun _ => -bound
    upper := fun _ => bound
    ordered := by
      intro i j hij _
      exact add_le_add (le_refl a) (mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ (j : ℝ) from by exact_mod_cast hij) (sub_nonneg.mpr order.le))
    left := by simp only [Nat.cast_zero,zero_mul,add_zero]
    right := by simp only [Nat.cast_one,one_mul,add_sub_cancel]
    lower_bound := by
      intro i hi x hx
      have index : i=0 := by omega
      simp only [index,Nat.cast_zero,zero_mul,add_zero,zero_add,Nat.cast_one,one_mul,add_sub_cancel] at hx
      exact (abs_le.mp (bounded x ⟨hx.1.le,hx.2⟩)).1
    upper_bound := by
      intro i hi x hx
      have index : i=0 := by omega
      simp only [index,Nat.cast_zero,zero_mul,add_zero,zero_add,Nat.cast_one,one_mul,add_sub_cancel] at hx
      exact (abs_le.mp (bounded x ⟨hx.1.le,hx.2⟩)).2
  }
  have limits := darbouxApproximationNativeBounds order h e
  have lower : e.lowerSum = -bound*(b-a) := by
    simp only [e,RiemannGeometry.Enclosure.lowerSum,Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero,zero_add,Nat.cast_one,one_mul,add_sub_cancel]
  have upper : e.upperSum = bound*(b-a) := by
    simp only [e,RiemannGeometry.Enclosure.upperSum,Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero,zero_add,Nat.cast_one,one_mul,add_sub_cancel]
  rw [lower,upper] at limits
  exact abs_le.mpr ⟨by linarith [limits.1],limits.2⟩

theorem riemannIntegralAbsoluteBound (f a b v bound : M.Value)
    (realF : RealFunctionValue M f) (realBound : M.mem bound (M.standard .real))
    (_nonnegative : RealLeValue M (M.number 0) bound)
    (h : HasRiemannIntegralValue M f a b v)
    (bounded : ∀ x, M.mem x (riemannIntervalValue a b) → RealLeValue M (absValue (F.callValue f x)) bound) :
    RealLeValue M (absValue v) (M.mulValue bound (absValue (M.subValue b a))) := by
  obtain ⟨ar,rfl⟩ := (M.real_members a).mp h.2.1
  obtain ⟨br,rfl⟩ := (M.real_members b).mp h.2.2.1
  obtain ⟨vr,rfl⟩ := (M.real_members v).mp h.1
  obtain ⟨kr,rfl⟩ := (M.real_members bound).mp realBound
  rw [absValue_number,M.sub_numbers,←Complex.ofReal_sub,absValue_number,M.mul_numbers,←Complex.ofReal_mul]
  apply (realLeValue_numbers _ _).mpr
  by_cases ends : ar=br
  · have valueZero := h.2.2.2.2.2.1.resolve_left (not_not.mpr (by rw [ends]))
    have zero : vr=0 := Complex.ofReal_injective (M.number_injective valueZero)
    simp only [ends,sub_self,abs_zero,mul_zero,zero,le_refl]
  have order : Min.min ar br < Max.max ar br := by
    rcases lt_or_gt_of_ne ends with left | right
    · simpa only [min_eq_left left.le,max_eq_right left.le] using left
    · simpa only [min_eq_right right.le,max_eq_left right.le] using right
  have approximation := h.2.2.2.2.2.2
  rw [minMaxValue_number,minMaxValue_number,riemannOrientedValue_number] at approximation
  simp only [Bool.false_eq_true,ite_false,ite_true] at approximation
  have nativeBound (x : ℝ) (hx : x ∈ Set.Icc (Min.min ar br) (Max.max ar br)) :
      |observeRealFunction f x| ≤ kr := by
    have interval : M.mem (M.number (x : ℂ)) (riemannIntervalValue (M.number (ar : ℂ)) (M.number (br : ℂ))) := by
      unfold riemannIntervalValue
      rw [minMaxValue_number,minMaxValue_number]
      simp only [Bool.false_eq_true,ite_false,ite_true]
      exact (F.sep_members _ _ _).mpr ⟨(M.real_members _).mpr ⟨x,rfl⟩,
        (realLeValue_numbers _ _).mpr hx.1,(realLeValue_numbers _ _).mpr hx.2⟩
    have bound := bounded _ interval
    rw [observeRealFunction_spec f realF x (h.2.2.2.1 _ interval),absValue_number] at bound
    exact (realLeValue_numbers _ _).mp bound
  have result := darbouxApproximationAbsBound order approximation nativeBound
  simp only [observeRealValue_number] at result
  rw [max_sub_min_eq_abs] at result
  rcases lt_or_gt_of_ne ends with forward | reverse
  · rw [Real.sign_of_pos (sub_pos.mpr forward),one_mul] at result
    exact result
  · rw [Real.sign_of_neg (sub_neg.mpr reverse),neg_one_mul,abs_neg] at result
    exact result
end Litex
