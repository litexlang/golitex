import Litex.Analysis

universe u
namespace Litex.RiemannGeometry

theorem Enclosure.compareLocal {f g : ℝ → ℝ} {a b : ℝ}
    (e : Enclosure f a b) (d : Enclosure g a b)
    (compare : ∀ x, x ∈ Set.Icc a b → f x ≤ g x) : e.lowerSum ≤ d.upperSum := by
  apply partitionLowerUpper e.ordered d.ordered (e.left.trans d.left.symm)
    (e.right.trans d.right.symm) e.lower_bound
  intro i hi x hx
  have start : a ≤ x := by
    rw [←d.left]
    exact le_trans (d.ordered 0 i (by omega) (by omega)) hx.1.le
  have finish : x ≤ b := by
    rw [←d.right]
    exact le_trans hx.2 (d.ordered (i+1) d.n (by omega) le_rfl)
  exact le_trans (compare x ⟨start,finish⟩) (d.upper_bound i hi x hx)
end Litex.RiemannGeometry

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem darbouxLowerUpperLocalComparison {f g p q lower upper lower' upper' : M.Value}
    {a b : ℝ} {n m : ℕ}
    (compare : ∀ x, M.mem x (riemannClosedIntervalValue (M.number (a : ℂ)) (M.number (b : ℂ))) →
      RealLeValue M (F.callValue f x) (F.callValue g x))
    (h : DarbouxEnclosureValue f (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number (n : ℂ)) p lower upper)
    (k : DarbouxEnclosureValue g (M.number (a : ℂ)) (M.number (b : ℂ))
      (M.number (m : ℂ)) q lower' upper') :
    RealLeValue M (riemannStepSumValue (M.number (n : ℂ)) p lower)
      (riemannStepSumValue (M.number (m : ℂ)) q upper') := by
  rw [riemannStepSumValue_nat h.2.2.1 h.2.2.2.1,
    riemannStepSumValue_nat k.2.2.1 k.2.2.2.2.1]
  apply (realLeValue_numbers _ _).mpr
  apply (darbouxNativeEnclosure h).compareLocal (darbouxNativeEnclosure k)
  intro x hx
  have member : M.mem (M.number (x : ℂ))
      (riemannClosedIntervalValue (M.number (a : ℂ)) (M.number (b : ℂ))) :=
    (F.sep_members _ _ _).mpr ⟨(M.real_members _).mpr ⟨x,rfl⟩,
      (realLeValue_numbers _ _).mpr hx.1,(realLeValue_numbers _ _).mpr hx.2⟩
  exact riemannRealLeObserve (compare _ member)

theorem darbouxEnclosureLocalComparison {f g a b n m p q lower upper lower' upper' : M.Value}
    (compare : ∀ x, M.mem x (riemannClosedIntervalValue a b) →
      RealLeValue M (F.callValue f x) (F.callValue g x))
    (h : DarbouxEnclosureValue f a b n p lower upper)
    (k : DarbouxEnclosureValue g a b m q lower' upper') :
    RealLeValue M (riemannStepSumValue n p lower) (riemannStepSumValue m q upper') := by
  obtain ⟨ar,br,ha,hb,_⟩ := h.1
  have hn := inNPos_natural (semanticObject n (M.member_isSet h.2.1)) h.2.1
  have hm := inNPos_natural (semanticObject m (M.member_isSet k.2.1)) k.2.1
  obtain ⟨nr,hnr⟩ := (M.natural_members n).mp hn
  obtain ⟨mr,hmr⟩ := (M.natural_members m).mp hm
  rw [ha,hb,hnr] at h
  rw [ha,hb,hmr] at k
  rw [ha,hb] at compare
  rw [hnr,hmr]
  exact darbouxLowerUpperLocalComparison compare h k

theorem darbouxApproximationLocalCompare {f g a b v w : M.Value}
    (order : RealLtValue M a b)
    (compare : ∀ x, M.mem x (riemannClosedIntervalValue a b) →
      RealLeValue M (F.callValue f x) (F.callValue g x))
    (hv : DarbouxApproximationValue f a b v)
    (hw : DarbouxApproximationValue g a b w) :
    observeRealValue v ≤ observeRealValue w := by
  by_contra hle
  let epsilon := (observeRealValue v-observeRealValue w)/2
  have positive : 0<epsilon := by dsimp [epsilon]; linarith
  obtain ⟨n,_,p,_,l,_,u,_,ls,hls,us,hus,henc,hlsEq,husEq,hl,hu,hgap⟩ :=
    hv (M.number (epsilon : ℂ)) (numberInRPos epsilon positive) order
  obtain ⟨n',_,p',_,l',_,u',_,ls',hls',us',hus',henc',hlsEq',husEq',hl',hu',hgap'⟩ :=
    hw (M.number (epsilon : ℂ)) (numberInRPos epsilon positive) order
  have cross := darbouxEnclosureLocalComparison compare henc henc'
  rw [←hlsEq,←husEq'] at cross
  have cross := riemannRealLeObserve cross
  have hl := riemannRealLeObserve hl
  have hu := riemannRealLeObserve hu
  have hl' := riemannRealLeObserve hl'
  have hu' := riemannRealLeObserve hu'
  have hgap := riemannRealLtObserve hgap
  have hgap' := riemannRealLtObserve hgap'
  rw [riemannObserveSub hus hls,observeRealValue_number] at hgap
  rw [riemannObserveSub hus' hls',observeRealValue_number] at hgap'
  dsimp [epsilon] at hgap hgap'
  linarith

theorem riemannIntegralLocalCompare (f g a b v w : M.Value)
    (order : RealLeValue M a b)
    (compare : ∀ x, M.mem x (riemannClosedIntervalValue a b) →
      RealLeValue M (F.callValue f x) (F.callValue g x))
    (hv : HasRiemannIntegralValue M f a b v)
    (hw : HasRiemannIntegralValue M g a b w) : RealLeValue M v w := by
  by_cases same : a=b
  · have zv := hv.2.2.2.2.2.1.resolve_left (not_not.mpr same)
    have zw := hw.2.2.2.2.2.1.resolve_left (not_not.mpr same)
    exact ⟨0,0,zv,zw,le_rfl⟩
  obtain ⟨ar,rfl⟩ := (M.real_members a).mp hv.2.1
  obtain ⟨br,rfl⟩ := (M.real_members b).mp hv.2.2.1
  obtain ⟨vr,rfl⟩ := (M.real_members v).mp hv.1
  obtain ⟨wr,rfl⟩ := (M.real_members w).mp hw.1
  have nativeOrder : ar<br := lt_of_le_of_ne ((realLeValue_numbers _ _).mp order)
    (fun equal => same (congrArg (fun r : ℝ => M.number (r : ℂ)) equal))
  have hd := hv.2.2.2.2.2.2
  have kd := hw.2.2.2.2.2.2
  rw [minMaxValue_number,minMaxValue_number,riemannOrientedValue_number] at hd kd
  simp only [Bool.false_eq_true,ite_false,ite_true,min_eq_left nativeOrder.le,
    max_eq_right nativeOrder.le,Real.sign_of_pos (sub_pos.mpr nativeOrder),one_mul] at hd kd
  apply (realLeValue_numbers _ _).mpr
  simpa only [observeRealValue_number] using darbouxApproximationLocalCompare
    ((realLtValue_numbers _ _).mpr nativeOrder) compare hd kd
end Litex
