import Litex.Antiderivative

open Filter
open scoped Topology
universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

-- The compiler must prove this from the original R/open-interval formation.
def RealRegionInteriorValue (M : Semantics.{u}) (region : M.Value) : Prop :=
  ∀ point, M.mem point region → ∃ p : ℝ, point=M.number (p : ℂ) ∧
    ∃ radius : ℝ, 0<radius ∧ ∀ x : ℝ, |x-p|<radius →
      M.mem (M.number (x : ℂ)) region

omit F in
theorem realLineRegionInterior : RealRegionInteriorValue M (M.standard .real) := by
  intro point member
  obtain ⟨p,hp⟩ := (M.real_members _).mp member
  exact ⟨p,hp,1,zero_lt_one,fun x _ => (M.real_members _).mpr ⟨x,rfl⟩⟩

theorem realOpenIntervalRegionInterior (a b : M.Value) :
    RealRegionInteriorValue M
      (F.sepValue (M.standard .real) (fun x => realBound false a x ∧ realBound false x b)) := by
  intro point member
  obtain ⟨realPoint,left,right⟩ := (F.sep_members _ _ _).mp member
  obtain ⟨p,hp⟩ := (M.real_members _).mp realPoint
  obtain ⟨lower,pLower,ha,hpLower,lowerBound⟩ := left
  obtain ⟨pUpper,upper,hpUpper,hb,upperBound⟩ := right
  have lowerEqual : pLower=p := Complex.ofReal_injective (M.number_injective (hpLower.symm.trans hp))
  have upperEqual : pUpper=p := Complex.ofReal_injective (M.number_injective (hpUpper.symm.trans hp))
  subst pLower
  subst pUpper
  refine ⟨p,hp,Min.min (p-lower) (upper-p),lt_min (sub_pos.mpr lowerBound) (sub_pos.mpr upperBound),?_⟩
  intro x near
  apply (F.sep_members _ _ _).mpr
  refine ⟨(M.real_members _).mpr ⟨x,rfl⟩,⟨lower,x,ha,rfl,?_⟩,⟨x,upper,rfl,hb,?_⟩⟩
  · have := (abs_lt.mp near).1
    have := min_le_left (p-lower) (upper-p)
    linarith
  · have := (abs_lt.mp near).2
    have := min_le_right (p-lower) (upper-p)
    linarith

theorem semanticDerivativeOfSourceCandidate
    (f point coefficient : M.Value) (p : ℝ)
    (hf : RealFunctionValue M f) (hp : point=M.number (p : ℂ))
    (h : HasDerivativeAtValue M f point coefficient) :
    SemanticDerivativeAtValue M
      (fun x => F.callValue f (M.number (x : ℂ))) p coefficient := by
  obtain ⟨q,d,hq,hd,hi,he⟩ := h
  have equal : q=p := Complex.ofReal_injective (M.number_injective (hq.symm.trans hp))
  subst q
  refine ⟨d,hd,observeRealFunction f,?_,(derivativeEpsilon_iff_hasDerivAt f p d hi).mp he⟩
  obtain ⟨radius,hradius,hnear⟩ := hi
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨radius,hradius,?_⟩
  intro x hx
  exact observeRealFunction_spec f hf x (hnear x (by simpa only [Real.dist_eq] using hx))

theorem derivativeOfLocalSemanticFormula
    (f point coefficient : M.Value) (p : ℝ) (raw : ℝ → M.Value)
    (hp : point=M.number (p : ℂ)) (hi : DerivativeInteriorValue M f p)
    (hbody : (fun x : ℝ => F.callValue f (M.number (x : ℂ))) =ᶠ[𝓝 p] raw)
    (h : SemanticDerivativeAtValue M raw p coefficient) :
    HasDerivativeAtValue M f point coefficient := by
  obtain ⟨d,hd,native,hnative,hderivative⟩ := h
  refine ⟨p,d,hp,hd,hi,?_⟩
  apply (derivativeEpsilon_iff_hasDerivAt f p d hi).mpr
  apply hderivative.congr_of_eventuallyEq
  filter_upwards [hbody,hnative] with x hbody hnative
  unfold observeRealFunction
  rw [hbody,hnative,observeRealValue_number]

theorem derivativeInRegionOfSemanticFormula
    (f point coefficient region : M.Value) (p radius : ℝ) (raw : ℝ → M.Value)
    (hp : point=M.number (p : ℂ)) (hradius : 0<radius)
    (hnear : ∀ x : ℝ, |x-p|<radius → M.mem (M.number (x : ℂ)) region)
    (cover : ∀ x, M.mem x region → M.mem x (F.domainValue f))
    (equal : ∀ x : ℝ, M.mem (M.number (x : ℂ)) region →
      F.callValue f (M.number (x : ℂ))=raw x)
    (h : SemanticDerivativeAtValue M raw p coefficient) :
    HasDerivativeAtValue M f point coefficient := by
  apply derivativeOfLocalSemanticFormula f point coefficient p raw hp
    ⟨radius,hradius,fun x hx => cover _ (hnear x hx)⟩ _ h
  apply Metric.eventually_nhds_iff.mpr
  exact ⟨radius,hradius,fun x hx => equal x (hnear x (by simpa only [Real.dist_eq] using hx))⟩

theorem antiderivativeShiftFunction
    (primitive function result region constant : M.Value)
    (realPrimitive : RealFunctionValue M primitive)
    (interior : RealRegionInteriorValue M region)
    (cover : ∀ x, M.mem x region → M.mem x (F.domainValue result))
    (constantReal : M.mem constant (M.standard .real))
    (source : IsAntiderivativeOnValue M primitive function region)
    (equal : ∀ x, M.mem x region →
      F.callValue result x=M.addValue (F.callValue primitive x) constant) :
    IsAntiderivativeOnValue M result function region := by
  intro point member
  obtain ⟨p,hp,radius,hradius,hnear⟩ := interior point member
  have derivative := semanticDerivativeOfSourceCandidate primitive point
    (F.callValue function point) p realPrimitive hp (source point member)
  have summed := semanticDerivativeAdd
    (fun x : ℝ => F.callValue primitive (M.number (x : ℂ))) (fun _ => constant) p
    (F.callValue function point) (M.number 0) derivative
    (semanticDerivativeConstant constant p constantReal)
  have final : SemanticDerivativeAtValue M
      (fun x : ℝ => M.addValue (F.callValue primitive (M.number (x : ℂ))) constant)
      p (F.callValue function point) := by
    obtain ⟨_,d,_,hd,_,_⟩ := source point member
    simpa only [hd,M.add_numbers,add_zero] using summed
  exact derivativeInRegionOfSemanticFormula result point _ region p radius _ hp hradius
    hnear cover (fun x hx => equal _ hx) final

theorem antiderivativeAddFunctions
    (first firstValue second secondValue result resultValue region : M.Value)
    (realFirst : RealFunctionValue M first) (realSecond : RealFunctionValue M second)
    (interior : RealRegionInteriorValue M region)
    (cover : ∀ x, M.mem x region → M.mem x (F.domainValue result))
    (sourceFirst : IsAntiderivativeOnValue M first firstValue region)
    (sourceSecond : IsAntiderivativeOnValue M second secondValue region)
    (primitiveEqual : ∀ x, M.mem x region →
      F.callValue result x=M.addValue (F.callValue first x) (F.callValue second x))
    (valueEqual : ∀ x, M.mem x region →
      F.callValue resultValue x=M.addValue (F.callValue firstValue x) (F.callValue secondValue x)) :
    IsAntiderivativeOnValue M result resultValue region := by
  intro point member
  obtain ⟨p,hp,radius,hradius,hnear⟩ := interior point member
  have derivativeFirst := semanticDerivativeOfSourceCandidate first point
    (F.callValue firstValue point) p realFirst hp (sourceFirst point member)
  have derivativeSecond := semanticDerivativeOfSourceCandidate second point
    (F.callValue secondValue point) p realSecond hp (sourceSecond point member)
  rw [valueEqual point member]
  exact derivativeInRegionOfSemanticFormula result point _ region p radius _ hp hradius hnear cover
    (fun x hx => primitiveEqual _ hx)
    (semanticDerivativeAdd (fun x : ℝ => F.callValue first (M.number (x : ℂ)))
      (fun x : ℝ => F.callValue second (M.number (x : ℂ))) p _ _ derivativeFirst derivativeSecond)

theorem antiderivativeScaleFunctions
    (primitive function result resultValue region constant : M.Value)
    (realPrimitive : RealFunctionValue M primitive)
    (interior : RealRegionInteriorValue M region)
    (cover : ∀ x, M.mem x region → M.mem x (F.domainValue result))
    (constantReal : M.mem constant (M.standard .real))
    (source : IsAntiderivativeOnValue M primitive function region)
    (primitiveEqual : ∀ x, M.mem x region →
      F.callValue result x=M.mulValue constant (F.callValue primitive x))
    (valueEqual : ∀ x, M.mem x region →
      F.callValue resultValue x=M.mulValue constant (F.callValue function x)) :
    IsAntiderivativeOnValue M result resultValue region := by
  intro point member
  obtain ⟨p,hp,radius,hradius,hnear⟩ := interior point member
  have derivative := semanticDerivativeOfSourceCandidate primitive point
    (F.callValue function point) p realPrimitive hp (source point member)
  rw [valueEqual point member]
  exact derivativeInRegionOfSemanticFormula result point _ region p radius _ hp hradius hnear cover
    (fun x hx => primitiveEqual _ hx)
    (semanticDerivativeScale (fun x : ℝ => F.callValue primitive (M.number (x : ℂ))) p
      constant _ constantReal derivative)

end Litex
