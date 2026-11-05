import Litex.Multivariable

open Filter
open scoped Topology
universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

-- Observe the original coordinate path only on the checked local domain.
theorem semanticDerivativeOfPartialCandidate
    (f point n axis value : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem axis (closedRangeValue (M.number 1) n))
    (returnsReal : ∀ x, M.mem x (F.domainValue f) → M.mem (F.callValue f x) (M.standard .real))
    (pointDomain : M.mem point (F.domainValue f))
    (h : HasPartialDerivativeAtValue M f point n axis value) :
    SemanticDerivativeAtValue M
      (fun t => F.callValue f (coordinatePathValue point n axis (M.number (t : ℂ)))) 0 value := by
  obtain ⟨hi,p,r,hp0,hr,_,he⟩ := h
  have pzero : p=0 := Complex.ofReal_injective (M.number_injective (hp0.symm.trans (by simp)))
  subst p
  obtain ⟨radius,hradius,hnear⟩ := hi
  obtain ⟨rad,hrad,hradpos⟩ := NativeBridge.realWitnessOfPositive radius (inRPos_positive radius hradius)
  have pathDomain (t : ℝ) (ht : |t|<rad) :
      M.mem (coordinatePathValue point n axis (M.number (t : ℂ))) (F.domainValue f) := by
    apply hnear _ ((M.real_members _).mpr ⟨t,rfl⟩)
    rw [absValue_number,hrad]
    exact ⟨|t|,rad,rfl,rfl,ht⟩
  let native := fun t : ℝ => observeRealValue (F.callValue f (coordinatePathValue point n axis (M.number (t : ℂ))))
  have spec (t : ℝ) (ht : |t|<rad) :
      F.callValue f (coordinatePathValue point n axis (M.number (t : ℂ)))=M.number (native t : ℂ) :=
    riemannRealObservation (returnsReal _ (pathDomain t ht))
  have zeroPath := coordinatePathValueZero point n axis hn hp hk
  have origin : F.callValue f point=M.number (native 0 : ℂ) := by
    simpa only [Complex.ofReal_zero,zeroPath] using spec 0 (by simpa only [abs_zero] using hradpos)
  refine ⟨r,hr,native,?_,?_⟩
  · apply Metric.eventually_nhds_iff.mpr
    exact ⟨rad,hradpos,fun t ht => spec t (by simpa only [Real.dist_eq,sub_zero] using ht)⟩
  · apply hasDerivAt_iff_tendsto_slope.mpr
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro epsilon hepsilon
    obtain ⟨delta,hdelta,hcontrol⟩ := he epsilon hepsilon
    refine ⟨Min.min delta rad,lt_min hdelta hradpos,?_⟩
    intro input hinput hsmall
    have hne : input≠0 := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hinput
    have hneC : (input : ℂ)≠0 := by exact_mod_cast hne
    have bound : |input|<rad := by
      have := lt_of_lt_of_le hsmall (min_le_right delta rad)
      simpa only [Real.dist_eq,sub_zero] using this
    have laws := partialQuotientGraphLaws f point n axis returnsReal pointDomain
    have sourceInput : M.mem (M.number (input : ℂ)) (F.domainValue (partialQuotientValue f point n axis)) := by
      apply (laws.1 _).mpr
      exact ⟨(M.real_members _).mpr ⟨input,rfl⟩,fun eq => hneC (M.number_injective eq),pathDomain input bound⟩
    have positive : 0<finiteLimitDistance .both 0 input := by
      simpa only [finiteLimitDistance,sub_zero] using abs_pos.mpr hne
    have small : finiteLimitDistance .both 0 input<delta := by
      have := lt_of_lt_of_le hsmall (min_le_left delta rad)
      simpa only [finiteLimitDistance,Real.dist_eq,sub_zero] using this
    obtain ⟨output,houtput,herror⟩ := hcontrol input sourceInput positive small
    rw [laws.2 _ sourceInput,spec input bound,origin,M.sub_numbers,M.div_numbers _ _ hneC,
      ←Complex.ofReal_sub,←Complex.ofReal_div] at houtput
    have quotient : (native input-native 0)/input=output :=
      Complex.ofReal_injective (M.number_injective houtput)
    have slopeEq : slope native 0 input=output := by
      simpa only [slope,smul_eq_mul,vsub_eq_sub,sub_zero,div_eq_mul_inv,mul_comm] using quotient
    rw [slopeEq,Real.dist_eq]
    exact herror

private inductive PartialAlgebraOperation where
  | add | subtract | multiply | divide

private def partialOperation (op : PartialAlgebraOperation) (a b : M.Value) : M.Value :=
  match op with
  | .add => M.addValue a b
  | .subtract => M.subValue a b
  | .multiply => M.mulValue a b
  | .divide => M.divValue a b

private def partialCoefficient (op : PartialAlgebraOperation) (fp gp a b : M.Value) : M.Value :=
  match op with
  | .add => M.addValue a b
  | .subtract => M.subValue a b
  | .multiply => M.addValue (M.mulValue a gp) (M.mulValue fp b)
  | .divide => M.divValue (M.divValue (M.subValue (M.mulValue a gp) (M.mulValue fp b)) gp) gp

private theorem partialAlgebra
    (op : PartialAlgebraOperation) (f g result point n axis a b : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem axis (closedRangeValue (M.number 1) n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M result n)
    (domainG : F.domainValue g=F.domainValue f)
    (domainH : F.domainValue result=F.domainValue f)
    (pointDomain : M.mem point (F.domainValue f))
    (equal : ∀ x, M.mem x (F.domainValue f) →
      F.callValue result x=partialOperation op (F.callValue f x) (F.callValue g x))
    (guard : op=.divide → F.callValue g point≠M.number 0)
    (first : HasPartialDerivativeAtValue M f point n axis a)
    (second : HasPartialDerivativeAtValue M g point n axis b) :
    HasPartialDerivativeAtValue M result point n axis
      (partialCoefficient op (F.callValue f point) (F.callValue g point) a b) := by
  let rawF := fun t : ℝ => F.callValue f (coordinatePathValue point n axis (M.number (t : ℂ)))
  let rawG := fun t : ℝ => F.callValue g (coordinatePathValue point n axis (M.number (t : ℂ)))
  have derivativeF := semanticDerivativeOfPartialCandidate f point n axis a hn hp hk
    (fun x hx => multivariableFunctionReturnsReal f n x hf hx) pointDomain first
  have derivativeG := semanticDerivativeOfPartialCandidate g point n axis b hn hp hk
    (fun x hx => multivariableFunctionReturnsReal g n x hg hx) (domainG.symm ▸ pointDomain) second
  have zeroPath := coordinatePathValueZero point n axis hn hp hk
  have calculus : SemanticDerivativeAtValue M (fun t => partialOperation op (rawF t) (rawG t)) 0
      (partialCoefficient op (F.callValue f point) (F.callValue g point) a b) := by
    cases op with
    | add => exact semanticDerivativeAdd rawF rawG 0 a b derivativeF derivativeG
    | subtract => exact semanticDerivativeSub rawF rawG 0 a b derivativeF derivativeG
    | multiply =>
      simpa only [partialOperation,partialCoefficient,rawF,rawG,Complex.ofReal_zero,zeroPath]
        using semanticDerivativeMul rawF rawG 0 a b derivativeF derivativeG
    | divide =>
      have hne : rawG 0≠M.number 0 := by
        simpa only [rawG,Complex.ofReal_zero,zeroPath] using guard rfl
      simpa only [partialOperation,partialCoefficient,rawF,rawG,Complex.ofReal_zero,zeroPath]
        using semanticDerivativeDiv rawF rawG 0 a b derivativeF derivativeG hne
  have interior : PartialInteriorValue M result point n axis := by
    obtain ⟨radius,hr,hcontrol⟩ := first.1
    exact ⟨radius,hr,fun t ht hs => domainH.symm ▸ hcontrol t ht hs⟩
  apply partialDerivativeOfSemanticPath result point n axis _
    (fun t => partialOperation op (rawF t) (rawG t))
    (fun x hx => multivariableFunctionReturnsReal result n x hh hx)
    (domainH.symm ▸ pointDomain) interior _ _ calculus
  · simpa only [rawF,rawG,Complex.ofReal_zero,zeroPath] using (equal point pointDomain).symm
  · intro t ht
    exact equal _ (domainH ▸ ht)

theorem partialDerivativeAddFunctions
    (f g result point n axis a b : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem axis (closedRangeValue (M.number 1) n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M result n)
    (domainG : F.domainValue g=F.domainValue f)
    (domainH : F.domainValue result=F.domainValue f)
    (pointDomain : M.mem point (F.domainValue f))
    (equal : ∀ x, M.mem x (F.domainValue f) →
      F.callValue result x=M.addValue (F.callValue f x) (F.callValue g x))
    (first : HasPartialDerivativeAtValue M f point n axis a)
    (second : HasPartialDerivativeAtValue M g point n axis b) :
    HasPartialDerivativeAtValue M result point n axis (M.addValue a b) :=
  partialAlgebra .add f g result point n axis a b hn hp hk hf hg hh
    domainG domainH pointDomain equal (by intro impossible; cases impossible) first second

theorem partialDerivativeSubFunctions
    (f g result point n axis a b : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem axis (closedRangeValue (M.number 1) n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M result n)
    (domainG : F.domainValue g=F.domainValue f)
    (domainH : F.domainValue result=F.domainValue f)
    (pointDomain : M.mem point (F.domainValue f))
    (equal : ∀ x, M.mem x (F.domainValue f) →
      F.callValue result x=M.subValue (F.callValue f x) (F.callValue g x))
    (first : HasPartialDerivativeAtValue M f point n axis a)
    (second : HasPartialDerivativeAtValue M g point n axis b) :
    HasPartialDerivativeAtValue M result point n axis (M.subValue a b) :=
  partialAlgebra .subtract f g result point n axis a b hn hp hk hf hg hh
    domainG domainH pointDomain equal (by intro impossible; cases impossible) first second

theorem partialDerivativeMulFunctions
    (f g result point n axis a b : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem axis (closedRangeValue (M.number 1) n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M result n)
    (domainG : F.domainValue g=F.domainValue f)
    (domainH : F.domainValue result=F.domainValue f)
    (pointDomain : M.mem point (F.domainValue f))
    (equal : ∀ x, M.mem x (F.domainValue f) →
      F.callValue result x=M.mulValue (F.callValue f x) (F.callValue g x))
    (first : HasPartialDerivativeAtValue M f point n axis a)
    (second : HasPartialDerivativeAtValue M g point n axis b) :
    HasPartialDerivativeAtValue M result point n axis (M.addValue (M.mulValue a (F.callValue g point)) (M.mulValue (F.callValue f point) b)) :=
  partialAlgebra .multiply f g result point n axis a b hn hp hk hf hg hh
    domainG domainH pointDomain equal (by intro impossible; cases impossible) first second

theorem partialDerivativeDivFunctions
    (f g result point n axis a b : M.Value)
    (hn : M.mem n (M.standard .natural))
    (hp : M.mem point (realVectorSetValue n))
    (hk : M.mem axis (closedRangeValue (M.number 1) n))
    (hf : RealMultivariableFunctionValue M f n)
    (hg : RealMultivariableFunctionValue M g n)
    (hh : RealMultivariableFunctionValue M result n)
    (domainG : F.domainValue g=F.domainValue f)
    (domainH : F.domainValue result=F.domainValue f)
    (pointDomain : M.mem point (F.domainValue f))
    (equal : ∀ x, M.mem x (F.domainValue f) →
      F.callValue result x=M.divValue (F.callValue f x) (F.callValue g x))
    (nonzero : F.callValue g point≠M.number 0)
    (first : HasPartialDerivativeAtValue M f point n axis a)
    (second : HasPartialDerivativeAtValue M g point n axis b) :
    HasPartialDerivativeAtValue M result point n axis (M.divValue (M.divValue (M.subValue (M.mulValue a (F.callValue g point)) (M.mulValue (F.callValue f point) b)) (F.callValue g point)) (F.callValue g point)) :=
  partialAlgebra .divide f g result point n axis a b hn hp hk hf hg hh
    domainG domainH pointDomain equal (fun _ => nonzero) first second

end Litex
