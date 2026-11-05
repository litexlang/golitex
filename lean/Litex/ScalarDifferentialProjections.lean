import Litex.Multivariable

open Filter
open scoped Topology
universe u
namespace Litex

theorem realDerivativeOfLinearError (f : ℝ → ℝ) (d : ℝ)
    (control : ∀ epsilon>0, ∃ delta>0, ∀ h : ℝ,
      0 < |h| → |h|<delta → |f h-f 0-d*h|<epsilon * |h|) :
    HasDerivAt f d 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro epsilon positive
  obtain ⟨delta,hdelta,bound⟩ := control epsilon positive
  refine ⟨delta,hdelta,?_⟩
  intro h nonzero near
  have hne : h≠0 := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using nonzero
  have hpos : 0 < |h| := abs_pos.mpr hne
  have hclose : |h|<delta := by simpa only [Real.dist_eq,sub_zero] using near
  have estimate := bound h hpos hclose
  have identity : (f h-f 0)/h-d=(f h-f 0-d*h)/h := by field_simp
  have slopeEqual : slope f 0 h=(f h-f 0)/h := by
    simp only [slope,smul_eq_mul,vsub_eq_sub,sub_zero,div_eq_mul_inv,mul_comm]
  rw [slopeEqual,Real.dist_eq,identity,abs_div]
  exact (div_lt_iff₀ hpos).mpr estimate

variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem scalarDifferentialPartialCandidate (f point n matrix axis : M.Value)
    (dimension : M.mem n (M.standard .natural))
    (pointVector : M.mem point (realVectorSetValue n))
    (realF : RealMultivariableFunctionValue M f n)
    (pointDomain : M.mem point (F.domainValue f))
    (axisMember : M.mem axis (closedRangeValue (M.number 1) n))
    (source : HasScalarDifferentialAtValue M f point n matrix) :
    HasPartialDerivativeAtValue M f point n axis
      (F.callValue matrix (FiniteFunction.pack2 (M.number 1) axis)) := by
  let raw := fun h : ℝ => F.callValue f (coordinatePathValue point n axis (M.number (h : ℂ)))
  let native := fun h : ℝ => observeRealValue (raw h)
  have returns (input : M.Value) (hinput : M.mem input (F.domainValue f)) :
      M.mem (F.callValue f input) (M.standard .real) :=
    multivariableFunctionReturnsReal f n input realF hinput
  have pathZero : coordinatePathValue point n axis (M.number 0)=point :=
    coordinatePathValueZero point n axis dimension pointVector axisMember
  have rawZero : raw 0=F.callValue f point := by
    dsimp only [raw]
    rw [Complex.ofReal_zero,pathZero]
  have pointValue : F.callValue f point=M.number (native 0 : ℂ) := by
    rw [←rawZero]
    exact riemannRealObservation (by rw [rawZero];exact returns point pointDomain)
  have nearPath := coordinatePathNeighborhoodOfInterior (F.domainValue f) point n axis
    dimension pointVector axisMember source.2.1
  obtain ⟨eta,heta,inDomain⟩ := Metric.eventually_nhds_iff.mp nearPath
  have rowMember : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 1)) := by
    simpa only [Int.cast_one] using (closedRangeValue_members (M := M) 1 1 (M.number 1)).mpr
      ⟨1,by norm_num,le_rfl,le_rfl⟩
  let rows := semanticObject (M.number 1) (M.member_isSet ((M.complex_members _).mpr ⟨1,rfl⟩))
  let cols := semanticObject n (M.member_isSet dimension)
  have coefficientReal := F.call_mem _ _ _ _ source.1
    (matrixDomain_pair rows cols (M.number 1) axis rowMember axisMember)
  obtain ⟨a,coefficient⟩ := (M.real_members _).mp coefficientReal
  have derivative : SemanticDerivativeAtValue M raw 0
      (F.callValue matrix (FiniteFunction.pack2 (M.number 1) axis)) := by
    refine ⟨a,coefficient,native,?_,?_⟩
    · filter_upwards [nearPath] with h hh
      exact riemannRealObservation (returns _ hh)
    · apply realDerivativeOfLinearError
      intro epsilon hepsilon
      obtain ⟨delta,hdelta,bound⟩ := source.2.2 (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
      obtain ⟨dr,hdr,positive⟩ := NativeBridge.realWitnessOfPositive delta (inRPos_positive delta hdelta)
      refine ⟨Min.min dr eta,lt_min positive heta,?_⟩
      intro step hpos hsmall
      have member : M.mem (coordinatePathValue point n axis (M.number (step : ℂ))) (F.domainValue f) :=
        inDomain (by simpa only [Real.dist_eq,sub_zero] using (lt_min_iff.mp hsmall).2)
      have distance := coordinatePathDistance point n axis step dimension pointVector axisMember
      have estimate := bound _ member
        (by rw [distance];exact ⟨0,|step|,by simp,rfl,hpos⟩)
        (by rw [distance,hdr];exact (realLtValue_numbers _ _).mpr (lt_min_iff.mp hsmall).1)
      have value : raw step=M.number (native step : ℂ) := riemannRealObservation (returns _ member)
      rw [scalarDifferentialErrorCoordinate f point n matrix axis step (native step) (native 0) a
        dimension pointVector source.1 axisMember value pointValue coefficient,
        distance,M.mul_numbers,←Complex.ofReal_mul] at estimate
      exact (realLtValue_numbers _ _).mp estimate
  exact partialDerivativeOfSemanticPath f point n axis _ raw returns pointDomain
    (partialInteriorOfMultivariableInterior f point n axis dimension pointVector axisMember source.2.1)
    rawZero (fun _ _ => rfl) derivative
theorem scalarDifferentialGradientRow (f point n matrix : M.Value)
    (dimension : M.mem n (M.standard .natural))
    (pointVector : M.mem point (realVectorSetValue n))
    (realF : RealMultivariableFunctionValue M f n)
    (pointDomain : M.mem point (F.domainValue f))
    (source : HasScalarDifferentialAtValue M f point n matrix) :
    HasGradientAtValue M f point n
      (F.graphValue (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True))
        (M.standard .real) (fun axis => F.callValue matrix (FiniteFunction.pack2 (M.number 1) axis))) := by
  let rows := semanticObject (M.number 1) (M.member_isSet ((M.complex_members _).mpr ⟨1,rfl⟩))
  let cols := semanticObject n (M.member_isSet dimension)
  have rowMember : M.mem (M.number 1) (closedRangeValue (M.number 1) (M.number 1)) := by
    simpa only [Int.cast_one] using (closedRangeValue_members (M := M) 1 1 (M.number 1)).mpr
      ⟨1,by norm_num,le_rfl,le_rfl⟩
  have returns (axis : M.Value)
      (member : M.mem axis (F.sepValue (closedRangeValue (M.number 1) n) (fun _ => True))) :
      M.mem (F.callValue matrix (FiniteFunction.pack2 (M.number 1) axis)) (M.standard .real) :=
    F.call_mem _ _ _ _ source.1
      (matrixDomain_pair rows cols (M.number 1) axis rowMember ((F.sep_members _ _ _).mp member).1)
  refine ⟨F.graph_inFnSet _ _ _ returns,?_⟩
  intro axis member
  rw [F.call_graphValue _ _ _ returns _ ((F.sep_members _ _ _).mpr ⟨member,True.intro⟩)]
  exact scalarDifferentialPartialCandidate f point n matrix axis dimension pointVector realF pointDomain member source
end Litex
