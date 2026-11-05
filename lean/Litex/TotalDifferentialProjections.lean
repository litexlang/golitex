import Litex.ScalarDifferentialProjections

open Filter
open scoped Topology
universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem componentRealGraphLaws (f n m row : M.Value)
    (realF : VectorMultivariableFunctionValue M f n m)
    (rowMember : M.mem row (closedRangeValue (M.number 1) m)) :
    (∀ x, M.mem x (F.domainValue (componentFunctionValue f (F.domainValue f) row)) ↔ M.mem x (F.domainValue f)) ∧
    (∀ x, M.mem x (F.domainValue f) →
      F.callValue (componentFunctionValue f (F.domainValue f) row) x=F.callValue (F.callValue f x) row) ∧
    (∀ x, M.mem x (F.domainValue (componentFunctionValue f (F.domainValue f) row)) →
      M.mem (F.callValue (componentFunctionValue f (F.domainValue f) row) x) (M.standard .real)) := by
  let D := F.sepValue (F.domainValue f) (fun _ => True)
  let body := fun x => F.callValue (F.callValue f x) row
  have returns (x : M.Value) (hx : M.mem x D) : M.mem (body x) (M.standard .real) :=
    F.call_mem _ _ _ _
      (multivariableVectorFunctionReturns f n m x realF ((F.sep_members _ _ _).mp hx).1)
      ((F.sep_members _ _ _).mpr ⟨rowMember,True.intro⟩)
  have member : M.mem (componentFunctionValue f (F.domainValue f) row) (F.fnSetValue D (M.standard .real)) :=
    F.graph_inFnSet _ _ _ returns
  obtain ⟨signature,functionMember,_,_⟩ := realF
  have sourceDomainSet : M.isSet (F.domainValue f) := by
    rw [F.domainValue_eq signature.domain_isSet functionMember]
    exact signature.domain_isSet
  have domain := F.domainValue_eq (F.sep_isSet _ _ sourceDomainSet) member
  have domains (x : M.Value) :
      M.mem x (F.domainValue (componentFunctionValue f (F.domainValue f) row)) ↔ M.mem x (F.domainValue f) := by
    rw [domain]
    exact ⟨fun hx => ((F.sep_members _ _ _).mp hx).1,fun hx => (F.sep_members _ _ _).mpr ⟨hx,True.intro⟩⟩
  refine ⟨domains,?_,?_⟩
  · intro x hx
    exact F.call_graphValue _ _ _ returns x ((F.sep_members _ _ _).mpr ⟨hx,True.intro⟩)
  · intro x hx
    have inputD : M.mem x D := by
      dsimp only [D]
      rw [←domain]
      exact hx
    exact F.call_mem _ _ _ _ member inputD
theorem totalDifferentialPartialCandidate (f point n m matrix row axis : M.Value)
    (dimension : M.mem n (M.standard .natural)) (outputDimension : M.mem m (M.standard .natural))
    (pointVector : M.mem point (realVectorSetValue n))
    (realF : VectorMultivariableFunctionValue M f n m)
    (pointDomain : M.mem point (F.domainValue f))
    (rowMember : M.mem row (closedRangeValue (M.number 1) m))
    (axisMember : M.mem axis (closedRangeValue (M.number 1) n))
    (source : HasTotalDifferentialAtValue M f point n m matrix) :
    HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) row)
      point n axis (F.callValue matrix (FiniteFunction.pack2 row axis)) := by
  let component := componentFunctionValue f (F.domainValue f) row
  have laws := componentRealGraphLaws f n m row realF rowMember
  have componentPoint : M.mem point (F.domainValue component) := (laws.1 point).mpr pointDomain
  have componentInterior : MultivariableInteriorValue (F.domainValue component) point n := by
    obtain ⟨radius,positive,control⟩ := source.2.1
    exact ⟨radius,positive,fun x hx near => (laws.1 x).mpr (control x hx near)⟩
  let raw := fun h : ℝ => F.callValue component (coordinatePathValue point n axis (M.number (h : ℂ)))
  let native := fun h : ℝ => observeRealValue (raw h)
  have pathZero := coordinatePathValueZero point n axis dimension pointVector axisMember
  have rawZero : raw 0=F.callValue component point := by
    dsimp only [raw]
    rw [Complex.ofReal_zero,pathZero]
  have pointValue : F.callValue component point=M.number (native 0 : ℂ) := by
    rw [←rawZero]
    exact riemannRealObservation (by rw [rawZero];exact laws.2.2 point componentPoint)
  have nearPath := coordinatePathNeighborhoodOfInterior (F.domainValue f) point n axis
    dimension pointVector axisMember source.2.1
  obtain ⟨eta,heta,inDomain⟩ := Metric.eventually_nhds_iff.mp nearPath
  let rows := semanticObject m (M.member_isSet outputDimension)
  let cols := semanticObject n (M.member_isSet dimension)
  have coefficientReal := F.call_mem _ _ _ _ source.1
    (matrixDomain_pair rows cols row axis rowMember axisMember)
  obtain ⟨a,coefficient⟩ := (M.real_members _).mp coefficientReal
  have derivative : SemanticDerivativeAtValue M raw 0
      (F.callValue matrix (FiniteFunction.pack2 row axis)) := by
    refine ⟨a,coefficient,native,?_,?_⟩
    · filter_upwards [nearPath] with h hh
      exact riemannRealObservation (laws.2.2 _ ((laws.1 _).mpr hh))
    · apply realDerivativeOfLinearError
      intro epsilon hepsilon
      obtain ⟨delta,hdelta,bound⟩ := source.2.2 (M.number (epsilon : ℂ)) (numberInRPos epsilon hepsilon)
      obtain ⟨dr,hdr,positive⟩ := NativeBridge.realWitnessOfPositive delta (inRPos_positive delta hdelta)
      refine ⟨Min.min dr eta,lt_min positive heta,?_⟩
      intro step hpos hsmall
      let input := coordinatePathValue point n axis (M.number (step : ℂ))
      have member : M.mem input (F.domainValue f) :=
        inDomain (by simpa only [Real.dist_eq,sub_zero] using (lt_min_iff.mp hsmall).2)
      have distance := coordinatePathDistance point n axis step dimension pointVector axisMember
      have estimate := bound input member
        (by rw [distance];exact ⟨0,|step|,by simp,rfl,hpos⟩)
        (by rw [distance,hdr];exact (realLtValue_numbers _ _).mpr (lt_min_iff.mp hsmall).1)
      have value : raw step=M.number (native step : ℂ) :=
        riemannRealObservation (laws.2.2 _ ((laws.1 _).mpr member))
      have atInput : F.callValue (F.callValue f input) row=M.number (native step : ℂ) :=
        (laws.2.1 input member).symm.trans value
      have atPoint : F.callValue (F.callValue f point) row=M.number (native 0 : ℂ) :=
        (laws.2.1 point pointDomain).symm.trans pointValue
      obtain ⟨error,errorEqual,coordinateBound⟩ := totalDifferentialErrorCoordinateBound
        f point n m matrix row axis step (native step) (native 0) a dimension outputDimension
        pointVector source.1 rowMember axisMember
        (multivariableVectorFunctionReturns f n m input realF member)
        (multivariableVectorFunctionReturns f n m point realF pointDomain) atInput atPoint coefficient
      rw [errorEqual,distance,M.mul_numbers,←Complex.ofReal_mul] at estimate
      exact lt_of_le_of_lt coordinateBound ((realLtValue_numbers _ _).mp estimate)
  exact partialDerivativeOfSemanticPath component point n axis _ raw laws.2.2 componentPoint
    (partialInteriorOfMultivariableInterior component point n axis dimension pointVector axisMember componentInterior)
    rawZero (fun _ _ => rfl) derivative

theorem totalDifferentialJacobianCandidate (f point n m matrix : M.Value)
    (dimension : M.mem n (M.standard .natural)) (outputDimension : M.mem m (M.standard .natural))
    (pointVector : M.mem point (realVectorSetValue n))
    (realF : VectorMultivariableFunctionValue M f n m)
    (pointDomain : M.mem point (F.domainValue f))
    (source : HasTotalDifferentialAtValue M f point n m matrix) :
    HasJacobianAtValue M f point n m matrix := by
  refine ⟨source.1,?_⟩
  intro row rowMember axis axisMember
  exact totalDifferentialPartialCandidate f point n m matrix row axis dimension outputDimension
    pointVector realF pointDomain rowMember axisMember source
end Litex
