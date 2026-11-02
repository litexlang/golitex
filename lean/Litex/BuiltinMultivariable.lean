import Litex.Multivariable
universe u
namespace Litex

theorem multivariableScalarLimitOfClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point dimension value : M.Value) (hv : M.mem value (M.standard .real))
    (ha : MultivariableAccumulationValue M (F.domainValue f) point dimension)
    (he : MultivariableScalarEpsilonValue M f point dimension value) :
    HasMultivariableScalarLimitValue M f point dimension value := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  exact ⟨r,hr,ha,he⟩

theorem multivariableScalarLimitClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point dimension value : M.Value) (h : HasMultivariableScalarLimitValue M f point dimension value) :
    MultivariableAccumulationValue M (F.domainValue f) point dimension ∧
      MultivariableScalarEpsilonValue M f point dimension value := by
  obtain ⟨_,_,ha,he⟩ := h
  exact ⟨ha,he⟩


def MultivariableVectorEpsilonValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n m value : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (M.number 0) (multivariableDistanceValue input point n) →
        RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
        RealLtValue M (multivariableDistanceValue (F.callValue f input) value m) epsilon

theorem multivariableVectorLimitOfClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value : M.Value) (hv : M.mem value (realVectorSetValue m))
    (ha : MultivariableAccumulationValue M (F.domainValue f) point n)
    (he : MultivariableVectorEpsilonValue M f point n m value) :
    HasMultivariableVectorLimitValue M f point n m value := ⟨hv,ha,he⟩

theorem multivariableVectorLimitClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value : M.Value) (h : HasMultivariableVectorLimitValue M f point n m value) :
    MultivariableAccumulationValue M (F.domainValue f) point n ∧
      MultivariableVectorEpsilonValue M f point n m value := h.2
theorem gradientOfCoordinatePartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (hv : M.mem value (realVectorSetValue n))
    (h : ∀ coordinate, M.mem coordinate (closedRangeValue (M.number 1) n) →
      HasPartialDerivativeAtValue M f point n coordinate (F.callValue value coordinate)) :
    HasGradientAtValue M f point n value := ⟨hv,h⟩

theorem gradientCoordinatePartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (h : HasGradientAtValue M f point n value) :
    ∀ coordinate, M.mem coordinate (closedRangeValue (M.number 1) n) →
      HasPartialDerivativeAtValue M f point n coordinate (F.callValue value coordinate) := h.2

theorem hessianOfOrderedPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (hv : M.mem value (realMatrixSetValue n n))
    (h : ∀ row, M.mem row (closedRangeValue (M.number 1) n) →
      ∀ col, M.mem col (closedRangeValue (M.number 1) n) →
        HasSecondPartialAtValue M f point n row col
          (F.callValue value (FiniteFunction.pack2 row col))) :
    HasHessianAtValue M f point n value := ⟨hv,h⟩

theorem hessianOrderedPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (h : HasHessianAtValue M f point n value) :
    ∀ row, M.mem row (closedRangeValue (M.number 1) n) →
      ∀ col, M.mem col (closedRangeValue (M.number 1) n) →
        HasSecondPartialAtValue M f point n row col
          (F.callValue value (FiniteFunction.pack2 row col)) := h.2

theorem jacobianOfComponentPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value : M.Value) (hv : M.mem value (realMatrixSetValue m n))
    (h : ∀ row, M.mem row (closedRangeValue (M.number 1) m) →
      ∀ col, M.mem col (closedRangeValue (M.number 1) n) →
        HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) row)
          point n col (F.callValue value (FiniteFunction.pack2 row col))) :
    HasJacobianAtValue M f point n m value := ⟨hv,h⟩

theorem jacobianComponentPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m value : M.Value) (h : HasJacobianAtValue M f point n m value) :
    ∀ row, M.mem row (closedRangeValue (M.number 1) m) →
      ∀ col, M.mem col (closedRangeValue (M.number 1) n) →
        HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) row)
          point n col (F.callValue value (FiniteFunction.pack2 row col)) := h.2

theorem divergenceOfDiagonalPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (hv : M.mem value (M.standard .real))
    (h : ∃ diagonal : Obj (M := M) M.Value,
      M.mem (denote diagonal) (realVectorSetValue n) ∧
      (∀ coordinate, M.mem coordinate (closedRangeValue (M.number 1) n) →
        HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) coordinate)
          point n coordinate (F.callValue (denote diagonal) coordinate)) ∧
      vectorSumValue (denote diagonal) n = value) :
    HasDivergenceAtValue M f point n value := ⟨hv,h⟩

theorem divergenceDiagonalPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (h : HasDivergenceAtValue M f point n value) :
    ∃ diagonal : Obj (M := M) M.Value,
      M.mem (denote diagonal) (realVectorSetValue n) ∧
      (∀ coordinate, M.mem coordinate (closedRangeValue (M.number 1) n) →
        HasPartialDerivativeAtValue M (componentFunctionValue f (F.domainValue f) coordinate)
          point n coordinate (F.callValue (denote diagonal) coordinate)) ∧
      vectorSumValue (denote diagonal) n = value := h.2

theorem laplacianOfDiagonalPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (hv : M.mem value (M.standard .real))
    (h : ∃ diagonal : Obj (M := M) M.Value,
      M.mem (denote diagonal) (realVectorSetValue n) ∧
      (∀ coordinate, M.mem coordinate (closedRangeValue (M.number 1) n) →
        HasSecondPartialAtValue M f point n coordinate coordinate
          (F.callValue (denote diagonal) coordinate)) ∧
      vectorSumValue (denote diagonal) n = value) :
    HasLaplacianAtValue M f point n value := ⟨hv,h⟩

theorem laplacianDiagonalPartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n value : M.Value) (h : HasLaplacianAtValue M f point n value) :
    ∃ diagonal : Obj (M := M) M.Value,
      M.mem (denote diagonal) (realVectorSetValue n) ∧
      (∀ coordinate, M.mem coordinate (closedRangeValue (M.number 1) n) →
        HasSecondPartialAtValue M f point n coordinate coordinate
          (F.callValue (denote diagonal) coordinate)) ∧
      vectorSumValue (denote diagonal) n = value := h.2

theorem curlOfCoordinatePartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value : M.Value) (hv : M.mem value (realVectorSetValue (M.number 3)))
    (h : CurlDefinitionValue M f (F.domainValue f) point value) :
    HasCurlAtValue M f point value := ⟨hv,h⟩

theorem curlCoordinatePartials {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point value : M.Value) (h : HasCurlAtValue M f point value) :
    CurlDefinitionValue M f (F.domainValue f) point value := h.2

theorem partialDerivativeOfClauses {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate value : M.Value) (_hv : M.mem value (M.standard .real))
    (hi : PartialInteriorValue M f point n coordinate)
    (hl : HasFiniteFunctionLimitValue M .both (partialQuotientValue f point n coordinate)
      (M.number 0) value) : HasPartialDerivativeAtValue M f point n coordinate value := ⟨hi,hl⟩

theorem partialDerivativeClauses {M : Semantics.{u}} [FunctionSemantics M]
    (f point n coordinate value : M.Value) (h : HasPartialDerivativeAtValue M f point n coordinate value) :
    PartialInteriorValue M f point n coordinate ∧
      HasFiniteFunctionLimitValue M .both (partialQuotientValue f point n coordinate) (M.number 0) value := h

theorem scalarDifferentialOfClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n matrix : M.Value) (hv : M.mem matrix (realMatrixSetValue (M.number 1) n))
    (hi : MultivariableInteriorValue (M := M) (F.domainValue f) point n)
    (he : ScalarDifferentialRemainderValue f point n matrix) :
    HasScalarDifferentialAtValue M f point n matrix := ⟨hv,hi,he⟩

theorem scalarDifferentialClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n matrix : M.Value) (h : HasScalarDifferentialAtValue M f point n matrix) :
    MultivariableInteriorValue (M := M) (F.domainValue f) point n ∧
      ScalarDifferentialRemainderValue f point n matrix := h.2

theorem totalDifferentialOfClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m matrix : M.Value) (hv : M.mem matrix (realMatrixSetValue m n))
    (hi : MultivariableInteriorValue (M := M) (F.domainValue f) point n)
    (he : TotalDifferentialRemainderValue f point n m matrix) :
    HasTotalDifferentialAtValue M f point n m matrix := ⟨hv,hi,he⟩

theorem totalDifferentialClauses {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m matrix : M.Value) (h : HasTotalDifferentialAtValue M f point n m matrix) :
    MultivariableInteriorValue (M := M) (F.domainValue f) point n ∧
      TotalDifferentialRemainderValue f point n m matrix := h.2

end Litex
