import Litex.Multivariable

namespace Litex
universe u

/-- Scalar differentiability retains the source's real row-matrix witness. -/
def ScalarDifferentiableAtValue (M : Semantics.{u}) [FunctionSemantics M]
    (f point n : M.Value) : Prop :=
  ∃ a : Obj (M := M) M.Value,
    M.mem (denote a) (realMatrixSetValue (M.number 1) n) ∧
      HasScalarDifferentialAtValue M f point n (denote a)

/-- Vector differentiability retains both original coordinate dimensions. -/
def VectorDifferentiableAtValue (M : Semantics.{u}) [FunctionSemantics M]
    (f point n m : M.Value) : Prop :=
  ∃ a : Obj (M := M) M.Value,
    M.mem (denote a) (realMatrixSetValue m n) ∧
      HasTotalDifferentialAtValue M f point n m (denote a)

theorem scalarDifferentiableAtFromDefinition {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value)
    (h : ∃ a : Obj (M := M) M.Value,
      M.mem (denote a) (realMatrixSetValue (M.number 1) n) ∧
        HasScalarDifferentialAtValue M f point n (denote a)) :
    ScalarDifferentiableAtValue M f point n := h

theorem scalarDifferentiableAtToDefinition {M : Semantics.{u}} [FunctionSemantics M]
    (f point n : M.Value) (h : ScalarDifferentiableAtValue M f point n) :
    ∃ a : Obj (M := M) M.Value,
      M.mem (denote a) (realMatrixSetValue (M.number 1) n) ∧
        HasScalarDifferentialAtValue M f point n (denote a) := h

theorem vectorDifferentiableAtFromDefinition {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value)
    (h : ∃ a : Obj (M := M) M.Value,
      M.mem (denote a) (realMatrixSetValue m n) ∧
        HasTotalDifferentialAtValue M f point n m (denote a)) :
    VectorDifferentiableAtValue M f point n m := h

theorem vectorDifferentiableAtToDefinition {M : Semantics.{u}} [FunctionSemantics M]
    (f point n m : M.Value) (h : VectorDifferentiableAtValue M f point n m) :
    ∃ a : Obj (M := M) M.Value,
      M.mem (denote a) (realMatrixSetValue m n) ∧
        HasTotalDifferentialAtValue M f point n m (denote a) := h

end Litex
