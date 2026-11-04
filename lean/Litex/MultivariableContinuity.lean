import Litex.Multivariable

namespace Litex
universe u

/-- The source neighborhood includes the point and uses the actual function domain. -/
def ScalarMultivariableContinuousAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value,
      M.mem (denote delta) (denote (RPos (M := M))) ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
        RealLtValue M (absValue (M.subValue (F.callValue f input) (F.callValue f point))) epsilon

/-- Vector continuity retains both coordinate dimensions and the same full neighborhood. -/
def VectorMultivariableContinuousAtValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f point n m : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    ∃ delta : Obj (M := M) M.Value,
      M.mem (denote delta) (denote (RPos (M := M))) ∧
      ∀ input, M.mem input (F.domainValue f) →
        RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
        RealLtValue M (multivariableDistanceValue (F.callValue f input) (F.callValue f point) m) epsilon

theorem scalarMultivariableContinuousAtFromDefinition {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n : M.Value)
    (h : ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
      ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
        ∀ input, M.mem input (F.domainValue f) →
          RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
          RealLtValue M (absValue (M.subValue (F.callValue f input) (F.callValue f point))) epsilon) :
    ScalarMultivariableContinuousAtValue M f point n := h

theorem scalarMultivariableContinuousAtToDefinition {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n : M.Value) (h : ScalarMultivariableContinuousAtValue M f point n) :
    ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
      ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
        ∀ input, M.mem input (F.domainValue f) →
          RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
          RealLtValue M (absValue (M.subValue (F.callValue f input) (F.callValue f point))) epsilon := h

theorem vectorMultivariableContinuousAtFromDefinition {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m : M.Value)
    (h : ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
      ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
        ∀ input, M.mem input (F.domainValue f) →
          RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
          RealLtValue M (multivariableDistanceValue (F.callValue f input) (F.callValue f point) m) epsilon) :
    VectorMultivariableContinuousAtValue M f point n m := h

theorem vectorMultivariableContinuousAtToDefinition {M : Semantics.{u}} [F : FunctionSemantics M]
    (f point n m : M.Value) (h : VectorMultivariableContinuousAtValue M f point n m) :
    ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
      ∃ delta : Obj (M := M) M.Value, M.mem (denote delta) (denote (RPos (M := M))) ∧
        ∀ input, M.mem input (F.domainValue f) →
          RealLtValue M (multivariableDistanceValue input point n) (denote delta) →
          RealLtValue M (multivariableDistanceValue (F.callValue f input) (F.callValue f point) m) epsilon := h

end Litex
