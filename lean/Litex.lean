import Litex.Multivariable
import Litex.BuiltinScalar
import Litex.BuiltinElementary
import Litex.BuiltinComplex
import Litex.BuiltinSets
import Litex.BuiltinOrder
import Litex.BuiltinTranscendental
import Litex.BuiltinCardinality
import Litex.BuiltinDenseOrder
import Litex.BuiltinNumberTheory
import Litex.BuiltinLogarithm
import Litex.BuiltinTrigonometry
import Litex.BuiltinPower
import Litex.BuiltinFiniteIndex
import Litex.BuiltinFolds
import Litex.BuiltinDisjunction
import Litex.BuiltinChoice
import Litex.FiniteSequenceSpaces
import Litex.SequenceSpaces
import Litex.SetConstructorCongruence
import Litex.SymmetricDifferenceIdentities
import Litex.FunctionConstructorCongruence
import Litex.RecursiveFunctions
import Litex.BuiltinVector
import Litex.BuiltinSequence
import Litex.BuiltinMultivariable

/-! Stable entrypoint for the Litex semantic library and its proved compiler adapters. -/

namespace Litex
universe u v w x

/-- The finite complex square-matrix carrier, on original semantic values. -/
noncomputable def complexSquareMatrixValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (n : M.Value) : M.Value :=
  F.fnSetValue (realMatrixDomainValue n n) (M.standard .complex)

/-- A supplied two-sided inverse. Carrier conditions remain part of the contract. -/
def IsMatrixInvValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (a b n : M.Value) : Prop :=
  M.mem n (M.standard .natural) ∧
  M.mem a (complexSquareMatrixValue M n) ∧
  M.mem b (complexSquareMatrixValue M n) ∧
  matrixComplexOn a (NativeBridge.naturalValue n) (NativeBridge.naturalValue n) *
    matrixComplexOn b (NativeBridge.naturalValue n) (NativeBridge.naturalValue n) = 1 ∧
  matrixComplexOn b (NativeBridge.naturalValue n) (NativeBridge.naturalValue n) *
    matrixComplexOn a (NativeBridge.naturalValue n) (NativeBridge.naturalValue n) = 1

def MatrixInversibleValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (a n : M.Value) : Prop :=
  ∃ b : Obj (M := M) M.Value,
    ∃ _ : M.mem (denote b) (complexSquareMatrixValue M n), IsMatrixInvValue M a (denote b) n

theorem isMatrixInvOfProducts {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hr : Same (matrixMultiply a b n n n hn hn hn ha hb) (identityMatrix n hn))
    (hl : Same (matrixMultiply b a n n n hn hn hn hb ha) (identityMatrix n hn)) :
    IsMatrixInvValue M (denote a) (denote b) (denote n) := by
  refine ⟨hn,ha,hb,?_,?_⟩
  · have h := congrArg (fun z => matrixComplexValue z n n) hr
    rw [matrixComplexValueMultiply, matrixComplexValue_identity] at h
    exact h
  · have h := congrArg (fun z => matrixComplexValue z n n) hl
    rw [matrixComplexValueMultiply, matrixComplexValue_identity] at h
    exact h

theorem isMatrixInvProducts {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (h : IsMatrixInvValue M (denote a) (denote b) (denote n)) :
    Same (matrixMultiply a b n n n hn hn hn ha hb) (identityMatrix n hn) ∧
    Same (matrixMultiply b a n n n hn hn hn hb ha) (identityMatrix n hn) := by
  constructor
  · apply matrixSameOfComplexMatrix (matrixMultiply a b n n n hn hn hn ha hb) (identityMatrix n hn) n n hn hn
      (matrixMultiplyInFnSet _) (functionRealToComplex (identityMatrixInFnSet _))
    rw [matrixComplexValueMultiply, matrixComplexValue_identity]
    exact h.2.2.2.1
  · apply matrixSameOfComplexMatrix (matrixMultiply b a n n n hn hn hn hb ha) (identityMatrix n hn) n n hn hn
      (matrixMultiplyInFnSet _) (functionRealToComplex (identityMatrixInFnSet _))
    rw [matrixComplexValueMultiply, matrixComplexValue_identity]
    exact h.2.2.2.2

theorem isMatrixInvInversible {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (h : IsMatrixInvValue M (denote a) (denote b) (denote n)) :
    MatrixInversibleValue M (denote a) (denote n) :=
  ⟨semanticObject (denote b) (isSet b),h.2.2.1,h⟩

theorem matrixInversibleNonzero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β)
    (h : MatrixInversibleValue M (denote a) (denote n)) :
    matrixDeterminantValue (denote a) n ≠ M.number 0 := by
  obtain ⟨b,_,h⟩ := h
  have hd := congrArg Matrix.det h.2.2.2.1
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  have hz' := M.number_injective hz
  change (matrixComplexOn (denote a) (NativeBridge.naturalValue (denote n))
    (NativeBridge.naturalValue (denote n))).det = 0 at hz'
  rw [hz',zero_mul] at hd
  exact zero_ne_one hd

theorem matrixInversibleOfNonzero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β) (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    MatrixInversibleValue M (denote a) (denote n) := by
  let b := matrixInverse a n hn ha hd
  exact isMatrixInvInversible a b n (isMatrixInvOfProducts a b n hn ha
    (matrixInverseInFnSet b) (matrixMultiplyInverseRight a n hn ha hd)
    (matrixMultiplyInverseLeft a n hn ha hd))

theorem matrixInversibleNatural {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β)
    (h : MatrixInversibleValue M (denote a) (denote n)) : In n N := by
  obtain ⟨b,_,hb⟩ := h
  exact hb.1

theorem matrixInversibleCarrier {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (n : Obj (M := M) β)
    (h : MatrixInversibleValue M (denote a) (denote n)) :
    M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)) := by
  obtain ⟨b,_,hb⟩ := h
  exact hb.2.1

end Litex
