import Litex.Multivariable
universe u v w x
namespace Litex

theorem matrixCandidateDeterminantNonzero {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hr : Same (matrixMultiply a b n n n hn hn hn ha hb) (identityMatrix n hn))
    (_hl : Same (matrixMultiply b a n n n hn hn hn hb ha) (identityMatrix n hn)) :
    matrixDeterminantValue (denote a) n ≠ M.number 0 := by
  have product := congrArg (fun z => matrixComplexValue z n n) hr
  rw [matrixComplexValueMultiply, matrixComplexValue_identity] at product
  have determinant := congrArg Matrix.det product
  rw [Matrix.det_mul, Matrix.det_one] at determinant
  intro zero
  have nativeZero := M.number_injective zero
  change (matrixComplexValue (denote a) n n).det = 0 at nativeZero
  rw [nativeZero,zero_mul] at determinant
  exact zero_ne_one determinant

theorem matrixInverseOfCandidate {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (hn : In n N)
    (ha : M.mem (denote a) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (hb : M.mem (denote b) (F.fnSetValue (matrixDomain n n) (M.standard .complex)))
    (_hr : Same (matrixMultiply a b n n n hn hn hn ha hb) (identityMatrix n hn))
    (hl : Same (matrixMultiply b a n n n hn hn hn hb ha) (identityMatrix n hn))
    (hd : matrixDeterminantValue (denote a) n ≠ M.number 0) :
    Same (matrixInverse a n hn ha hd) b := by
  apply matrixSameOfComplexMatrix (matrixInverse a n hn ha hd) b n n hn hn
    (matrixInverseInFnSet _) hb
  have canonical := congrArg (fun z => matrixComplexValue z n n)
    (matrixMultiplyInverseRight a n hn ha hd)
  rw [matrixComplexValueMultiply, matrixComplexValue_identity] at canonical
  have candidate := congrArg (fun z => matrixComplexValue z n n) hl
  rw [matrixComplexValueMultiply, matrixComplexValue_identity] at candidate
  exact Matrix.right_inv_eq_left_inv canonical candidate

end Litex
