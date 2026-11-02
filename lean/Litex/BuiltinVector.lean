import Litex.Matrices
import Litex.BuiltinComplex
universe u v w x
namespace Litex

theorem finiteInnerProductSelfPositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ))
    (hself : Same p.val.left p.val.right) : In p R ∧ Le (number 0) p := by
  let q := euclideanNorm p.val.left p.val.dimension p.wd.1 p.wd.2.1
  have heq : denote p = M.number (euclideanNormSum (denote p.val.left) p.val.dimension) := by
    change M.number (finiteInnerProductValue (denote p.val.left) (denote p.val.right) p.val.dimension) = _
    change denote p.val.left = denote p.val.right at hself
    rw [← hself]
    exact (euclideanNormSquareInner q).symm.trans (euclideanNormSquare q)
  obtain ⟨r,hr,hsum⟩ := finiteMagnitudeSquareSumNonnegative
    (matrixIndexValue p.val.dimension)
    (fun k => NativeBridge.complexValue (F.callValue (denote p.val.left) k))
    (matrixIndexFinite p.val.dimension p.wd.1)
  have hvalue : denote p = M.number (r : ℂ) := heq.trans (congrArg M.number hsum)
  exact ⟨(M.real_members _).mpr ⟨r,hvalue⟩, 0,r,rfl,hvalue,hr⟩
end Litex
