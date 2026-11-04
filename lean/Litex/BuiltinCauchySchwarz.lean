import Litex.BuiltinMatrixInnerAdjoint
import Litex.BuiltinNormTriangle
universe u v w x
namespace Litex

theorem finiteComplexCauchySchwarz {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ i, star (f i) * g i‖ ≤
      Real.sqrt (∑ i, ‖f i‖ ^ 2) * Real.sqrt (∑ i, ‖g i‖ ^ 2) := by
  simpa only [PiLp.inner_apply,RCLike.inner_apply',PiLp.toLp_apply,starRingEnd_apply,
    PiLp.norm_eq_of_L2] using
      (norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 f) (WithLp.toLp 2 g))

theorem finiteInnerProductCauchySchwarz {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (FiniteInnerProductObj (M := M) α β γ)) :
    RealLeValue M (complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) (denote p))
      (M.mulValue
        (denote (euclideanNorm p.val.left p.val.dimension p.wd.1 p.wd.2.1))
        (denote (euclideanNorm p.val.right p.val.dimension p.wd.1 p.wd.2.2))) := by
  rw [finiteInnerProductFiniteSum p, complexUnaryValue_number,
    euclideanNormFiniteSum (euclideanNorm p.val.left p.val.dimension p.wd.1 p.wd.2.1),
    euclideanNormFiniteSum (euclideanNorm p.val.right p.val.dimension p.wd.1 p.wd.2.2),
    M.mul_numbers, ← Complex.ofReal_mul]
  apply (realLeValue_numbers _ _).mpr
  exact finiteComplexCauchySchwarz
    (fun i : Fin (NativeBridge.naturalValue (denote p.val.dimension)) =>
      NativeBridge.complexValue (F.callValue (denote p.val.left) (FiniteFunction.index i)))
    (fun i : Fin (NativeBridge.naturalValue (denote p.val.dimension)) =>
      NativeBridge.complexValue (F.callValue (denote p.val.right) (FiniteFunction.index i)))

end Litex
