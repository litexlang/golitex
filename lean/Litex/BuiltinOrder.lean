import Litex.OrderedArithmetic

universe u

namespace Litex

theorem mulStructuralLtNegativeLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactor : Lt lhs.val.left (number 0))
    (hOperands : Lt rhs.val.right lhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨c, z, hc, hz, hcz⟩ := hFactor
  change M.number 0 = M.number (z : ℂ) at hz
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  have hc0 : c < 0 := hz0 ▸ hcz
  obtain ⟨b, a, hb, ha, hba⟩ := hOperands
  refine NativeBridge.ltOfDenoteReal lhs rhs (c * a) (c * b) ?_ ?_
    (mul_lt_mul_of_neg_left hba hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hSame.symm.trans hc, hb, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLeNonpositiveLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactor : Le lhs.val.left (number 0))
    (hOperands : Le rhs.val.right lhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Le lhs rhs := by
  obtain ⟨c, z, hc, hz, hcz⟩ := hFactor
  change M.number 0 = M.number (z : ℂ) at hz
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  have hc0 : c ≤ 0 := hz0 ▸ hcz
  obtain ⟨b, a, hb, ha, hba⟩ := hOperands
  refine NativeBridge.leOfDenoteReal lhs rhs (c * a) (c * b) ?_ ?_
    (mul_le_mul_of_nonpos_left hba hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hSame.symm.trans hc, hb, M.mul_numbers, Complex.ofReal_mul]

end Litex
