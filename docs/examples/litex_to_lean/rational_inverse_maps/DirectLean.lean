import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- A complete ordinary Mathlib authoring baseline for two inverse rational maps. -/

namespace DirectLean

def forward (x : ℚ) : ℚ := (2 * x + 1) / (x - 1)
def backward (y : ℚ) : ℚ := (y + 1) / (y - 2)

theorem forwardDomain (x : ℚ) (hx : x ≠ 1) : forward x ≠ 2 := by
  intro h
  unfold forward at h
  field_simp [sub_ne_zero.mpr hx] at h
  linarith

theorem backwardDomain (y : ℚ) (hy : y ≠ 2) : backward y ≠ 1 := by
  intro h
  unfold backward at h
  field_simp [sub_ne_zero.mpr hy] at h
  linarith

-- Use the earlier domain certificate for the outer quotient.
theorem leftInverse (x : ℚ) (hx : x ≠ 1) : backward (forward x) = x := by
  change (forward x + 1) / (forward x - 2) = x
  apply (div_eq_iff (sub_ne_zero.mpr (forwardDomain x hx))).mpr
  unfold forward
  field_simp [sub_ne_zero.mpr hx]
  ring

theorem rightInverse (y : ℚ) (hy : y ≠ 2) : forward (backward y) = y := by
  change (2 * backward y + 1) / (backward y - 1) = y
  apply (div_eq_iff (sub_ne_zero.mpr (backwardDomain y hy))).mpr
  unfold backward
  field_simp [sub_ne_zero.mpr hy]
  ring

-- Reuse the proved inverse instead of redoing rational normalization.
theorem forwardInjectiveOn : Set.InjOn forward {x : ℚ | x ≠ 1} := by
  intro x hx x' hx' h
  have inverseEquality := congrArg backward h
  simpa only [leftInverse x hx, leftInverse x' hx'] using inverseEquality

-- Ordinary Lean packaging of the two source inverse laws; no new mathematical claim.
def rationalEquiv : {x : ℚ // x ≠ 1} ≃ {y : ℚ // y ≠ 2} where
  toFun x := ⟨forward x.val, forwardDomain x.val x.property⟩
  invFun y := ⟨backward y.val, backwardDomain y.val y.property⟩
  left_inv x := Subtype.ext (leftInverse x.val x.property)
  right_inv y := Subtype.ext (rightInverse y.val y.property)

end DirectLean
