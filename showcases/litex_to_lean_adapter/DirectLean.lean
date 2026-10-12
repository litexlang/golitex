import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DirectLean

/-- The integration example is already a standard Mathlib identity. -/
theorem quotientDistributes (x y z : ℝ) :
    (x + y) / z = x / z + y / z := by
  exact add_div x y z

/-- A more involved comparison: a fractional-linear involution. -/
noncomputable def mobius (x : ℝ) : ℝ := (x + 1) / (x - 1)

/-- This is a native baseline, not an export of the Litex compiler. -/
theorem mobiusInvolution (x : ℝ) (hx : x ≠ 1) :
    mobius x ≠ 1 ∧ mobius (mobius x) = x := by
  unfold mobius
  constructor
  · intro h
    field_simp [sub_ne_zero.mpr hx] at h
    linarith
  · field_simp [sub_ne_zero.mpr hx]
    ring

end DirectLean
