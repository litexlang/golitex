import Adapter

namespace LitexLeanExample

/-- A Lean user sees only real numbers, a nonzero premise, and native equality. -/
theorem quotientDistributes (x y z : ℝ) (hz : z ≠ 0) :
    (x + y) / z = x / z + y / z := by
  exact Adapter.quotientDistributes x y z hz

/-- The native definition uses ordinary real arithmetic. -/
noncomputable def mobius (x : ℝ) : ℝ := (x + 1) / (x - 1)

theorem mobiusInvolution (x : ℝ) (hx : x ≠ 1) :
    mobius x ≠ 1 ∧ mobius (mobius x) = x := by
  simpa only [mobius] using Adapter.mobiusInvolution x hx

end LitexLeanExample
