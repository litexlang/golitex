import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
example : Real.sqrt 2 * Real.sqrt 8=4 := by
  rw [← Real.sqrt_mul (by norm_num : (0:Real)≤2)]
  norm_num
