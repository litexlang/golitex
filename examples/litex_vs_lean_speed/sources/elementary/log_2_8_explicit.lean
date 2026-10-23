import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
example : Real.logb 2 8=3 := by
  rw [show (8:Real)=2^3 by norm_num, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1:Real)<2)]
  norm_num
