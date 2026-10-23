import Mathlib
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
example : Finset.sum (Finset.range 100) (fun k => (((k + 1 : Nat) : Int)^2)) = 338350 := by norm_num
