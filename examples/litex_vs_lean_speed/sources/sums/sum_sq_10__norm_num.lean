import Mathlib
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
example : Finset.sum (Finset.range 10) (fun k => (((k + 1 : Nat) : Int)^2)) = 385 := by norm_num
