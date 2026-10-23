import Mathlib
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
example : Finset.sum (Finset.range 10) (fun _ => (1/3 : Rat)) = 10/3 := by norm_num
