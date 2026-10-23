import Mathlib
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
example : Finset.sum (Finset.range 100) (fun _ => (1/3 : Rat)) = 100/3 := by norm_num [Finset.sum_const]
