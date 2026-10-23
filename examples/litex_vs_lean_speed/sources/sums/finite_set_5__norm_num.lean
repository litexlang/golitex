import Mathlib
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
example : Finset.sum ({1,3,5,7,9} : Finset Int) (fun k => k) = 25 := by norm_num
