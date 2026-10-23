import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
example : (95800 : Nat)^4+217519^4+414560^4=422481^4 := by norm_num
