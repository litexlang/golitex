import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
example : exists a b c d : Nat, a>0 ∧ b>0 ∧ c>0 ∧ d>0 ∧ a^4+b^4+c^4=d^4 := by refine ⟨95800,217519,414560,422481,?_⟩; norm_num
