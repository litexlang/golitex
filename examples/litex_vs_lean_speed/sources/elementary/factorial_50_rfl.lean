import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
example : Nat.factorial 50=30414093201713378043612608166064768844377641568960512000000000000 := by rfl
