import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
example : Nat.gcd 10610209857723 6557470319842=1 := by native_decide
