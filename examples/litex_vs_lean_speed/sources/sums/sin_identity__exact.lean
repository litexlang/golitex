import Mathlib
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
example : forall x : Real, Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := fun x => Real.sin_sq_add_cos_sq x
