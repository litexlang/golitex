import Mathlib

example : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num
