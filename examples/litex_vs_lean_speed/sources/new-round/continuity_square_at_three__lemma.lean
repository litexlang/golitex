import Mathlib

example : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2
