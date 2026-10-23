import Mathlib

example : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x
