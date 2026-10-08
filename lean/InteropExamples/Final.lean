import InteropExamples.Adapter

namespace NativeConsumer

theorem complexAddZero (x : ℂ) : x + 0 = x := by
  exact Adapter.complexAddZero x

theorem realAddZero (x : ℝ) : x + 0 = x := by
  exact Adapter.realAddZero x

example (x : ℂ) (f : ℂ → ℂ) : f (x + 0) = f x := by
  rw [complexAddZero]

end NativeConsumer
