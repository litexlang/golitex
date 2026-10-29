import examples.function_limit_punctured_cancellation.Adapter

open Filter
open scoped Topology

/-- The compiled punctured rational-function proof yields a native limit. -/
theorem squareDivSelfLimitZero :
    Tendsto (fun x : ℝ => x ^ 2 / x) (𝓝[≠] 0) (𝓝 0) := by
  exact Adapter.puncturedCancellationLimit
