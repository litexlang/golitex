import examples.function_limit_unique.Adapter

open Filter
open scoped Topology

/-- Two finite limits of a real function at the same punctured point agree. -/
theorem realFunctionLimitUnique (f : ℝ → ℝ) (x0 L K : ℝ)
    (hL : Tendsto f (𝓝[≠] x0) (𝓝 L)) (hK : Tendsto f (𝓝[≠] x0) (𝓝 K)) : L = K := by
  exact Adapter.functionLimitsUnique f x0 L K hL hK
