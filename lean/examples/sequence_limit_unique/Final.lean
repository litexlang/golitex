import examples.sequence_limit_unique.Adapter

open Filter
open scoped Topology

/-- A real sequence cannot converge to two different real limits. -/
theorem realSequenceLimitUnique (f : ℕ → ℝ) (L K : ℝ)
    (hL : Tendsto f atTop (𝓝 L)) (hK : Tendsto f atTop (𝓝 K)) : L = K := by
  exact Adapter.sequenceLimitsUnique f L K hL hK
