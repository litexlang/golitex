import examples.function_limit_polynomial_chain.Adapter

open Filter
open scoped Topology

theorem polynomialProductLimit :
    Tendsto (fun x : ℝ => (x^2+1)*(x-2)) (𝓝[≠] 2) (𝓝 0) := by
  exact Adapter.polynomialChainLimit
