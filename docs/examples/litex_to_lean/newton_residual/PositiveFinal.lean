import newton_residual.PositiveAdapter

theorem newtonPositive (x : ℝ) (hx : 0 < x) :
    0 < (x + 2 / x) / 2 := by
  exact Adapter.newtonPositive x hx
