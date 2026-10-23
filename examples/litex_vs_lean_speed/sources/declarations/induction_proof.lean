import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def bench_terms (k : Int) : Int := k
theorem bench_use : ∀ n : Nat, 1 ≤ n → 2 * (∑ k ∈ Finset.range n, bench_terms ((k+1 : Nat) : Int)) = (n : Int) * ((n : Int)+1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [bench_terms]
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    simp only [bench_terms] at *
    push_cast at *
    nlinarith
