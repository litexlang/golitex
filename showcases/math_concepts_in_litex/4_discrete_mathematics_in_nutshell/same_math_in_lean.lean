/- The same direct recurrence theorem as the Litex Pascal-table example,
using only Lean's automatically loaded Prelude.  No separate proposition
wrapper is needed: the recursive equation is already the reusable theorem. -/

def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem pascalIdentity (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by
  rfl

example : choose 5 2 = 10 := by decide
