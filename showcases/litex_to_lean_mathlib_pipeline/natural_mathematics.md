# Natural Mathematics

For all real numbers `a` and `b`, if `a < b`, then `a ≤ b`.

The proof spine has one step: strict order implies non-strict order.

The downstream use is deliberately different from restating the theorem. A
Lean/Mathlib consumer uses the exported result to prove that the closed
interval `[a, b]` is nonempty whenever `a < b`.
