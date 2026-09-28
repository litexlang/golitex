# Property-flow compilation boundary

Status: open

## Concrete probe

- Source: `property_flow.lit`.
- Litex verification succeeds without `trust` or `abstract_prop`.
- Current compilation stops at `square_of_is_nonnegative` with:

  ```text
  statement Result 5 failed to compile: named forall proof step 1 failed to compile:
  builtin rule `builtin.verify.verify_builtin_rules.number_compare.verify_zero_le_even_integer_pow_builtin_rule`
  has no reviewed ToLean mapping; target `#14#root ^ 2 >= 0`; children [#14#root $in Z; Z $subset R]
  ```

## Desired interface

Compile the verifier-owned even-integer-power nonnegativity evidence through a
reviewed generic rule mapping. Then continue through the existing concrete
predicate premise, local `by thm`, and `by def` consumers without introducing
an axiom, proof hole, or source-specific shortcut.

Acceptance: compile the fixture to Lean, pass `lake env lean` on the generated
file, and retain the fixture as the generic regression.

Primary blocker: `kernel_problem`.
