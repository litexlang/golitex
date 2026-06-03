# Litex Examples

This folder is both a runnable test suite and a reading gallery.

For a first pass, read the public folders in order:

1. [`00_first_steps/`](00_first_steps/) - small facts, equality chains, arithmetic, and linear equations.
2. [`01_proof_patterns/`](01_proof_patterns/) - reusable proof shapes: claims, theorem reuse, cases, contradiction, witnesses, induction, and proposition properties.
3. [`02_builtin_math/`](02_builtin_math/) - builtin arithmetic, order, ranges, finite sets, powers, absolute value, square roots, logarithms, and modular arithmetic.
4. [`03_objects_and_data/`](03_objects_and_data/) - objects, facts, statements, functions, anonymous functions, structs, tuples, matrices, macros, and templates.
5. [`04_structures/`](04_structures/) - user-defined mathematical structures such as groups, sets, functions, matrices, monotonicity, and integrability sketches.
6. [`05_case_studies/`](05_case_studies/) - larger examples and proof developments, including Euclid's algorithm, infinite primes, countability, Cantor-Schroeder-Bernstein, and Hilbert-style geometry.

The [`_internal/`](_internal/) folder is still tested, but it is not the main
reader path. It contains regression checks, scratch files, std-import examples,
fixtures for `run_file`, and snapshots from parser/data work.

## Recommended Reading Path

Start with:

1. [`00_first_steps/example_in_readme.lit`](00_first_steps/example_in_readme.lit)
2. [`00_first_steps/calculation.lit`](00_first_steps/calculation.lit)
3. [`00_first_steps/linear_equation.lit`](00_first_steps/linear_equation.lit)
4. [`01_proof_patterns/claim.lit`](01_proof_patterns/claim.lit)
5. [`01_proof_patterns/thm.lit`](01_proof_patterns/thm.lit)
6. [`03_objects_and_data/litex_statement_examples.lit`](03_objects_and_data/litex_statement_examples.lit)
7. [`04_structures/group_quotient.lit`](04_structures/group_quotient.lit)

Then browse by topic. Most files are intentionally small; the goal is to show a
single proof pattern or language feature in a runnable form.

For a first serious algebra example, `04_structures/group_quotient.lit` combines
`struct`, `template`, `forall ... exist!`, and `have fn ... as set` to build the
left-coset quotient set. It also records the `is_normal_subgroup` predicate as
the condition needed later for quotient-group multiplication to be well-defined.

## Testing

The repository test runner recursively checks `examples/**/*.lit`.

```bash
cargo test run_examples -- --nocapture
```

Std-import examples under `_internal/std_imports/` are optional and run with:

```bash
cargo test run_examples_include_std -- --ignored --nocapture
```
