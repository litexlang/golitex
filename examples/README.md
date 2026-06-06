# Litex Examples

This folder is both a runnable test suite and a reading gallery.

For a first pass, read the public folders in order:

1. [`00_first_steps/`](00_first_steps/) - small facts, equality chains, arithmetic, and linear equations.
2. [`01_proof_patterns/`](01_proof_patterns/) - reusable proof shapes: claims, theorem reuse, cases, contradiction, witnesses, induction, and proposition properties.
3. [`02_builtin_math/`](02_builtin_math/) - builtin arithmetic, order, ranges, finite sets, powers, absolute value, square roots, logarithms, and modular arithmetic.
4. [`03_objects_and_data/`](03_objects_and_data/) - objects, facts, statements, functions, anonymous functions, structs, tuples, matrices, macros, and templates.
5. [`04_structures/`](04_structures/) - user-defined mathematical structures such as groups, sets, functions, matrices, monotonicity, and integrability sketches.
6. [`05_case_studies/`](05_case_studies/) - larger examples and proof developments, including Euclid's algorithm, infinite primes, countability, Cantor-Schroeder-Bernstein, and Hilbert-style geometry.
7. [`06_std/`](06_std/) - runnable examples that exercise standard-library modules.
8. [`07_dataset_gallery/`](07_dataset_gallery/) - Markdown gallery pages with representative checkable examples selected from local dataset and textbook translation workspaces.

The public folders are now Markdown galleries. Each checked example is a
`litex` fenced block with a short note saying whether it exercises an object,
statement, fact, proof pattern, builtin rule, standard-library interface, or
case study.

The [`_internal/`](_internal/) folder is still tested, but it is not the main
reader path. It contains regression checks, scratch files, std-import examples,
fixtures for `run_file`, and snapshots from parser/data work.

## Recommended Reading Path

Start with:

1. [`00_first_steps/README.md`](00_first_steps/README.md) - `example_in_readme`, `calculation`, and `linear_equation`
2. [`01_proof_patterns/README.md`](01_proof_patterns/README.md) - `claim`, `thm`, cases, witnesses, induction, and theorem reuse
3. [`03_objects_and_data/README.md`](03_objects_and_data/README.md) - `litex_statement_examples`, object forms, functions, structs, and templates
4. [`04_structures/README.md`](04_structures/README.md) - `group_quotient` and other structure-facing examples

Then browse by topic. Most files are intentionally small; the goal is to show a
single proof pattern or language feature in a runnable form.

For a first serious algebra example, `04_structures/README.md` contains
`group_quotient`, which combines
`struct`, `template`, `forall ... exist!`, and `have fn ... as set` to build a
left-coset quotient set and the quotient multiplication interface for a normal
subgroup. The representative-independence lemmas are proved in that example.

## Testing

The repository test runner recursively checks `examples/**/*.lit`, the public
examples Markdown galleries, and the `litex` fenced blocks in
`examples/07_dataset_gallery/**/*.md`.

```bash
cargo test run_examples -- --nocapture
```

Std-import examples under `_internal/std_imports/` are optional and run with:

```bash
cargo test run_examples_include_std -- --nocapture
```
