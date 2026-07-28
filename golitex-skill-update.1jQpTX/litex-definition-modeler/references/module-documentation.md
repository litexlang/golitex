# Litex Module Documentation

Use this convention for a new top-level module or project, and when an existing
module adds or changes a core mathematical interface.

## One pair per module

Maintain exactly one `README.md` and one `math_collections.md` for the whole
top-level module, even when it contains many files, exports or submodules.

- Put the pair in a reusable directory module's root.
- Put a textbook project's pair in `scripts/textbooks_drafts/<Book>/` beside
  its `litex.config`; publish it to `textbooks/<Book>/` only during an
  explicitly requested release.
- Treat a textbook pair as non-rendered, non-kernel sidecar documentation. Do
  not add it to `[export]`, imports, or rendered chapter lists.
- Do not backfill untouched modules only to satisfy this convention.

## README.md: current implementation

Keep the README factual and compact:

1. Module purpose and mathematical scope.
2. Import or run entrypoint and canonical namespace.
3. Actual public objects, functions, templates, predicates and main theorems.
4. Visible checked, trusted and axiom boundaries.
5. One or two verified minimal uses.

Do not list an ideal interface that has not been implemented. A new empty
module may say that no public API is implemented yet.

## math_collections.md: mathematical manual

Record the mathematical spine, not every declaration. For each important
concept or intermediate node, explain:

1. Its ordinary mathematical meaning and why later work depends on it.
2. Its ideal Litex form: builtin, `prop`, `have`, `have fn`,
   `have fn ... by exist!`, `template`, or a source-facing theorem.
3. A short representative signature or interface sketch.
4. Why the nearest alternative form is wrong.
5. Its dependencies and representative downstream uses.
6. Which proof, existence, uniqueness or well-definedness holes may remain
   behind that interface.

Write this as a readable design note. Do not add machine statuses, exhaustive
theorem inventories, or a schema that needs a validator.

## Use while writing code

1. Read both files before substantial module work.
2. Use `math_collections.md` to choose the interface and run a representative
   downstream use probe.
3. If code and the note differ, decide which misunderstood the mathematics.
4. Fix the code when it drifted. If the design changed, update
   `math_collections.md` first and then migrate the affected code.
5. Never preserve incompatible forms through wrappers, aliases,
   compatibility predicates, `abstract_prop`, or `trust`.
6. After verification, update `README.md` to describe the actual public API.
