# Obj regression corpus

This directory tests the terminal variants reachable from `Obj` in
`src/ast/obj.rs`. Each variant has a dedicated, nonempty positive `.lit` file.
Function-head variants and the `FnSetSpace` helper enum are audited as well.
This is an object corpus; statement and fact inventories remain in the existing
`stmt_nodes` and `proof_nodes` suites.

The cases cover exact numeric values, carriers, precedence, signs, zero,
endpoints, empty containers where legal, nested objects, binders, function
arity/domain/codomain, struct fields, and identifier ownership. Most positive
cases use independent `sketch:` scopes, whose facts and definitions do not
escape to later cases. Rejections and unresolved positive cases are standalone
fixtures. No test uses `trust` to manufacture success.

The approved numeric and aggregate repairs add exact decimal normalization,
imaginary nonzero and guarded division, bounded nested sum/product calculation
and symbolic identities. See [acceptance](acceptance.md) for current gate results
and [todo](todo.md) for surviving issues. Earlier reports remain historical.

## Run

From the repository root:

```sh
cargo build --release
python3 examples/test_objs/run.py
```

The runner first builds the current release source and stops if compilation
fails, so an older executable cannot masquerade as current verification.
The default command checks intended behavior, including recorded gaps. It
returns nonzero while any legitimate positive still fails, or any forbidden
input still succeeds. It also rejects timeouts, crashes, invalid JSON,
exit/JSON disagreement, incomplete fixture inventories, and uncovered AST
variants. A known defect is never converted into a passing semantic test.

To reproduce the complete observed baseline, including known defects:

```sh
python3 examples/test_objs/run.py --baseline --report examples/test_objs/baseline.json
```

Baseline success means the recorded observations reproduced. It does not mean
the known defects are fixed. A fixed gap makes the baseline differ; promote its
successful regression or rejection, update the manifest and close its todo.

Focused commands:

```sh
python3 examples/test_objs/run.py --object div
python3 examples/test_objs/run.py --object anonymous_fn --object finite_set_reduce
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
target/release/litex -f examples/test_objs/div.lit
```

Every process is checked using the current CLI's top-level `success` field and
its exit status. Source and executable hashes are recorded in structured
reports; a source/executable change during a gate invalidates it. Build before
running after source changes. This checkout does not support the older workflow
flags `-compact`, `-runner`, `-before` or the `try:` statement. The implementation
journals record ordinary persistent sessions and final clean-file gates instead.

## Layout and evidence

- `*.lit`: independently scoped positive cases, with stable `Pxx` case IDs.
- `identifier_with_*/main.lit`: qualified-name cases with minimal projects
  needed to exercise real export and import ownership.
- `negative/`: individually executable must-reject cases. Some currently
  expose defects; the manifest and todo identify those explicitly.
- `gaps/`: legitimate cases that remain unverified. These are executed too.
- `fixtures/`: small maintained library for qualified-identifier tests.
- `coverage.json`: AST path, file, case and observed-gap inventory.
- `baseline.json`, `results.json`: historical complete-suite process observations
  for the initial inventory; consult their hashes and status.
- `number_diagnosis_*.json`: focused follow-up snapshots for the added Number
  inequality regression.
- [diagnosis_2026-10-02.md](diagnosis_2026-10-02.md): checked causes of the
  decimal, complex-inverse and finite-sum examples selected by the user.
- `proof_journals/`: accepted source and materially distinct failed attempts.
- [coverage.md](coverage.md): readable per-object inventory and case counts.
- [todo.md](todo.md): concrete reproductions, exact diagnostics, intended
  outcomes and next actions for surviving issues.
- [acceptance.md](acceptance.md): tracer, selected gates and verification limits.

Do not recursively treat every `.lit` here as a must-pass example: the negative
and gap fixtures deliberately exercise the rejected or defective boundaries.
Use `run.py` to select and interpret them.

## Current language boundaries

These cases follow the implementation's contracts, rather than adding external
mathematical axioms. `N` contains zero. `quot(a, d)` requires `d` in `N+`.
`gcd(a, b)` excludes `(0, 0)`. Displayed list-set entries must be provably
pairwise distinct. Real `abs` is separate from complex `C_abs`. Tuple and
Cartesian-product indices and finite-sequence function domains are one-based.
Integer ranges and real intervals have different endpoint rules.
Range `sum`/`product` require a nonempty range; `reduce` permits an empty range.
Indexed union/intersection/product currently require a nonempty index carrier.
Free-form nested bracket sequences and explicit `&Struct{value}.field` selection
are outside the current syntax.

A rejected mathematically correct direct assertion can be a missing proof route
or an authoring limitation. The todo distinguishes those observations from
confirmed violations of well-definedness contracts. This finite regression
corpus cannot prove the absence of all object bugs.
