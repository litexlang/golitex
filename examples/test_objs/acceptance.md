# Obj corpus acceptance

Task: one detailed Litex regression file per Obj variant.

## Tracer: exact division and its WD boundary

The existing division WD example only introduced a value:

```litex
# Existing examples/wd/obj/scalar_div.lit
let q = 1 / 2
```

The dedicated [div.lit](div.lit) now independently verifies exact values, sign, associativity/precedence and symbolic nonzero division:

```litex
6 / 2 = 3
(1 / 2) + (1 / 2) = 1
8 / 2 / 2 = 2
8 / (2 / 2) = 8
```

Executable boundaries also check a zero denominator, an unproved nonzero denominator, a wrong value and a nonnumeric divisor. For example:

```litex
# negative/div__n01.lit: must reject
let x = 1 / 0
```

A complex inverse was originally a separate gap. It is now checked in `div.lit`
case `P08`; the repair journal below preserves its rejected baseline.

## Initial complete-suite verification snapshot

- 99 terminal Obj paths audited against `src/ast/obj.rs`, including all nested interval and number-set alternatives and the helper enums.
- 461 independently scoped positive cases in 99 dedicated files.
- 261 negative fixtures: 254 correctly rejected; 7 incorrect admissions retained as defects.
- 103 direct positive cases retained as unresolved proof/WD boundaries.
- All `.lit` fixtures are inventoried, nonempty and free of trust.
- The intended-behavior gate remains nonzero because the defects and unresolved cases are included.
- The baseline gate passes only if all recorded observations reproduce; no negative/gap is skipped.

```sh
cargo build --release
target/release/litex -f examples/test_objs/div.lit
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/test_runner.py
python3 examples/test_objs/run.py --report examples/test_objs/results.json
python3 examples/test_objs/run.py --baseline --report examples/test_objs/baseline.json
```

Baseline snapshot executable: `b128f1c404a38f16c7f4d0ba9ab6394951ba9b600be9c6e9a9de49cdcd940b2a`.

Baseline snapshot source: `4a21ba75a90faf5103376d6fcb69bba9abb9909df83912c3a83966144ff175be`.

The runner built the current source before each final gate. Source and executable remained stable within each gate; the two reports have different snapshot hashes because concurrent source work continued between runs. Every recorded gap has the same observed outcome and phase in both reports. See the reports for each snapshot's exit codes and diagnostics. Broader Rust unit tests, docs, textbook and Lean suites were outside this test-corpus change; no shared semantic contract was changed by this task.

The runner's nine protocol/coverage boundary tests passed, including the control that a failed build must execute no fixture.

## Source updates observed during this task

A concurrent update added nonempty-index requirements. Previously accepted empty-index examples were retired in the positive files and replaced with executable `N_EMPTY` negatives; their original journal observations remain historical, not current acceptance evidence. A transient compile failure in that work was resolved before final verification.

The same unchanged callable-template alias that initially failed now passes after that concurrent source update, so it was promoted to `instantiated_template_obj.lit` case `P04`:

```litex
template<S set>:
    have fn identity(x S) S = x
let f = \identity<R>
f(2) = 2
```

This task did not implement the engine repair; it captured the successful behavior in the corpus.

Temporary staging scripts and probes were removed after durable journals, reports and issue records were written. Earlier unrelated workspace edits were preserved.

## Follow-up diagnosis (2026-10-02)

The written inventory now contains 262 negative fixtures and 111 recorded gaps. The new negative [number__n03.lit](negative/number__n03.lit) must reject:

```litex
2.400 != 2.4
```

The release verifier instead accepted it through `Closed decimal inequality`. See [diagnosis_2026-10-02.md](diagnosis_2026-10-02.md) for the normalization cause, the two complex-inverse barriers and the proposed finite-sum reduction. The follow-up ran a focused Number gate; it did not rerun the complete corpus or change kernel semantics. `number_diagnosis_baseline.json` and `number_diagnosis_results.json` record that focused snapshot; the earlier `baseline.json` and `results.json` describe the initial full gate and earlier inventory.
