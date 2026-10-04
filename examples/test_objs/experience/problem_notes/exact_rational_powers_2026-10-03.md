# Exact rational powers: accepted scope

Only candidate 1 was requested. Radical order/derived functions and binomial
radical denominator inversion were excluded.

## Before and now

```litex
# Before: each of these lines rejected in the freshly built baseline.
# 8^(1/3)=2
# 16^(3/4)=8
# (1/27)^(-1/3)=3
# eval 8^(1/3)
# The first failure was Pow WD requiring 1/3 (or the other exponent) in Z.

8^(1/3)=2
16^(3/4)=8
(1/27)^(-1/3)=3
eval (4/9)^(1/2)
```

All four active lines now pass. The eval result is exactly `2 / 3`.
The dedicated runnable [tracer](../../../proof_nodes/equal/by_builtin_rule/closed_rational_power_calculation.lit)
retains the old rejection as comments and uses independent discarded sketches.

## Owners and mathematical boundary

- Pow WD in `well_defined_results/verify_obj/scalar.rs` has one added closed
  `Q+`/`Q` branch. Both operand WD and checked membership certificates remain
  in the proof. It inherits the caller's VerifyState. Symbolic noninteger
  exponents and nonpositive bases with noninteger exponents are not added.
- `exact_rational.rs` owns the shared calculation. For reduced positive base
  `a/b` and reduced exponent `p/q`, a rational result requires integer q-th
  roots of both a and b, since p and q are coprime. After these exact roots,
  reuse the existing checked integer power, including reciprocals for p < 0.
- Integer root search uses checked integer powers and binary search. Overflow
  of a trial positive power proves that trial exceeds the i128 input; it is
  not accepted as a value. A root >= 2 with degree >= 127 cannot fit i128.
  Inputs equal to one are handled before that bound. No prime factorization,
  floating point, new dependency, AST shape, state owner or search policy.
- Taking roots first admits `8^(100/3)=2^100` without forming `8^100`.
  Nonperfect roots and checked arithmetic overflow decline calculation.
  Existing integer-power domains, including `0^0=1`, are unchanged.

Well-definedness and exact evaluation are independent:

```litex
let u=2^(1/3)       # accepted as an object
# eval 2^(1/3)     # rejects: no rational value is supplied
# eval 8^(127/3)   # rejects: exact integer result would overflow
# (-8)^(1/3)=-2    # rejects: this added domain requires a positive base
```

## Accepted evidence

- Stable release source/test fingerprint:
  `ddd707471ed8bb555c3b97d070b88969ed179e710b593bd31260fc2346473a1c`.
- Release binary:
  `b0360930197e6bc039b3863a67c467a3f64590b3ab7a71d545f15e74bf7014b8`.
- 23 selected release Rust tests pass: 7 `exact_rational_powers`, 9
  `closed_exact_elementary_calculation`, 6 `closed_numeric_expr`, and the
  existing `exact_signed_integer_powers_and_eval` regression. The tracer is
  collected by `run_examples_closed_rational_power_calculation`.
- 38 strict CLI checks pass: the tracer, complete owning `pow.lit` (29
  independent cases), 12 Pow rejection files, 16 new individual positive
  cases, two new Manual/FAQ blocks and six independent eval value checks.
  Positives require exit 0/JSON success true/no session_error; negatives
  require exit 1/success false. Eval checks also require the exact displayed
  value and no stored facts. Source and binary are stable across this gate.
- `pow.lit` gains P141–P156; its negative corpus gains N141–N149.
  No trust was added. This is a focused certificate, not a whole-corpus pass.

```sh
cargo build --release
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/closed_rational_power_calculation.lit
cargo test --release --lib exact_rational_powers -- --nocapture
cargo test --release --lib closed_exact_elementary_calculation -- --nocapture
cargo test --release --lib closed_numeric_expr -- --nocapture
cargo test --release --lib execute::exact_numeric_periodic_modulus::exact_signed_integer_powers_and_eval -- --exact --nocapture
```

The [journal](../../proof_journals/exact_rational_powers_2026-10-03.json) retains
the fresh baseline, persistent session, build attempts, source identities,
all receipts and scope/audit decisions. The [structured report](../../exact_rational_powers_results_2026-10-03.json)
retains the final checks.

## Additional old mixed-module test failures

An additional full `exact_numeric_periodic_modulus` module run had 9 passes
and three failures. These are not hidden or counted as an all-green module:

1. `new_rule_normal_output_is_bilingual` expects earlier builtin names for
   `C_abs(3+4*i)=5` and `3^(-2)=1/9`.
2. `new_leaves_inherit_search_ceiling_and_do_not_store_search_facts` expects
   `C_abs(3-4*i)=5` to fail at KnownSpecialProperty, although the central
   Direct calculation is permitted there.
3. `logarithm_algebra_for_positive_nonunit_bases` requires
   `LogOfPowerSameBase` for `log(1/2,(1/2)^(-3))=-3`; it now calculates.

The retained pre-change binary and final binary both accept the numeric
examples with `by_closed_calculation`, without the old provenance labels.
The existing [source audit](../../../../tests/unit/execute/exact_numeric_periodic_modulus/bugs/src-basic-release-audit-2026-10-03.md)
already records these tests. Their migration is outside this rational-power
addition; no expected result was weakened and no mixed-module test was edited.

## Workflow deviations

- Actual CLI routing is `-strict -f/-e`; JSON reports `success`. The ordinary
  persistent REPL supports discarded sketch scopes. The obsolete skill flags
  `-runner/-compact/-before` and literal `try` protocol are not implemented.
- One final build hit four independent private-module references in concurrent
  witness diagnostics. A read-only follow-up observed the public-path repair
  already applied by concurrent work; this task did not edit witness code.
- An initial CLI gate spanned two unrelated test-source updates. The final
  release was rebuilt and all 38 CLI checks replayed against the stable
  source/test fingerprint above. Both attempts remain in the journal.
