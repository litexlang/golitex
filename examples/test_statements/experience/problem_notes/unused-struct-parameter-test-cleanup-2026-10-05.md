# Unused struct parameter: stale negative corrected

The maintainer confirmed that the old DEC04 test expectation was wrong and
authorized a small test/record cleanup. Struct field-set semantics are retained.

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
```

K is absent from the fields, so both Point<N,R> and Point<Z,R> describe R × N.
The original negative expression is preserved as an executable positive:

```litex
# Original template prefix supplies selected_value.
forall t &Point<N,R>:
    \selected_value<Z,R,t>(0)=t.value
```

Its reverse unused-K application also passes. A new negative changes the
parameter that actually controls value's carrier:

```litex
# With the same original Point/template prefix, this must reject.
forall t &Point<N,R>:
    \selected_value<N,Z,t>(0)=t.value
```

The original wrong-object and missing-template-guard controls remain intact.
Every check also rejects 0=1 and verifies the environment stack returns to one
frame. The new [durable tracer](../../../wd/struct_parameter_carriers.lit)
checks identical unused-parameter field sets, explicit extension equality,
and a separately used field parameter:

```litex
struct FieldParameterPoint<K nonempty_set,S nonempty_set>:
    value S
    tag K
(0,-1) $in &FieldParameterPoint<Z,R>
# Negative Rust control:
# (0,-1) $in &FieldParameterPoint<N,R>
```

Executable negatives also cover a noninteger integer tag, an imaginary real
value, and universal Z-tag to N-tag membership. N-to-Z is mathematically a
valid inclusion; it cannot be classified as a wrong-carrier negative.
The bare universal used-field N-to-Z shortcut and one coordinate author probe
still missed in the exploratory session. They are recorded without pretending
to add general struct subtype automation; no production rule was changed.

The historical 933/934 and earlier red gates remain unchanged in their frozen
reports. Current concrete DEC04 pending paragraphs are removed only after
the focused test correction and final gate; a closed-ID link remains.

## Verification

The original targeted test reproduced its stale expected-false assertion:
actual true / expected false, exit 101. After cleanup the surrounding
`showcase_local_repair_tests` module passed 7/7. The baseline persistent CLI
session retained unused-K positives and true negatives, with 1=1 passing after
rejections. The complete new strict tracer passed 9 top-level statements.

Final full Rust and file gate results follow below. Raw input,
output, failed compile attempt, and source fingerprints are retained in the
[journal](../../proof_journals/unused-struct-parameter-test-cleanup-2026-10-05.json)
and its receipt archive. The first all-targets attempt compiled no tests due
to a shared module declaration preceding //! documentation; that source was
already corrected on inspection. This cleanup does not claim that repair.

Owned changes: test expectations/controls, one tracer, one corrected K/S
fixture comment, and current records. No AST, Runtime/Env, struct carrier,
storage, search, trust or production verifier behavior changed. Other work in
the shared checkout is preserved.

## Final current-source gates

- `cargo test --release --offline --all-targets -- --nocapture`: exit 0; lib **955/955**, integration **1/1**, no ignored tests. The main binary has zero unit tests; the nonzero lib/integration selections are recorded separately.
- `cargo test --release --offline --lib showcase_local_repair_tests -- --nocapture`: **7/7** after correction. The complete final gate also reruns these seven tests on the later shared source snapshot.
- `cargo build --release --offline`: exit 0. Final production CLI SHA256: `0b2b20c808b02876d727512b32fb094b3b48e715d7e4b8a8cb339bb56cb1c3ae`.
- Eleven final strict CLI file gates: four expected accepts and seven expected rejects, all with nonzero statement results, matching exits and no session error. New tracer **9/9**, original template fixture **6/6**.
- Final capture watches 820 files under src/tests/Cargo plus the two relevant Litex fixtures, with zero watched drift. It includes shared native fixed-base work, which this task does not claim to implement.

Full docs/textbook/geometry/Lean/release collectors were outside this cleanup.
Historical red-gate counts are preserved; current DEC04 pending paragraphs are
gone. The receipt snapshot retains source/test/Cargo and selected input bytes;
five pre-existing unrelated receipt ZIPs per snapshot are retained by hash
rather than duplicated. Their original workspace files are untouched.
