# Exact numeric, integral trig periods and numeric complex modulus

Task: implement the user's items 1/2/6, including symbolic integer periods and
both signs/orders of numeric complex coordinates. Date: 2026-10-03.

`have k Z; tan(pi+2*k*pi)=0` now checks its real-angle WD, a separate
sine/cosine nonzero certificate and every surviving symbolic term's integer
membership. Tangent/cotangent have period pi; nonzero signed sine/cosine values
need period 2*pi. Exact special angles include sixths, quarters, thirds and
halves. Linear coefficients combine without introducing new stored atoms.
Unknown real periods, poles and undefined canceled divisions reject.

Closed negative integer powers use a checked reciprocal; closed rational order
uses positive denominators and exact checked cross-products. Binary fraction
min/max now work. All zero-base/denominator and wrong-value controls remain
rejected. Overflow declines computation; no approximate evidence is created.

Numeric complex arithmetic produces exact rational real/imaginary coordinates.
The modulus rule checks the nonnegative root of their squared sum. Requested
`a+b*i`, `b*i+a`, `a-b*i` and `-b*i+a` layouts work, including decimal and
fractional coefficients. Negative roots reject. Display evaluation preserves
an exact root even after its modulus equality was proved, without storing a fact.

The 14 former reproductions and complete process results are retained in
[the journal](../../proof_journals/exact_numeric_periodic_modulus_2026-10-03.json).
Promotions: pow-P04, min/max-P05, sin/cos-P04, tan-P02/P03/P04,
cot-P02/P03 and complex_abs-P03/P04/P05/P06. Only these verified closures
are retired. Another 21 independently scoped positives and five negatives
cover signed powers, all fraction order signs, symbolic trig periods and every
requested modulus layout in the owning Obj files. The live manifest now has
The later concurrent follow-ups leave 594 positive cases, 289 negatives and 22 direct gaps; their extra closures are not attributed to this repair. Finite-set extrema on fractions still reject; no closure is claimed.

Durable tracers and commands:

```sh
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/periodic_trig_exact_values.lit
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/negative_integer_power_exact.lit
target/release/litex -strict -f examples/proof_nodes/atomic/by_builtin_rule/exact_fraction_order.lit
target/release/litex -strict -f examples/proof_nodes/equal/by_builtin_rule/numeric_complex_modulus.lit
cargo test --release exact_numeric_periodic_modulus -- --nocapture
```

Paired rejection controls: `examples/negative/exact_numeric_periodic_modulus/`.
The journal records a stable successful current-source release, the old failing
tracer, eight focused Rust families (80 tests), 38 supported session frames,
clean-file and four changed executable documentation blocks. All source and
binary identities are recorded. A later concurrent verification-state
refactor makes subsequent current-source builds fail before fixture execution;
retained-release receipts are explicitly labeled and do not certify that
unfinished checkout. This task adapts its new state-ceiling test to the current
API without changing the state contract. There is no active Lean compiler in this
checkout, and full Rust, textbook, packaging and publication gates are outside
this bounded kernel change. AST, Env/Runtime state and global search budgets
are unchanged. Existing concurrent work is retained.

Final verification limit: a stable release after the state-API transition passes
all 17 feature artifacts/controls, all 26 added corpus cases and four docs blocks.
The complete corpus still has 39 owning-file failures and the remaining direct
gaps; see the separate current-source regression ledger. Source edits continued
between individual Rust commands, so the journal labels that receipt unstable.
The eight original tests all pass; added concurrent test failures are preserved
without weakening their assertions or making an all-family pass claim.
