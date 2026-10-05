# Fixed real trigonometric reflections and cosine double angle

User request: add similar elementary conclusions outside the repair batch.
Five bounded equality leaves now prove the following directly:

```litex
forall x R:
    cos(2*x)=cos(x)^2-sin(x)^2
    cos(2*x)=1-2*sin(x)^2
    cos(2*x)=2*cos(x)^2-1
    sin(pi-x)=sin(x)
    cos(pi-x)=-cos(x)
    sin(pi/2-x)=cos(x)
    cos(pi/2-x)=sin(x)
```

All seven cold direct assertions previously exited 1 with root success false,
no session error, and first failure in search_proof. Cosine double angle and
the two complementary-angle goals already had checked explicit author routes;
this update adds fixed shortcuts rather than treating their author routes as
missing mathematical checkability. Solved AU55/AU56 concrete pending entries
were removed from the active plan. Historical audits remain intact.

## Contract and owner

The existing TrigComplexIdentity owner matches one outer sin/cos constructor
after complete equality WD. Reflections recognize an exact pi coefficient in
`q*pi-x` or `q*pi+(-x)`, with q=1 or q=1/2. Cosine double angle recognizes
`2*x`, `x*2`, or `x+x` and compares the RHS with three fixed rational-expression
forms. Symmetric targets, equivalent scalar spellings and composite real
arguments remain supported. These leaves generate no proof obligations and
perform no recursive trig expansion. Global scheduling, ceilings, WD,
storage, state, AST and compiler contracts were not changed.

Each success has its own typed payload. Detailed retains the matched angle;
CosDoubleAngle also retains the matched RHS form. Ten named locale methods
provide distinct Normal explanations. A standalone successful equality stores
an actual fact, and reversed reuse retains a real citation.

## Executed acceptance

- `cargo test --release --offline --lib trig_reflections_double_angle_tests -- --nocapture`: 8/8 tests passed, including 27 rejected assertions, scoped failure recovery, cold matching, actual storage reuse, adjacent old routes, and ten-language output.
- `cargo test --release --offline --lib rule_language_methods_tests -- --nocapture`: 3/3 contract tests passed.
- Current-source `cargo build --release --offline`: exit 0.
- Five new complete strict CLI tracer files: all pass (three top-level statements each). Six adjacent old sum/difference/shift files also pass.
- Seven original isolated assertions: all pass after repair. Eleven additional CLI false/WD-invalid controls exit 1 with root success false and no session error.
- CLI total: 29 executions, 18 expected accepts and 11 expected rejections. Source/test/Cargo manifest has 760 files and remained unchanged through final build/gates.
- One additional persistent CLI process: 12 frames, 10 successes and two rejected wrong-sign assertions; accepted facts remain reusable after both failures. Rust tests separately check the actual citation.

Baseline CLI SHA256: `c37e06113e91a09e500adde57949039e09d171f7da995d6487e08579d116feac`.
Final CLI SHA256: `7a1f5c8b87d90d19c555ab5916f17b5a58ad667129e4208fa119d5f0a873f90e`.
Complete before/final Rust source, test and Cargo bytes, pinned binaries, exact inputs and raw
outputs are retained in the [receipt archive](../../proof_journals/trig-reflections-double-angle-2026-10-05-receipts.zip)
and indexed by the [journal](../../proof_journals/trig-reflections-double-angle-2026-10-05.json).

The first output test incorrectly inspected a forall's Normal summary, which
deliberately hides the inner leaf. The corrected test executes a standalone
equality after `have x R` in the same Runtime. The initial 7/8 result and final
8/8 result are both preserved; no output semantics were changed to satisfy it.

Impact: L2 isolated equality rule family with rule-specific output wiring.
Full kernel/examples/docs/Lean/release gates were not selected. Complex-domain
trig and unguarded partial arguments retain the existing real-domain WD
boundary; wrong signs, angles, coefficients and different RHS arguments reject.
No unresolved blocker remains for these five leaves.

Tracers: [cosine double angle](../../equal/by_builtin_rule/cos_double_angle.lit),
[sine pi reflection](../../equal/by_builtin_rule/sin_pi_reflection.lit),
[cosine pi reflection](../../equal/by_builtin_rule/cos_pi_reflection.lit),
[sine complementary angle](../../equal/by_builtin_rule/sin_half_pi_reflection.lit),
[cosine complementary angle](../../equal/by_builtin_rule/cos_half_pi_reflection.lit).
