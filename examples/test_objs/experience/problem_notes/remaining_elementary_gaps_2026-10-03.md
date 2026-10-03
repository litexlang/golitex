# Remaining elementary object gaps

Task: clear the user's 22 rational, trig, inverse, log and modulus goals.
Scope: the 14 existing closures were rechecked; this round closes the remaining
8 goals in examples/test_objs. No trust was added.

The finite-extremum equality leaf selects an original rational list member.
Its dedicated max/min certificates record the zero-based selected index,
original member and every exact normalized comparison. Whole-object WD retains
nonempty, finite, real and pairwise-distinct requirements. Arithmetic overflow
returns a computation miss; display eval is not used as proof evidence.

Quarter-angle inverse proofs use a separately checked sine/cosine nonzero
fact, the forward tan/cot value, the correct principal range and an equality
chain. Only strict order of closed rational pi coefficients was added. The
current restricted builtin-premise entry also requires explicit real-carrier
facts. Every retained carrier was independently deletion-probed in the live
session; the inverse carriers were necessary. No negative-value inverse table
or global search change was introduced.

The three log algebra identities now require a positive base unequal to one,
including bases below one. Both requirements appear in Detailed evidence.
The native e > 1 bound supplies e != 1; positivity and the general self rule
finish log(e,e)=1. Monotonicity keeps its existing separate base-range checks.
The log source first proves (1/2)^(-3)=8, then uses the same-base-power chain.
The deletion audit removed the unnecessary 1 $in R lines.

Durable tracers:
- [Rational extrema](../../../proof_nodes/equal/by_builtin_rule/finite_set_rational_extrema.lit)
- [Quarter-angle inverses](../../../proof_nodes/equal/by_builtin_rule/inverse_trig_quarter_angles.lit)
- [Log algebra](../../../proof_nodes/equal/by_builtin_rule/log_positive_nonunit_base.lit)

Former fixtures, failed candidates, accepted session blocks, and deletion
controls are retained in
[the journal](../../proof_journals/remaining_elementary_gaps_2026-10-03.json).

The current CLI lacks -compact/-runner/-before/try. Sessions used independent
sketch blocks; clean file gates require strict top-level success=true and exit
0. Its REPL only prints success/error, so precise failure phases were
corroborated with standalone strict JSON. Concurrent parser and verifier work
interrupted builds; this round added only a RuntimeResult annotation to one
parser closure. No AST fields or Env/Runtime state were changed by this round.

Final gates and stable source/binary identities are recorded in the journal
and the focused corpus report. Full kernel, textbook, release and Lean gates
are outside this bounded change.

Verification receipts: all 22 requested goals and all three durable tracers
passed strict exit/JSON gates. The current-source focused run passed 95 positive
cases in 13 object files and all 42 rejection fixtures, with no gate failures.
The exact-numeric/periodic/modulus Rust group passed 12 tests; JSON acceptance
passed 14 tests. The AST/manifest audit passed for 99 leaves and 99 files.
Scoped diff whitespace checks passed. The live inventory contains 594 positive
cases, 289 negatives and 22 unrelated gaps.

Focused gate source SHA-256: `737218fd2d79c2d39ee4236ef36091c0871e51d25f565eb1734d0f9346ef9855`.
Focused gate binary SHA-256: `bc1c88e23cc38ddcf0e8e8d565395b6e8d970549808614b95735ff4afed2ee4e`.
Both identities remained stable during the run and matched the workspace at
the final direct-goal/tracer gate.
