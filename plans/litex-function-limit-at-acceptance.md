# Finite-point function limits: delivery receipt

Date: 2026-10-20. Stage F is implemented under the user's explicit approval
of its exact Function/AtPoint and positive/negative Fact additions. The
[continuation](litex-limits-next-phases.md) retains S/I/U as proposals.
The requested goal skill is installed as `$litex-function-limit-at` at
`/Users/shenjiachen/.codex/skills/litex-function-limit-at/`; its validator passes.

## Delivered contract

First prove `$has_limit_at(f,x0,L)` or existence of a finite real candidate;
then use `lim(f,x0)`. WD consumes that evidence. It does not inspect a body,
invoke limit laws, or guess an answer. Cancellation by zero still requires
the limit operand to be well-defined. Existing `lim(a)` is preserved.

The function's actual complete unary real domain includes its guards.
The candidate requires both punctured accumulation and epsilon-delta control.
The point need not belong to the domain, and no call at that point is made.
Empty/isolated domains cannot supply a limit by vacuous control. Accumulation
is part of truth, so negative candidates on those domains remain expressible.

Delivered consumers include real membership, nested use, exact candidate-value
calculation, uniqueness, substitution/capture, alpha identity, congruence of
function and point, JSON evidence, ten output-language dispatches, and LaTeX.
Only the approved AST additions were made; no Env/Runtime field or global
proof-search ceiling changed. All 22 explicit BT contracts and their real
domain premises are listed in [the live documentation](../docs/function-limits.md).

## Checked artifacts

- [Primary punctured proof](../examples/wd/real_function_limit_at.lit):
  accumulation with r/2, epsilon-delta control for x²/x at zero, definition
  introduction, selected value and arithmetic, and explicit contradiction
  of the false candidate 1. It never calls f(0).
- [Common proofs](../examples/wd/real_function_limit_common_proofs.lit):
  x² at 3 gives 9; the named sum x²+1 gives 10; the legal quotient
  (x²+1)/2 gives 5; nested arithmetic gives 6.
- [Interfaces](../examples/wd/real_function_limit_interfaces.lit): arbitrary
  checked real-subset domains, finite existence, nested function calls and
  simultaneous function/point equality transport.
- [Relative endpoint](../examples/wd/real_function_limit_endpoints.lit):
  identity on R+ at zero, with its own proved approach.
- One strict fixture for each `fn_limit_at_*` theorem in
  `examples/stmt_nodes/release_and_expand/builtin_thm/`, plus two direct
  selected-value/uniqueness equality fixtures.
- Ten `real_function_limit_*.lit` rejection controls in `examples/wd_negative/`:
  missing convergence, zero cancellation, punctured function without proof,
  empty/isolated/non-real domains, illegal base call, wrong point, zero
  limiting denominator and an incorrect output function.

Public examples use no `trust` or local axioms. The native BTs are mathematical
kernel rules with checked and retained premises; their acceptance tests do
not constitute an independent soundness proof of every analytic law.

## Measured validation

Release binary: `tmp/2026-10-20/function-limit-at/target/release/litex`.
The [machine-readable receipt](litex-function-limit-at-acceptance.json)
records its SHA-256, representative source hashes, actual commands, file
results and language checks. Evidence describes the working tree, not a
clean commit or a full-repository release gate.

| Release-library filter | Passed | Failed |
| --- | ---: | ---: |
| `function_limit_tests` | 13 | 0 |
| `sequence_limit_tests` | 12 | 0 |
| `function_composition` | 17 | 0 |
| `compile_to_latex` | 12 | 0 |
| `builtin_thm` | 23 | 0 |

The focused family includes the collector of all 28 positive and 10 negative
files, proof-before-use and context retention, exact value calculation,
carriers/domains/arity, negation, named output laws, local/order/squeeze/sign
contracts, proof ceilings, JSON, LaTeX and explicit Lean rejection. It also
distinguishes a non-real approach-point error from missing convergence and
rejects later claim-body evidence being used to justify earlier value WD.
Adjacent filters passed before the final diagnostic-only failure split;
the focused family and file gates passed again afterward.

Commands use the isolated target directory:

```bash
cargo build --release --target-dir tmp/2026-10-20/function-limit-at/target
cargo test --release --lib function_limit_tests --target-dir tmp/2026-10-20/function-limit-at/target
tmp/2026-10-20/function-limit-at/target/release/litex -strict -lang en -f examples/wd/real_function_limit_at.lit
```

All 28 strict positive files returned exit 0 with Normal JSON `kind=run`,
`run_result=success`, `session_terminated=false`, `termination=null`.
All 10 negatives returned nonzero with `run_result=failure` and no hard
termination. The main proof also passed in en, zh, zh-hant, fr, ru, es, ar,
ja, ko and vi, using each language's actual envelope keys. Both newly added
executable documentation blocks passed strict CLI verification.
The added local-link audit resolved 41 links, fences balanced in all ten
changed/new documentation files, and `git diff --check` passed.

The four WD examples rendered through `-latex` with `verified=false`.
Native Lean compilation rejected the main proof explicitly as unsupported
without writing a Lean artifact; focused tests additionally check candidate-
only and native-BT routes. No Lean axiom or proof stub is emitted.

Proof authoring used persistent release Sessions and retained accepted context
after ordinary failures. Raw segments and the final journal are retained in
`tmp/2026-10-20/function-limit-at/`. Rebuild adoption and an authoring parse
error used the documented restart/replay boundary. The final Session reports
failure because it contains intentional rejection controls; it reports no
hard termination and subsequent legal statements succeeded.

## Remaining boundary

Lean replay, one-sided/infinite approaches, infinite results, limsup/liminf,
general transcendental continuity, Heine equivalence and general composition
are not delivered by F. Algebra uses explicit named outputs and common actual
domains; quotient calls must be legal, and local transport checks a whole
target punctured neighborhood plus target accumulation. Local textbook
verification and the full Cargo/example corpus were not release gates for
this scoped change. Concurrent unrelated compiler/store/showcase changes
were preserved.
