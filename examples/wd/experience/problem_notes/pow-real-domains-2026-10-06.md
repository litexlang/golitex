# Real power WD and semantic consistency, 2026-10-06

Task provenance: the user authorized extending `^` well-definedness and
correcting conflicting semantic documentation. The displayed-set convention
was explicitly accepted and remains unchanged. This is a completed local Rust
semantic repair in golitex, not a whole-repository semantic certification.

## Original behavior and accepted tracer

These exact original inputs failed in power WD, because symbolic powers were
limited to integer exponents:

```litex
forall x R+:
    x^(1/2)=x^(1/2)
forall x R:
    exp(x)=e^x
```

Both now pass unchanged without trust. The maintained
[tracer](../../pow_real_domains.lit) also checks general real powers and their
real carrier, a guarded nonnegative base, zero with a positive real exponent,
the existing integer and closed rational domains, function-body reuse, and
`log(a,a^t)=t` under the usual positive-base and `a!=1` guards.
The [journal](../../proof_journals/pow_real_domains_2026-10-06.json) retains the
before receipts, materially distinct failed attempts, persistent frames, raw
test output, source manifests, and CLI hashes.

## Implemented contract

Pow WD first checks both child objects. Its existing branches retain their
order: closed positive rational base with a rational noninteger exponent,
real base with a natural exponent, complex base with a natural exponent, and
nonzero complex base with an integer exponent. Two new branches follow:

- A base in `R+` with an exponent in `R`.
- A base in `R`, a proved `0<=base`, and an exponent in `R+`.

The selected branch retains the actual requirement proofs and both child WD
proofs. Requirement search inherits the caller's `VerifyState`; no new
top-level state or search ceiling was introduced. On complete failure, the
existing integer-domain failure payload is retained. Negative bases with
noninteger exponents and general complex exponents remain unsupported; zero
with a negative exponent remains illegal. Natural powers retain `0^0=1`.

The existing real-carrier and fixed-base equality consumers now describe the
expanded WD contract accurately. Their Rust and Detailed rule identifiers
are `RealPower` and `ExpAsEulerPower`, replacing `RealIntegerPower` and
`ExpAsEulerIntegerPower`. The existing payload fields are unchanged, including
`base_in_real_proof`. Actual English and ten-language output is tested.

Manual, Reference, FAQ, the current DEC05 status, JSON output documentation,
example indexes, and Pow's AST comment agree with this contract. Dated
historical failure records remain intact. The old plan wording that rejected
`0^0` was corrected to the established `0^0=1` convention.
An unrelated concurrent documentation merge moved Reference's O27 entry into
Manual; the current entry retains the checked domain and exact example,
while Reference now redirects readers to Manual.

## Acceptance evidence

The current-source release CLI was built with
`cargo build --release --offline --lib --bin litex`. Build and acceptance
snapshots had no source drift. A final comment-only correction was rebuilt;
its receipt is separately recorded in the journal.

The following six focused release suites passed: `exact_rational_powers`
(13), `native_fixed_base_tests` (5), `power_laws` (3),
`real_arithmetic_constructor_closure` (5), `common_obj_relations` (6), and
`log_algebra_base` (7): **39 distinct tests**, zero failures or ignored tests.
Each used `cargo test --release --offline --lib <filter> -- --nocapture`.
They include selected typed WD evidence, inherited permission boundaries,
failed-binding rollback with valid same-name reuse, Detailed fields, and
language output. Public runtime execution remains the behavioral test entry.

The final persistent release session accepted all eight maintained scopes
and rejected both executable controls. Redundant self-equalities following
the real-carrier goals were deleted and the reduced scopes were rechecked.
The cold file gate was:

```sh
target/release/litex -strict -f examples/wd/pow_real_domains.lit
```

All **18 cold receipts** matched: four maintained files and two changed
documentation snippets passed with exit 0, top-level `success:true`, and no
session error; twelve illegal or false controls returned exit 1,
`success:false`, and no session error. Those controls cover missing positivity
or nonnegativity, negative fractional bases, complex fractional powers,
complex exponents, zero negative powers, illegal child expressions, false
`0^0=0`, and a false positive-base power equality. The existing fixed-base,
closed rational, and scalar sqrt tracers remain green.

One old log negative test contained the mathematically valid statement
`log(a,x^y)=y*log(a,x)` for `a,x,y R+` and `a<1`. Its former failure was caused
by power WD. The exact source is now a positive regression; illegal domains,
missing base guards, and the wrong coefficient `(y+1)` remain negative tests.
The original red receipt is retained. An initial Rust borrow-check failure
and an invalid test setup were repaired and retained as attempts, rather than
being counted as accepted evidence.

## Preserved adjacent boundaries

WD legality does not add every power identity or exact evaluator case. The
persistent diagnostics preserve these separate truth-search boundaries:

```litex
forall a,x R+:
    a!=1
    =>:
        a^log(a,x)=x
forall x R+:
    x^(1/2)=sqrt(x)
forall t R+:
    0^t=0
```

The first direct inverse leaf still requires `a>1`; the second lacks the
direct symbolic square-root identity; the third existing zero-power equality
leaf requires a positive natural exponent. These are valid mathematical
targets and were not reclassified as illegal WD. The exact evaluator's
fractional-power contract was not changed.

No trust, project axiom, AST field, Env/Runtime state, global dispatch,
displayed-set convention, or search policy was added or changed. The source
tree already contained unrelated working changes; baseline status and source
fingerprints are retained. This task certifies the recorded current-source
focused gates. Whole-project, textbook, Lean, replay, and release gates were
outside this local contract change and were not run.

The useful reusable distinction is explicit: a power domain certificate
establishes that an expression denotes a supported object; a truth-search
rule and an exact evaluator each retain their own separately checked domain.
