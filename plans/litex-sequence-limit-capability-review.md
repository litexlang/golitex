# Common sequence-limit proof capability review

Date: 2026-10-20. Task: test common mathematical uses of the newly implemented
real-sequence limit interface before choosing further enhancements.

The existing rules support the algebraic, squeezing and epsilon-tail proofs
listed below. The highest-priority friction is reusable equality/domain
evidence, followed by source-facing theorem interfaces and a checked analysis
library. This assessment changes no Rust, AST, Runtime, or proof-search policy.
WD continues to require independently proved convergence.

## Executed evidence

- Current-source release build passed. Baseline HEAD:
  `5d5852763ae2bb1333084257784eedd5becddd6b`.
- The actual release executable and SHA-256, cold reproductions and results
  are recorded in the [machine-readable audit](litex-sequence-limit-capability-review.json).
- Authoring used persistent Sessions, beginning with the full checked
  reciprocal epsilon-N proof. One restart replayed the accepted prefix after
  an authoring parse error: a failed declaration was incorrectly referenced
  by a subsequent command. This was not a mathematical or kernel failure.
- The curated [common proofs](../examples/wd/sequence_limit_common_proofs.lit)
  passed a separate current-release `-strict -lang en -f` gate: exit 0,
  Normal `kind=run`, `run_result=success`, `session_terminated=false`,
  `termination=null`, and 84 accepted top-level statements. The 426-line file
  includes the initial reciprocal proof and all local supporting mathematics.
  It contains no `trust`, axioms or omitted proofs.
- Cold positive controls pass for named functions, standalone beta equality,
  candidate transport, explicit domain proofs and carrier/positivity facts;
  the audit also preserves current misses on true inputs. Such misses
  are historical capability observations, not permanent must-reject tests.
- The false strict-order inference was rejected. In the live Session,
  `lim(no_guess)=0` was rejected after only declaring `no_guess(k)=1/k`, and
  `no_guess(2)=1/2` still passed afterward. Accepted earlier limits remained
  usable after ordinary failures.

No broad Cargo, release or textbook gate was run for this proof-only review.
Concurrent Lean compiler edits were preserved and are outside its scope.

Exact positive file command used:

```sh
tmp/2026-10-20/sequence-limit/target/release/litex -strict -lang en -f examples/wd/sequence_limit_common_proofs.lit
```

Chronological authoring evidence is retained in the task-owned
`tmp/2026-10-20/sequence-limit-probes/proof_journal.json`.

## Mathematical cases

| Case | Observed proof route | Result |
| --- | --- | --- |
| Constant sequences 0, 1 and 2 | Explicit `seq_limit_constant` | Pass |
| `1/n -> 0` | Full epsilon-N proof and explicit candidate introduction | Pass |
| `1/n^2 -> 0` | Power law, pointwise computation, function equality | Pass |
| `2+3/n -> 2` | Scaling, addition, named intermediate sequence, pointwise equality | Pass |
| `1/(n+1) -> 0` | Domain lemma, shift law and pointwise transport | Pass |
| `n/(n+1) -> 1` | Rewrite as `1-1/(n+1)`, subtraction law | Pass |
| `(1+1/n)/(2+1/n) -> 1/2` | Named numerator/denominator, both limits, all-index denominator nonzero proof, quotient law | Pass |
| `sin(n)/n -> 0` | Trigonometric range bounds and squeeze between `-1/n` and `1/n` | Pass |
| `sqrt(1+1/n) -> 1` | Square-root monotonicity and squeeze between 1 and `1+1/n` | Pass |
| `(1/2)^n -> 0` | Induction `2^n>=n+1`, negative-power identities, common-denominator comparison, squeeze | Pass |
| Changing finitely many initial terms | Given equality for every `n>=2`, explicit eventual-equality law | Pass |
| Even-index subsequence | Given named `b(n)=a(2*n)`, reuse an epsilon tail and its cutoff | Pass |
| Positive limit implies eventually positive terms | Epsilon `L/2`, contradiction, tail inclusion | Pass |
| Nonzero limit implies eventually nonzero terms | Epsilon `abs(L)/2`, contradiction, tail inclusion | Pass |
| `n` has no finite real limit | Assume a candidate, extract epsilon-1 tail, choose a later index by Archimedean bound, contradict | Pass |
| Constant zero cannot have limit 1 | Explicit contradiction using uniqueness | Pass |
| `sin(1/n) -> 0` | Squeezing reduces to small-angle estimates; the needed estimate was not established here | Not completed |

These are concrete experiments, not a completeness benchmark. The geometric
test is specifically base `1/2`; the subsequence test is specifically `2*n`
with a named output. Arbitrary geometric ratios, general cofinal index maps,
Cauchy equivalence and monotone convergence were not tested.

## 1. Reuse checked anonymous-call equalities under arithmetic

This reduced reproduction contains no limit expression:

```litex
claim:
    ? forall x R:
        fn(t R) R {t}(x)-1=x-1
    fn(t R) R {t}(x)=x
    fn(t R) R {t}(x)-1=x-1
```

Current result: proof-body search fails at the subtraction equality. The
standalone beta equality `fn(t R) R {t}(x)=x` passes. This corresponding named
function control also passes in a fresh process:

```litex
have fn h(t R) R=t
claim:
    ? forall x R:
        h(x)-1=x-1
    h(x)=x
    h(x)-1=x-1
```

The same difficulty appeared inside `abs(...)` in the epsilon proof of an
anonymous even-index subsequence. Naming the output sequence allowed that
mathematical proof to proceed. A version that creates a local named function,
proves its candidate and equates it with the anonymous output still failed
at the final candidate transport; a generic named-to-named candidate equality
transport control passes.

Desired result: the first reproduction verifies while preserving argument WD
and scoped equality evidence. This deserves a focused inspection of beta/alpha
identity, known-equality lookup and congruence consumers. The precise Rust
cause and repair scope were not established; no global search change is
justified by this observation alone.

## 2. Consume composite positive-domain evidence for nonzero WD

In a fresh process this declaration is rejected with obligation
`(k+1)!=0`:

```litex
have fn shifted(k N+) R=1/(k+1)
```

Both `k+1 $in N+` and `0<k+1` verify directly under `forall k N+`.
Publishing just that universal positivity fact still does not make the
declaration pass. An explicit nonzero lemma does:

```litex
claim:
    ? forall k N+:
        k+1!=0
    0<k
    0<k+1
    k+1!=0
have fn shifted(k N+) R=1/(k+1)
shifted(1)=1/2
```

This is ordinary domain-proof friction, independent of convergence discovery.
Desired result: the original declaration consumes the already justified
positive constructor domain. Keep unrelated zero-denominator rejection intact.
The report does not claim that arbitrary nonlinear nonzero facts should be
discovered automatically.

## 3. Package source-facing output and tail interfaces

After proving `a(n)=1/n -> 0`, the affine example is checkable, but the
published algebra laws describe specific anonymous output functions. In the
successful file the author names `times_three`, proves its equality to the
scale-rule output, obtains the sum candidate, proves a pointwise equality,
then transports the candidate to `affine` before selecting its limit.

A useful future checked theorem contract would be:

```text
forall a,b seq(R),A,c,d R:
    $has_seq_limit(a,A)
    forall n N+:
        b(n)=c*a(n)+d
    =>:
        $has_seq_limit(b,c*A+d)
```

This is a proposed interface, not an implemented new native rule. It could
be a checked library wrapper around the existing laws. Similar output-taking
wrappers for powers and quotients would avoid exposing internal anonymous
constructor shapes at each caller.

The existing `seq_limit_tail` returns a cutoff with a tail/preimage inclusion.
The new example's proved `epsilon_tail_at` theorem converts it to a statement
at a chosen index:

```litex
# In the proved epsilon-tail context, with k>=cutoff:
release thm epsilon_tail_at(a,L,epsilon,cutoff,k)
# Returned fact: abs(a(k)-L)<epsilon
```

`epsilon_tail_at` is a source theorem in this example, not a builtin. It is
used by the subsequence, sign, nonzero and nonconvergence proofs. A stable
library home for this projection and the proved eventual-property theorems
would remove repeated set-membership plumbing. The cutoff remains explicit.

## 4. Add a checked elementary-limit and estimate library

The reciprocal, shifted reciprocal, reciprocal square, affine and geometric
proofs are now concrete candidates for reusable checked theorems. The
convergence consequences above can also be packaged without making WD inspect
sequence bodies.

For the remaining sine example, the following upstream mathematical estimate
was rejected even with its interval premises:

```litex
forall x R:
    0<=x
    x<=pi/2
    =>:
        sin(x)<=x
```

The stronger `abs(sin(x))<=abs(x)` direct query and the concrete
`sin(1/k)<=1/k` query also miss. This assessment did not supply a proof of
those estimates from the trigonometric foundations. It does not establish
that they are impossible to formalize. A generic sequence between `-1/n` and
`1/n` was separately proved convergent, so the remaining work is the sine
estimate/continuity mathematics and its callable interface.

Suggested order: equality reuse and positive/nonzero WD consumption first;
then output-taking and tail-use library interfaces; then checked elementary
limit theorems and elementary-function estimates/continuity. WD should keep
consuming independently established convergence evidence throughout.
