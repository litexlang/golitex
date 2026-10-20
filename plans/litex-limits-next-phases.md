# Next native limit phases

Date: 2026-10-20. Status: **F is approved and implemented**; S/I/U remain
proposals with no implementation authorization. See the
[F acceptance receipt](litex-function-limit-at-acceptance.md) and
[live interface documentation](../docs/function-limits.md).

Parent: [native limits](litex-limits.md) and
[common mathematical operations](litex-latex-math-support.md).
This continuation controls the next four increments. It supersedes the older
plan's optional body-based discovery targets and its pre-sequence AST sketch.

## 1. Goal, baseline and delivery order

Deliver finite real limit values that can be used inside ordinary expressions,
with explicit convergence proofs, exact domains, WD, BT rules and examples.
LaTeX output is a consumer; parsing raw LaTeX is a separate feature.

Already delivered: `lim(a)` and `$has_seq_limit(a,L)`, accepting `seq(R)` and
equivalent `fn(k N+) R`. [Current documentation](../docs/sequence-limits.md)
owns that interface. The [common sequence proofs](../examples/wd/sequence_limit_common_proofs.lit)
and [capability review](litex-sequence-limit-capability-review.md) are its
practical baseline, including unresolved anonymous-function equality reuse.

| Milestone | Proposed values | Proposed candidate relations | Completion boundary |
| --- | --- | --- | --- |
| F — delivered | `lim(f,x0)` | `$has_limit_at(f,x0,L)` | Finite-point, relative punctured limits of unary real-valued functions |
| S | `lim_left(f,x0)`, `lim_right(f,x0)` | `$has_limit_left(f,x0,L)`, `$has_limit_right(f,x0,L)` | Each side's own approach, algebra and ordinary/one-sided bridge |
| I | `lim_pos_inf(f)`, `lim_neg_inf(f)` | `$has_limit_pos_inf(f,L)`, `$has_limit_neg_inf(f,L)` | Unbounded input approach; output still in `R` |
| U | `limsup(a)`, `liminf(a)` | `$has_seq_limsup(a,L)`, `$has_seq_liminf(a,L)` | Finite values, with existence theorems and first acceptance focused on bounded real sequences |

Order: F, then S, then I, then U. U is mathematically independent of S/I;
its position is a delivery priority, not a false dependency. Each milestone
must finish its proof/use/output/negative-control slice before the next one.
No calendar estimate is asserted before the first implementation checkpoint.

Out of scope: infinite result values or extended-real arithmetic, derivatives,
integrals, infinite aggregates, general filters/nets, complex/vector limits,
and a general-purpose epsilon solver. This plan introduces no Env/Runtime
state, registry, cache, global search-policy or shared AST-leaf redesign.

## 2. Common contract and primary tracer

All four milestones preserve this order:

1. Check the operands and their actual complete callable domains.
2. Prove a concrete candidate relation or existence of a real candidate.
3. Use the candidate uniqueness theorem to select the real value.
4. Allow arithmetic, nested calls and selected-value equalities.

WD only consumes step 2; it does not run anchor/algebra BTs, inspect a body,
sample values, or search for a numerical answer. Even constants require an
explicit convergence theorem or definition proof. A failed proof does not
establish the negated relation. Negated candidates mean logical negation.

Native source now supports both `lim(a)` and `lim(f,x0)`. This abbreviated
proof/use excerpt omits the defining-clause proofs and is **not an executable
proof**; the [complete F tracer](../examples/wd/real_function_limit_at.lit)
has passed strict verification:

```text
have fn f(x R: x != 0) R = x^2/x
# First prove the punctured approach and epsilon-delta condition.
by def $has_limit_at(f,0,0)
lim(f,0) = 0
lim(f,0) + 2 = 2
```

Proof spine: every radius contains a nonzero real input, for example half
that radius; on legal nonzero inputs, `x^2/x=x`; for epsilon choose
`delta=epsilon`. This never calls `f(0)`. Before the candidate proof, both
selected-value lines must fail for missing evidence. A zero limiting
denominator is not a quotient-rule proof of this example.

Delivered durable tracer: `examples/wd/real_function_limit_at.lit`. Retain the
old unsupported form as comments, the complete proved route as active code,
and executable negative controls separately. No proof/WD example may use
`trust`, a local axiom or an omitted proof.

## 3. Mathematical domains and definitions

`D_f` below is mathematical shorthand for the checked complete unary domain,
including its parameter carrier and every guard. It is not a proposed public
domain operator. Require that its inputs and outputs are real, using actual
membership/inclusion evidence. Do not widen a restricted function to all of
`R` or call it at an illegal input. A multi-argument or tuple-input function
needs an explicit unary real view. If different callable sources would select
different domains, require an unambiguous checked view instead of guessing.

### F: relative, punctured finite-point limits

`has_limit_at(f,x0,L)` has operands `x0,L in R` and means both:

- Accumulation: for every `r>0`, some `x in D_f` satisfies
  `0 < abs(x-x0) < r`.
- Control: for every `epsilon>0`, some `delta>0` makes
  `abs(f(x)-L)<epsilon` for all `x in D_f` with
  `0 < abs(x-x0) < delta`.

Neither `x0 in D_f` nor a legal call `f(x0)` is required. Accumulation is a
truth condition of the relation, not an extra WD prerequisite: the relation
and its negation must remain expressible for an isolated or empty domain.
Those domains cannot provide a selected value through vacuous implications.

### S: left and right limits

Use `0 < x0-x < r` on the left and `0 < x-x0 < r` on the right. Apply the
same directional inequality to delta control. Each relation includes its
own accumulation requirement; evidence from the opposite side is insufficient.

Under the recommended relative-domain convention, the following targets
illustrate a consequential boundary; they are not current native syntax:

```text
have fn endpoint(x R+) R = x
# After the corresponding proofs:
$has_limit_at(endpoint,0,0)
$has_limit_right(endpoint,0,0)
not $has_limit_left(endpoint,0,0)
```

An ordinary candidate implies a candidate on an accumulating side only.
Matching left/right candidates imply the ordinary candidate. The common
equivalence requires accumulation from both sides, so it cannot manufacture
a left limit in this endpoint example.

### I: approach to infinity, finite output

Positive-infinity candidates require:

- For every real `M`, some `x in D_f` satisfies `x>M`.
- For every `epsilon>0`, some real `T` makes `abs(f(x)-L)<epsilon`
  whenever `x in D_f` and `x>T`.

Negative infinity reverses both inequalities: `x<M`, then `x<T`.
The domain can be sparse; unboundedness in the specified direction matters,
not containing every sufficiently large real. Empty/bounded domains cannot
provide limits at an unavailable end. The two directions are independent.

For example, after explicit candidate proofs:

```text
have fn reciprocal(x R: x != 0) R = 1/x
lim_pos_inf(reciprocal) = 0
lim_neg_inf(reciprocal) = 0
```

`lim_pos_inf(fn(x R) R {x})` has no finite value. Neither that expression nor
`lim_right(reciprocal,0)` becomes `+infinity`; infinite-output relations and
extended-real selectors require a later contract.

### U: finite upper and lower sequence limits

Inputs are the existing `seq(R)` / `fn(k N+) R`, starting at 1. Define the
finite candidate relations directly by epsilon/tail conditions:

| Candidate | Eventual bound | Hits on every tail |
| --- | --- | --- |
| Upper limit L | For every epsilon>0, some N has `a(n)<L+epsilon` for all n>=N | For every epsilon>0 and N, some n>=N has `L-epsilon<a(n)` |
| Lower limit L | For every epsilon>0, some N has `L-epsilon<a(n)` for all n>=N | For every epsilon>0 and N, some n>=N has `a(n)<L+epsilon` |

Both clauses are essential: an eventual upper bound alone is not a limsup.
This keeps the candidate meaning faithful without requiring public selected
`sup`/`inf` operators as a prerequisite.

U's existence theorems and first positive examples cover bounded real
sequences. The candidate definitions retain their ordinary finite meaning;
they do not insert global boundedness into the definition. A proved finite
candidate is sufficient for WD, even if a later author proves it for a
sequence unbounded in the opposite direction. No general unbounded-sequence
existence or infinite value is promised. Boundedness alone enters through an
explicit existence theorem, never a new WD discovery route.

Quantifier encoding must respect the current language: existential bodies are
quantifier-free. Eventual clauses can use tail/neighborhood inclusion in a
preimage set, as existing sequence limits do. Accumulation and every-tail
hits use an existential point/index with only atomic conditions. Do not add
unapproved quantifier shapes or recognize user predicates by their names.

## 4. Explicit BTs and mathematical prerequisites

F's final call contracts are recorded in [the live documentation](../docs/function-limits.md).
S/I/U names remain proposed call families whose final argument contracts
must be recorded before implementation. The mathematical premises
below are mandatory regardless of spelling. Every BT retains its real
premise proofs. Algebra BTs prove candidate facts; selected-value equalities
follow afterward, rather than supplying their own existence premises.

### F rules

- `fn_limit_at_from_epsilon`, `fn_limit_at_control`: introduction from both
  defining clauses, and elimination to an epsilon/delta neighborhood.
- `fn_limit_at_unique`, `fn_limit_at_exists`, `fn_limit_at_selected`:
  uniqueness, existential introduction, and selection from proved existence.
- `fn_limit_at_constant`, `fn_limit_at_identity`: explicit anchor calls,
  with actual accumulation evidence for restricted domains.
- Negation, scale, sum, difference, product, natural powers, absolute value
  and quotient. Quotient requires a nonzero denominator limit and a legal
  quotient function on its own domain.
- Local equality, eventual comparison, squeeze; positive/nonzero limit
  implies eventual positivity/nonzero values, as reusable local facts.

Algebra must not silently intersect or enlarge domains. The first calls use
functions with a common checked domain, or explicit restricted views on that
domain. Support a caller-supplied output function with a checked pointwise
operation equation, so the API can conclude a candidate for the actual named
output rather than force anonymous-result equality adapters. Exact call
signatures and domain obligations are an F checkpoint before coding rules.

Local transport between different domains needs its own explicit premise:
on some punctured neighborhood every target input is legal for the source,
and the two values agree there; the target must accumulate. Agreement only
on a sparse intersection is insufficient. This is an alternative proof route
for the primary tracer, whose delivered file uses direct epsilon-delta control.

First F acceptance includes constant/identity, polynomial and rational
examples, local equality and squeeze. General trigonometric/exponential/log
continuity, the Heine equivalence and a continuity API are subsequent scope.
Composition is also subsequent: punctured outer and inner limits alone fail
when the inner function repeatedly equals the excluded point. No implicit
composition shortcut or change to the existing strict `compose` is planned.

### S rules

Each direction gets introduction/control, uniqueness/existence/selection,
anchors, local equality, algebra, comparison and squeeze under its own
domain conditions. Reuse internal algebra obligation construction where it
is identical, while retaining the direction in evidence and output.

Add `fn_limit_at_to_left/right` with the corresponding accumulation premise,
`fn_limit_from_sides` for matching candidates, and a mismatch theorem proving
no ordinary finite candidate when established side values differ.
Do not infer nonexistence merely because search failed.

### I rules

Each unbounded direction gets introduction/control,
uniqueness/existence/selection, constants, local/eventual equality, algebra,
comparison and squeeze. Add explicit reciprocal and reciprocal-power proofs
using thresholds and Archimedean/order facts. Rational examples follow by
algebra and legal domain restrictions, not a body-matching WD shortcut.

Reciprocal substitution between a side of zero and an infinite end can be a
later explicit bridge. It is not required to implement I and must not pull
general filter composition into the first increment.

### U rules and existence subphase

1. Epsilon introduction and elimination; unique candidate;
   existence/selection for upper and lower limits.
2. Explicit bounded-sequence existence BTs, consuming a real bound `M>0`
   and a proved `forall n N+: abs(a(n))<=M`.
3. Convergence to L implies both candidates L; conversely both candidates L
   imply `$has_seq_limit(a,L)`. Prove these relationally before using `lim`.
4. `liminf(a)<=limsup(a)` when both finite candidates exist; eventual order
   comparison, finite initial changes and shifts.
5. Negation swaps upper/lower with a minus sign; addition of a constant,
   nonnegative scaling, and negative scaling with the appropriate swap.
6. For bounded inputs and the required candidate evidence, upper limits of
   sums are subadditive and lower limits are superadditive. Adding a
   convergent sequence gives equality with its limit. General products and
   quotients remain later laws with separately specified sign conditions.

Do not assume existence because new names parse. U includes a real
completeness subphase: for each tail, construct its nonempty bounded range;
obtain a least-upper-bound certificate; assemble its unique tail supremum
sequence; prove it decreases and is bounded below; prove monotone convergence
from completeness; then derive the epsilon characterization above. Derive
the lower construction by the dual/negation route. These are local proof
dependencies, not a demand to ship a public `sup`/`inf` value family first.

Mine the [Analysis Chapter 6 development](../showcases/analysis/chapter06-sequential-limits.lit)
for this proof spine, but use its [recorded foundation boundary](../showcases/analysis/README.md).
Its axiomatic background is not a new strict native proof. Reuse the existing
[native completeness contracts](../src/execute/execute_by_stmt/builtin_thm/real_analysis.rs)
with their actual mathematical trust boundary and retained certificate
evidence. A missing completeness or monotone-convergence bridge is an explicit
U obligation, not permission to add an opaque existence oracle.

## 5. Semantic decisions proposed for review

The F relative-domain choice below was implemented under the user's stage-F
approval. Choices specific to S/I/U remain recommendations.

| Decision | Recommendation | Material alternative and cost |
| --- | --- | --- |
| Finite-point approach | Relative to the actual domain, with accumulation | Requiring both accumulating sides rejects `lim(endpoint,0)` in section 3; endpoint proofs use only `lim_right`. Either convention is coherent, but changing later changes accepted statements |
| Result carrier | `R` for all four milestones; infinity describes input approach | Extended reals allow `lim_pos_inf(identity)=+infinity`, but require a new carrier, domain rules and partial arithmetic before safe nested use |
| U's initial scope | Bounded-sequence existence/acceptance; faithful finite candidates | Requiring global boundedness even after a finite candidate is proved is narrower and adds a WD premise; extended-real total selectors are a larger independent feature |

The proposed native API keeps existing `lim(a)` and adds fixed-arity
`lim(f,x0)`. A source-library alternative can express candidate `prop`s and
`have fn ... by exist!`, but requires imports and does not itself deliver the
requested native operations/BT evidence. No extra abstraction is needed to
make that alternative available.

## 6. AST scope — F approved; S/I/U proposed

The user explicitly approved the first stage on 2026-10-20. Only
`Function(FunctionLimit)`, `FunctionLimit`, `LimitApproach::AtPoint`, and
`HasFunctionLimitFact` / `NotHasFunctionLimitFact` below have been added.
The full sketch also displays later, unapproved S/I/U additions; none of
those dormant variants or payloads have been added.

Existing `SequenceLimit`, `HasSequenceLimitFact` and
`NotHasSequenceLimitFact` retain their current fields. Extend the existing
`LimitOperator` rather than introducing another `Obj` family:

```rust
enum LimitOperator {
    Sequence(SequenceLimit),                 // existing
    Function(FunctionLimit),                 // F
    SequenceLimsup(SequenceLimsup),           // U
    SequenceLiminf(SequenceLiminf),           // U
}
struct FunctionLimit {
    function: Box<Obj>,
    approach: LimitApproach,
}
enum LimitApproach {
    AtPoint(Box<Obj>),                       // F
    FromLeft(Box<Obj>),                      // S
    FromRight(Box<Obj>),                     // S
    AtPositiveInfinity,                     // I
    AtNegativeInfinity,                     // I
}
struct SequenceLimsup { sequence: Box<Obj> }
struct SequenceLiminf { sequence: Box<Obj> }

// Add the six corresponding AtomicFact variants and payloads.
struct HasFunctionLimitFact {
    fact_id: FactId, function: Obj, approach: LimitApproach, value: Obj,
    line_file: Option<SourceLine>,
}
struct NotHasFunctionLimitFact {
    fact_id: FactId, function: Obj, approach: LimitApproach, value: Obj,
    line_file: Option<SourceLine>,
}
struct HasSequenceLimsupFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
struct NotHasSequenceLimsupFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
struct HasSequenceLiminfFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
struct NotHasSequenceLiminfFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
```

The six new AtomicFact variants have those exact names and contain their
same-named payload. F adds only Function/AtPoint and its two facts; S adds
only the two sided approaches; I adds only the two infinite approaches;
U adds its two values and four facts. Do not add dormant variants ahead of
their milestone. Constructor visibility/derives follow existing conventions.

These values preserve operation/direction identity for parser, WD,
substitution, alpha normalization, IR/congruence, diagnostics and LaTeX.
Dedicated leaf objects/facts make that responsibility explicit. Ordinary
calls or display-only maps do not retain native operation and mathematical
negation identity across those consumers; they remain the library alternative.

Fields own recursive expressions for the lifetime of the parsed value/fact.
They do not own proof results, inferred signatures, caches, selected answers
or permanent display binders. Stage-ordered execution/proof results own the
checked callable/domain, quantified approach/control, candidate/existence
and uniqueness evidence, including local scopes and source FactIds.
No existing payload field, Stmt, Identifier or Env/Runtime contract changes.
Further AST authorization is required before S/I/U implementation. Neither
the earlier sequence-only approval nor the later F approval covers them.

## 7. Owners and dependency order

| Responsibility | Existing owner / extension boundary |
| --- | --- |
| Operation and candidate identity | `src/ast/obj.rs`, `src/ast/fact/atomic.rs`; approved new arms only |
| Names, arity, positive/negative syntax | Object/fact parsers and reserved vocabulary; preserve one-argument sequence `lim` |
| Domain and WD | [Checked complete domains](../src/execute/execute_fact_stmt/function_domain.rs) and object-WD branches; consume proof evidence |
| Definitions, BTs and equality | Existing explicit definition/theorem and atomic/equality owners; new branch evidence |
| Recursive consumers | Instantiation, alpha normalization, identity/congruence, JSON/diagnostics, LaTeX, Lean dispatch |

Dependency edges, not just delivery order:

```text
real arithmetic + checked complete domains --definition--> approach/control
approach/control --definition--> function candidate
candidate --proof--> uniqueness; candidate --existence--> finite existence
finite existence + uniqueness --WD/selection--> value
candidate + arithmetic/local domain facts --proof--> algebra/locality/squeeze
directional candidates --proof--> side/ordinary bridges

seq(R) + epsilon/tails --definition--> finite upper/lower candidate
native completeness + tail ranges --existence--> tail extrema
tail extrema + checked monotone convergence --proof/existence--> U existence
U candidate + uniqueness --WD/selection--> limsup/liminf
sequence candidate + U candidates --proof--> convergence equivalence
```

F/S/I share obligations where mathematically identical, not a new general
filter framework. U uses sequence tails and completeness independently.
Proof results must mirror each real verification stage; do not add generic
optional fields to old results or change shared search/rollback contracts.
Expected implementation classification is R1 branch extensions with L3
producer/consumer checks; reclassify only on evidence of a shared change.

Before reserving the new public names and BTs, scan declarations, binders,
fields and exports. The initial focused public `.lit` declaration scan found
no exact proposed new names; this is not a complete compatibility inventory.
`lim` is already native/reserved. Inspect local-only projects read-only if a
collision inventory needs them; no implicit `scripts/` migration is authorized.

## 8. Acceptance and checkpoint protocol

All new source below is an acceptance target, not an observed pass.

| Milestone | Mathematical positive cases | Required counterexamples / missing-premise controls |
| --- | --- | --- |
| F | Constant, identity, `x^2` at 3, `(x^2-1)/(x-1)` at 1, primary `x^2/x` at 0, squeeze and nested use | Value before candidate; false constant result; empty/isolated domain; wrong arity/carrier; illegal call `f(0)`; quotient with zero limiting denominator cannot use quotient BT; local equality only on an intersection |
| S | Left/right values -1/+1 for `abs(x)/x`; both sides of `x^2` at 0; relative endpoint; equal-sides theorem | Jump has no ordinary finite limit; unavailable side; forgetting a side's accumulation; false equality of side values |
| I | `1/x`, `1/x^2` to zero at both ends; `(2*x+1)/(x-1)` to 2; constant on an unbounded domain | Identity has no finite limit; bounded/empty domain; domain unbounded in only one direction; unsupported infinite result; quotient call outside its domain |
| U | Constants and reciprocal; `(-1)^n` gives upper 1/lower -1; convergent sequences give equal values; bounded existence; shift/finite changes and negation; both `seq(R)` and equivalent `fn(k N+) R` inputs | No finite upper/lower selector for `a(n)=n`; finite/incomplete sequence interfaces rejected; boundedness does not imply convergence; no limsup additivity: for `a(n)=(-1)^n`, `b(n)=-a(n)`, the sum has upper limit 0 while individual upper limits sum to 2 |

Planned durable files: F's primary file above,
`examples/wd/real_function_limit_sides.lit`,
`examples/wd/real_function_limit_infinity.lit`, and
`examples/wd/sequence_limsup_liminf.lit`. Add one focused theorem example per
delivered rule in the existing builtin-theorem examples family, plus
executable negative fixtures. These paths are planned, not present deliveries.

For each milestone:

1. Freeze its public/semantic choices and exact protected AST scope. Finalize
   every BT's ordered arguments and quantified premises before coding it.
2. Implement candidate introduction/elimination and uniqueness; then WD and
   selected value; then laws. Do not use a selected value to prove its own
   existence. Keep the earlier native sequence branch as a regression anchor.
3. Author the complete positive proof in one live release `-session`, journal
   distinct attempts, and retain accepted context after ordinary failures.
4. Verify scope retention and no evidence leakage after failures; reject
   circular/undefined nested forms. For example, the following proposed
   control must fail even though its function is constant:

   ```text
   have fn unproved(x R) R = 3
   0*lim(unproved,0) = 0
   ```

   After an explicit constant-limit theorem proves its candidate, the same
   equality must pass. Multiplication by zero cannot erase the WD obligation.
5. Check producers and consumers: binders/capture, substitution, congruence,
   real membership, proof provenance/JSON, all supported diagnostics languages,
   and LaTeX with the actual domain/direction and fresh display binders.
6. Until a separately scoped Lean bridge exists, each new object, relation,
   WD and proof route must fail closed explicitly, without an axiom or stub.
7. Save and strictly run the actual public files; update current docs only
   after their representative routes pass. Record exact tests/binary/commands.

Positive CLI evidence requires exit 0 and Normal JSON `kind=run`,
`run_result=success`, `session_terminated=false`, `termination=null`.
Negative controls must fail for the documented reason, distinguishing missing
proof, invalid WD and mathematical nonexistence. False mathematical claims
need explicit contradiction/nonexistence proofs, not just failed searches.

Build/test only the new branch producers and directly affected consumers,
the saved files and affected executable docs. Rust test filters must match
actual registrations. No blanket release or local textbook gate is implied.

## 9. Planning evidence and implementation handoff

This plan uses read-only source inspection of the native sequence/domain/
completeness interfaces and the calculus/Analysis designs. The old calculus
showcase's general limits are still designs; the Analysis proof spine has
explicit foundational assumptions. Reading either is not new verification.

Planning acceptance consists of mathematical/domain/decision audits, local
link and fence checks, whitespace checks and a scoped file-change audit.
At that planning checkpoint no future syntax, AST proposal, BT call or proof
here had been executed. The later F receipt below supersedes that status for F.

Planning checks on 2026-10-20 passed for this continuation and both parent
plans: 50 local links/anchors resolve, 16 non-executable code fences are
balanced, all seven proposed value spellings are present, and scoped
whitespace checks pass. This task edits only those three planning documents;
prior examples and concurrent compiler/showcase work remain outside its delta.

F delivery is complete: proof-consuming WD, 22 explicit BT contracts, strict
positive/negative examples, recursive/output consumers, and an explicit
unsupported Lean boundary. Exact validation and remaining limits are recorded
in the [F receipt](litex-function-limit-at-acceptance.md). The requested goal
skill is installed as `$litex-function-limit-at`.

S is next in the proposed delivery order. Its approach variants and bridge
rules still require their own approval and implementation; S/I/U remain
separately reviewable increments rather than automatic scope expansion.
