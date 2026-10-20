# Native limits: mathematical and implementation plan

Date: 2026-10-20. Status: the sequence-only increment below is implemented;
its acceptance receipt is recorded separately below. The broader function,
one-sided, infinity and limsup/liminf roadmap remains a design proposal.

Parent: [common LaTeX mathematics roadmap](litex-latex-math-support.md).

## Current execution scope — real sequence limits only

On 2026-10-20 the user requested implementation of `lim(a)` with public
domain `seq(R)`, also accepting its equivalent `fn(k N+) R` interface, and
the matching WD and BT rules. This narrows the next increment to sequences;
the broader A–D roadmap below remains subsequent scope.

The sequence-only protected AST proposal is exactly:

```rust
// Add this Obj variant and this new family and leaf.
Obj::LimitOperator(LimitOperator)
enum LimitOperator { Sequence(SequenceLimit) }
struct SequenceLimit { sequence: Box<Obj> }

// Add these positive/negative AtomicFact variants and their leaves.
AtomicFact::HasSequenceLimitFact(HasSequenceLimitFact)
AtomicFact::NotHasSequenceLimitFact(NotHasSequenceLimitFact)
struct HasSequenceLimitFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
struct NotHasSequenceLimitFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
```

The Obj preserves operation identity through parsing, verification and
presentation. The facts represent the actual epsilon-tail relation and its
logical negation, rather than recognizing a user predicate by spelling.
These recursive values carry no inferred signature, proof, cache or selected
answer; existing proof results own the evidence. No existing payload fields,
Stmt, Identifier or Env/Runtime state contracts are changed. A source-library
selector using existing `have fn by exist!` remains possible, but requires an
import and does not provide the requested native branches and BT interface.

The user explicitly approved these concrete sequence-only AST additions on
2026-10-20. This approval does not include function-limit payloads or additional
Fact shapes.
The behavior contract is: `$has_seq_limit(a,L)` checks sequence membership and
real `L`, its truth follows epsilon-tail convergence; `lim(a)` additionally
requires independently established finite convergence. The first acceptance
file is `examples/wd/sequence_limit.lit`, with `1/k -> 0` and downstream use;
oscillating/diverging sequences receive no default value.

### Proof route before selected-value convenience

The user challenged the proposed two-line `a(k)=1/k; lim(a)=0` tracer because
it omitted the convergence proof. The revised first-delivery recommendation
is proof-driven selection: WD consumes independently established convergence;
it does not inspect the sequence body to discover its limit. This refinement
was confirmed by the user before native implementation.

Proof/use structure (the complete executable proof is in the acceptance example):

```text
have fn a(k N+) R = 1/k
claim:
    ? $has_seq_limit(a,0)
    # Supply the epsilon-N proof here.
lim(a) = 0
lim(a) + 2 = 2
```

The actual mathematical proof is: for each positive epsilon choose a positive
natural N greater than 1/epsilon, using the existing Archimedean interface.
For k>=N, positivity gives 0<1/k<=1/N<epsilon. Only after that candidate fact
has been proved should the selected value become available. A named theorem
may package this checked argument for explicit later use.

Recommended order within this sequence-only increment:

1. Candidate relation and an explicit epsilon-tail proof introduction route.
2. Uniqueness, then WD from a proved candidate/existential and real membership.
3. Equality of the selected limit with an established candidate, followed by
   ordinary equality substitution in downstream expressions.
4. Algebra, eventual equality/shifts, order and squeeze from their actual
   proved limit and tail premises. Each BT retains those premise proofs.

The first acceptance distinguishes `lim(a)=0` before and after the candidate
proof. Body-based discovery, including a special reciprocal-sequence match,
is not part of the revised recommendation. The broader roadmap's constructor
automation is deferred rather than being performed inside WD.

Proof-interface implementation note: current existential bodies are
quantifier-free, so an epsilon-tail definition cannot insert a raw nested
forall there. First derive a faithful representation using existing tail
restrictions, function ranges/subsets or an explicit witness interface; do
not silently add unapproved helper Fact payloads or recognize user props by
their spelling. Preserve the ordinary forall-epsilon / exists-cutoff meaning.

## Delivered sequence-only acceptance receipt (2026-10-20)

The user confirmed proof-driven selection and approved the exact AST additions
above. Implemented: native `lim(a)`, positive/negative `has_seq_limit` facts,
epsilon-tail definition introduction, proof-consuming WD, selected-value and
uniqueness equality rules, real membership, recursive substitution/identity,
JSON evidence, capture-avoiding LaTeX, and 18 explicit `seq_limit_*` theorems.
No Env/Runtime fields or shared proof-search ceilings changed.

- Release build passed using the task-isolated Cargo target directory.
- `cargo test --release --lib sequence` passed 28 tests, including 12 new
  sequence-limit tests. They cover explicit reciprocal convergence, candidate
  versus existence interfaces, failure/context retention, guarded quotient and
  shift WD, real domains, negation identities, algebra/order/locality laws,
  missing premises, reserved names, substitution, JSON and compiler boundaries.
- Five adjacent filters passed: `function_composition` (17),
  `native_latex_operations` (7), `compile_to_latex` (12), `builtin_thm` (23),
  and `prop_domain` (4).
- All 18 theorem fixtures passed in one persistent release Session with
  `seq(R)`, then all 18 passed with equivalent `fn(index N+) R`. Ordinary
  negative probes preserved earlier accepted declarations and facts.
- Final current-binary CLI gates passed 22 public strict positive examples,
  two newly added documentation blocks and five public must-fail controls.
  Positive runs had exit 0, Normal `kind=run`, `run_result=success`,
  `session_terminated=false`, `termination=null`; negative runs had nonzero
  exit, `run_result=failure` and no hard termination.
- Selected-value output passed in all ten CLI languages. LaTeX rendering
  succeeded with `verified=false`; unsupported Lean compilation rejected the
  source explicitly without producing a Lean artifact.
- The two public source-owned selectors were renamed `sequence_limit_value`.
  The nutshell passed strict verification. Analysis Chapter 6 parsed/rendered
  successfully; its optional complete registered-prefix execution ended with
  exit 143 before a run result, so full Analysis verification is not claimed.
  No local-only `scripts/` source was changed or used as a release gate.

One existing adjacent audit is still failing:
`every_rule_impl_owns_ten_methods_and_a_selection_only_dispatcher` compares
literal `match lang` text with the unchanged Dvd dispatcher's `match language`.
Both mismatching sources already occur in HEAD; neither was changed here.
The other two `rule_language_methods` tests pass. This is recorded separately
from the passing new rule/output checks.

Durable sources: [complete reciprocal proof](../examples/wd/sequence_limit.lit),
[both input/existence interfaces](../examples/wd/sequence_limit_interfaces.lit),
[strict-order countercheck](../examples/equal_negative/sequence_limit_strict_order.lit),
and [focused Rust tests](../tests/unit/execute/sequence_limit/tests.rs).
Every explicit theorem has a matching `seq_limit_*.lit` file under
`examples/stmt_nodes/release_and_expand/builtin_thm/`; selection and uniqueness
also have direct equality-rule tracers. All feature proof/WD tracers are free
of `trust`. Function limits and the broader roadmap remain unimplemented.

The sections below preserve the original broader design. Current delivered
semantics and rules are specified in [Real sequence limits](../docs/sequence-limits.md).

## 1. Goal and proposed delivery boundary

Make limits usable as mathematical relations and, when justified, as values in
ordinary Litex expressions. Preserve precise domains and explicit evidence;
LaTeX rendering is one consumer of this interface.

Recommended order:

| Increment | Included | Deliberately later |
| --- | --- | --- |
| A | Real sequences indexed by `N+`; finite real limits of unary real functions at finite points; candidate relations, nontrivial approach, uniqueness, selected values, elementary rules and explicit epsilon proofs | One-sided and infinite approaches, infinite result values |
| B | Left/right finite limits, their relation to the ordinary limit | Infinity as a value |
| C | Finite real limits as the input tends to positive/negative infinity; relations describing divergence to infinity | Extended-real arithmetic |
| D | Finite `limsup`/`liminf`, initially for bounded real sequences | Unbounded extended-real selectors, general filters, nets, metric/topological spaces, vector/complex limits |

The first implementation should finish A as a complete vertical slice before
adding B. The full plan includes B–D, rather than calling A all of calculus.
Derivatives, integrals and infinite sums/products remain separate consumers.

## 2. Independently established source baseline

These are source inspections, not fresh verifier results:

- [The real-analysis nutshell](../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit)
  defines epsilon-tail relations, convergence, a uniqueness theorem, and a
  guarded `have fn lim by exist!`. Its [README](../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/README.md)
  records earlier strict verification; it is not an automatically loaded API.
- [Analysis Chapter 6](../showcases/analysis/chapter06-sequential-limits.lit)
  already develops sequence limit laws, boundedness, monotone convergence,
  finite limsup/liminf, infinite divergence and subsequences. Mine its
  statements and proof routes before writing replacements. The enclosing
  [collection](../showcases/analysis/README.md) has explicit foundation
  assumptions and a dated non-strict acceptance; importing it wholesale does
  not establish a new strict native limit interface.
- [The calculus design](../showcases/math_concepts_in_litex/7_calculus/math_collections.md)
  already specifies relative, punctured function limits and the need for a
  non-isolated approach point. Its executable source currently implements
  derivative candidates, rather than that general function-limit interface.
- [Obj](../src/ast/obj.rs) and [parser vocabulary](../src/parse/keywords.rs)
  have no native limit operation. Existing local `lim` declarations must be
  considered before reserving that name.
- [Complete function domains](../src/execute/execute_fact_stmt/function_domain.rs)
  retain checked signatures, guards and sources. These are the starting point
  for deriving the actual unary domain, rather than calling `f(a)` to infer it.
- [Existential verification](../src/execute/execute_fact_stmt/verify_exist_shaped_fact/verify_exist_shaped_fact.rs)
  includes an Archimedean reciprocal-bound rule; [native real-analysis theorems](../src/execute/execute_by_stmt/builtin_thm/real_analysis.rs)
  provide natural upper bounds and completeness certificates. Their presence
  is a dependency lead, not a claim that every epsilon argument is automatic.

Current source excerpt, in its showcase context:

```text
prop is_convergent_sequence(a fn(index N+) R):
    exist L R st {$has_limit(a, L)}

have fn lim by exist!:
    ? forall a fn(index N+) R:
        $is_convergent_sequence(a)
        =>:
            exist! L R st {$has_limit(a, L)}
```

## 3. Primary tracer and nearest boundaries

Proposed source, not executable in the current language:

```text
have fn f(x R: x != 0) R = x^2/x
lim(f,0) = 0
```

Before: the function itself is expressible, but there is no native two-argument
`lim` operation. Now, as a design target: the expression denotes the unique
finite limit without evaluating `f(0)`. The proof route is punctured local
equality to the identity function, an approach-point proof and the identity
limit. A division rule with denominator limit zero cannot justify it.

First establish this route with explicit candidate/local-equality facts and a
theorem call; the bare two-line form is a separate bounded-automation target.
Do not hide an unimplemented proof route behind its proposed concise syntax.

Planned durable acceptance file: `examples/wd/real_function_limit_at.lit`.
It should preserve the former unsupported syntax as comments, keep the new
checked code active, and point to executable negative controls.

Nearest controls:

```text
lim(fn(n N+) R {(-1)^n})       # no finite limit
lim(fn(n N+) R {n})           # no finite real limit
lim(fn(x {0}) R {7},0)        # isolated approach point
lim(fn(x {}) R {7},0)         # empty approach domain
lim(fn(x R) R {sign(x)},0)    # incompatible left/right limits
```

These selected-value expressions must not acquire default values. Rejecting
an unproved value is not itself a proof of nonconvergence. The implementation
tests must distinguish false claims from true claims outside search coverage.

## 4. Mathematical spine and public interfaces

Keep three distinct roles: a candidate relation, existence of a candidate,
and the uniquely selected value. They cannot justify one another circularly.
All public spellings below are proposals.

| Role | Proposed interface | Contract / immediate consumer |
| --- | --- | --- |
| Sequence candidate | `$has_seq_limit(a,L)` | `a` has the checked complete interface `fn(n N+) R`, `L in R`; epsilon-tail convergence |
| Function candidate | `$has_limit_at(f,a,L)` | Unary real domain, real outputs, `a,L in R`; punctured relative convergence plus nontrivial approach |
| Existence | `exist L R st {$has_seq_limit(a,L)}` or its function counterpart | No selected `lim` appears in this premise |
| Unique value | `lim(a)` / `lim(f,a)` | Returns a real only after finite-limit existence and uniqueness evidence |
| One-sided candidate/value | `$has_limit_left(f,a,L)`, `$has_limit_right(f,a,L)`; `lim_left(f,a)`, `lim_right(f,a)` | Each direction owns its own accumulation and convergence obligations |
| Finite value at infinity | `lim_pos_inf(f)`, `lim_neg_inf(f)` | Inputs tend to an unbounded end of the actual domain; result remains real |
| Infinite divergence | Separate positive/negative divergence relations | Statements about growth, not elements of `R` |
| Upper/lower limits | `limsup(a)`, `liminf(a)` in D | Selected finite values on the stated bounded-sequence domain |

Existence convenience predicates may be added as derived public vocabulary,
but they must be defined by these existential relations. A second opaque
convergence certificate is unnecessary.

### Sequence meaning

For every `epsilon > 0`, there is `n0 in N+` such that every `n in N+` with
`n >= n0` satisfies `abs(a(n)-L) < epsilon`. Indexing starts at 1, matching the
existing analysis interface. A function on `N` can be passed through an
explicit `fn(n N+) R {a(n)}` restriction. Do not silently reinterpret an
arbitrary guarded natural-domain function as a complete sequence.

### Function meaning and nontrivial approach

Write `D_f` only as mathematical shorthand for the checked complete unary
domain, including parameter carriers and guards. No new public domain object
or Env registry is proposed.

The at-point candidate means both:

1. For every `r > 0`, some `x in D_f` has `0 < abs(x-a) < r`.
2. For every `epsilon > 0`, some `delta > 0` makes
   `abs(f(x)-L) < epsilon` for every `x in D_f` with
   `0 < abs(x-a) < delta`.

The first condition prevents empty and isolated domains from making every
real a candidate by vacuous implication. It belongs to the relation's truth
conditions, rather than being assumed silently in a uniqueness rule. Neither
`a in D_f` nor `f(a)` is required. Each `f(x)` call remains guarded by the
actual domain. A false but well-formed candidate relation can still be
negated; its WD must not require convergence in advance.

For a left/right relation replace the punctured-distance test with
`a-r < x < a` / `a < x < a+r`, including the matching one-sided accumulation
condition. At positive/negative infinity require arbitrarily large/small
points in `D_f`; a bounded or empty domain must not yield vacuous limits.

### Selection and WD, in dependency order

1. Verify the operands and obtain their checked complete callable interface.
2. Check real input/output carriers and the chosen approach data.
3. Consume a proved existential or a proved concrete candidate, including its
   nontrivial approach evidence. Bounded constructor rules may independently
   construct such evidence for supported elementary cases.
4. Attach the uniqueness route for that approach and select its real value.
5. Permit use inside arithmetic, another function call, or a later theorem.

`lim(f,a)=L`, its own result membership, or an expression containing that
unverified `lim` may not prove step 3. Missing evidence should identify the
unproved convergence/approach obligation; it must not report a discovered
counterexample. If an ambiguous callable source would change the approach
domain, require a checked exact-domain view instead of guessing one.

## 5. Decisions for the maintainer

Recommendations here are not approvals. The first three decisions determine
the public contract; the concrete AST proposal below is a separate gate.

| Decision | Recommended option | Material alternative and consequence |
| --- | --- | --- |
| Native operation or source library | Native Obj and native candidate facts, with checked defining routes and bounded rules; matches the requested out-of-the-box operations | A standalone `std` module can use `prop` and `have fn by exist!`, reducing kernel additions but requiring import and source-qualified interfaces. It remains mathematically valid, but does not deliver a native operation |
| Public spelling | `lim(a)` for sequences; `lim(f,a)` for functions; fixed-arity parser dispatch | `seq_lim(a)` plus `lim(f,a)` separates names and preserves bare user `lim(a)` only if `lim` remains overloadable, which current reserved-name behavior does not provide. A wholly prefixed API such as `seq_lim`/`fn_lim` avoids the bare-name collision but is less familiar |
| Ordinary function approach | Relative to the actual domain, requiring an accumulation point | Requiring approach from both sides makes `lim(fn(x R+) R {x},0)` unavailable and requires `lim_right` there. Both are coherent conventions, but differ at endpoints; switching later changes accepted mathematics |

Under the recommendation, `lim(fn(x R+) R {x},0)=0` is valid relative-domain
mathematics. It does not imply that a left-hand limit exists. A two-sided
equivalence theorem must explicitly require accumulation from both sides.

First-stage output values stay in `R`. Later `lim(...)=+infinity` syntax would
need a separate extended-real value/type and arithmetic proposal. Relations
for divergence can precede it. This preserves the choice rather than silently
identifying infinity with a real number.

## 6. Laws, premises and proof ownership

The following are mathematical specifications, not implemented BT claims.
`lim` equalities are selected-value consequences of candidate/existence laws.
Prove/check the relational route before exposing a short value equality.

| Group | Law shape | Necessary conditions / owner |
| --- | --- | --- |
| Definition and uniqueness | Epsilon introduction/elimination; two candidates have equal values | Nontrivial approach for function uniqueness; explicit definition/theorem route retains quantified witnesses |
| Anchors | Constant sequences/functions; identity function; `1/n -> 0` | Constants require a valid approach domain; reciprocal sequence uses an actual Archimedean witness, not sampled values |
| Locality | Finite sequence changes, index shifts; eventual equality of functions | Respect complete domains and the approach under comparison |
| Algebra | Negation, sum, difference, product, scalar multiplication, fixed natural powers, absolute value | Existing candidate limits; the resulting function/sequence must be callable on its declared domain |
| Quotient | Limit of quotient equals quotient of limits | Denominator limit nonzero AND the quotient object's own domain valid; eventual nonzero is not global nonzero |
| Order | Non-strict comparison and squeeze | Inequalities hold eventually along the actual approach; strict inequalities may become equality in the limit |
| Elementary continuity | Polynomial/rational substitution; later exp, trig, log and sqrt | Each function's actual continuity and local domain, not just its name or a value at the point |
| Composition | Transport an inner limit through a continuous outer function; punctured alternative with eventual avoidance | Full local call legality, plus continuity at the inner limit OR eventual avoidance of that value for a punctured outer limit |
| One-sided bridge | An ordinary limit restricts to an accumulating side; two matching sides yield an ordinary limit | State both side-accumulation assumptions; do not infer a missing side |
| Sequence/function bridge | Heine criterion and subsequence preservation | Correct accumulating domain, sequences of admissible points avoiding the base point, and the right existence/selection dependencies |

A's first rule set: definition/candidate consumption, uniqueness, constant,
identity, reciprocal sequence, local equality, negation/addition/product,
nonzero quotient, fixed natural powers, absolute value, comparison and squeeze.
Transcendental continuity, composition and the Heine equivalence follow after
this set; they are not required for A's first acceptance. Rational limits can
use A's algebra plus local equality, without claiming every continuous
function is automatically recognized.

Small fixed-shape rules can be native BT leaves. Quantified assumptions,
epsilon witnesses, squeeze/locality and reusable theorems should also have
an explicit invocation route. Structural automation may descend through a
supported function body using checked binders and guards; it must retain
child evidence and a decreasing expression measure. No unrestricted search
for limits, global epsilon solver, numerical sampling or floating-point
equality proof is proposed.

### Three controls that must survive convenient rules

**Quotient:** proposed mathematical example:

```text
b(n) = 1-1/n, n in N+          # b -> 1, but b(1)=0
q(n) = 1/b(n)                 # NOT a complete sequence on N+
q_tail(n) = 1/b(n+1)          # an explicit valid reindexing can converge
```

A nonzero denominator limit does not waive the WD of `q`. Pointwise function
quotients can instead declare the nonzero guard and then prove accumulation
and convergence on that actual punctured domain.

**Composition:** mathematical counterexample, not Litex case syntax:

```text
f(0)=1; f(t)=0 for t!=0; g(x)=0
lim(f,0)=0; lim(g,a)=0; lim(f compose g,a)=1
```

Punctured limits alone do not justify substitution when the inner function
keeps hitting the excluded value. Do not alter the existing strict `compose`
contract to make a locally meaningful expression globally composable.

**Local equality:** to transfer a limit from `g` to `f`, establish a radius on
which every admissible punctured `f` input is a legal `g` input and the values
agree, plus nontrivial approach for `f`. Equality only on a sparse intersection
of two domains is insufficient. This is the precise route for the main tracer.

## 7. Proposed native representation and evidence ownership

### AST Struct Change Proposal — unapproved

For A, the minimal proposed additions are:

```rust
// New Obj family; no existing Obj payload field changes.
Obj::LimitOperator(LimitOperator)

enum LimitOperator {
    Sequence(SequenceLimit),
    Function(FunctionLimit),
}
struct SequenceLimit { sequence: Box<Obj> }
struct FunctionLimit { function: Box<Obj>, approach: LimitApproach }
enum LimitApproach { AtPoint(Box<Obj>) }

// New native positive/negative atomic variants, not name-matched user props.
AtomicFact::HasSequenceLimitFact(HasSequenceLimitFact)
AtomicFact::NotHasSequenceLimitFact(NotHasSequenceLimitFact)
AtomicFact::HasFunctionLimitFact(HasFunctionLimitFact)
AtomicFact::NotHasFunctionLimitFact(NotHasFunctionLimitFact)

struct HasSequenceLimitFact {
    fact_id: FactId, sequence: Obj, value: Obj,
    line_file: Option<SourceLine>,
}
struct HasFunctionLimitFact {
    fact_id: FactId, function: Obj, approach: LimitApproach, value: Obj,
    line_file: Option<SourceLine>,
}
// NotHasSequenceLimitFact and NotHasFunctionLimitFact have the corresponding
// positive payload's same fields; no hidden negation mode or default value.
```

This is a shape proposal, not a patch. Constructors, derives and visibility
should follow existing source conventions. `LimitApproach` identifies a
mathematically distinct approach and will be shared by objects and candidate
facts. B would separately propose `FromLeft(Box<Obj>)` and
`FromRight(Box<Obj>)`; C would separately propose payload-free infinite
approach variants. A does not add speculative unused variants.

Why native identity: diagnostics, substitution, proof evidence, JSON and
LaTeX need to retain which operation and approach were used. Parser expansion
into an unnamed unique witness loses that identity. Existing ordinary
functions remain the source-library alternative in section 5. Dedicated
native facts follow the current `AtomicFact` convention; the legacy opaque
completeness-certificate mechanism should not become a shortcut for new
limit mathematics or for matching a user predicate by spelling.

Operands are recursive expression values; they do not own convergence proofs,
fresh binder IDs, inferred signatures, caches or selected numerical answers.
The result proofs own checked callable sources, approach/nontriviality proof,
existence/candidate evidence and uniqueness route. Binder-local proofs retain
their actual local environments. Preserve the existing stage-ordered result
and dispatcher contracts. No `Stmt`, `Identifier`, existing payload, Env,
ExecEnv or Runtime field/state contract change is proposed.

Implementation must obtain explicit approval of these exact AST additions.
Approval of this planning task is not that approval.

## 8. Dependency graph and implementation sequence

```text
real arithmetic / abs / N+ / checked complete callable domains
  --signature + definition--> epsilon-tail and punctured relations
  --definition--> nontrivial approach / directional approach
relations + nontrivial approach
  --proof--> uniqueness
relations
  --existence--> proved concrete candidate or existential
candidate/existence + uniqueness
  --selection + WD--> native real-valued lim object
relations + arithmetic inequalities + Archimedean witnesses
  --proof--> anchors / locality / limit algebra / order and squeeze
those rules
  --proof--> selected-value examples and bounded structural convenience
directional relations
  --proof--> one-sided bridge and unbounded-input finite limits
real completeness + tail sup/inf interfaces + boundedness
  --existence + uniqueness + selection--> finite limsup/liminf
```

Edge labels distinguish definitions, proof, existence, uniqueness and
selection. The arithmetic/Archimedean/completeness foundations retain their
actual native trust boundary; a showcase axiom is not silently promoted to a
checked native theorem. Source-order adjustment: native candidate and domain
contracts must precede value syntax, even when a textbook first motivates
limits by writing a familiar formula.

Implementation checkpoints after the semantic and AST decisions:

1. **Freeze contracts and names.** Confirm A and the three choices in section
   5; scan declaration/binder/field/export collisions, including local-only
   workspaces read-only when needed. Publish a migration inventory before
   reserving names. Do not silently modify `scripts/` or unrelated chapters.
2. **Candidate definitions and uniqueness.** Introduce checked native relation
   routes and nontrivial approach; adapt the existing epsilon proofs in one
   persistent Session, retaining accepted statements after ordinary failure.
   Specify the exact negative-fact interpretation as logical negation.
3. **Obj, WD and first anchor.** Add the approved independent branches and
   evidence consumers. First pass a known candidate into `lim`, use its real
   result downstream, and reject self-justifying convergence.
4. **Algebra and the tracer.** Check constants/identity/reciprocal, local
   equality and A's rule list with positive and negative requirements. Prove
   the punctured example explicitly before measuring the bare direct route.
5. **Presentation and compatibility.** Complete substitution, capture-safe
   instantiation/alpha normalization, identity/IR, JSON and diagnostics;
   render sequence and function limit notation with correct binders and domains.
   Migrate in-scope `lim` declarations deliberately and preserve their math.
6. **B/C, then D.** Add directional and infinite-input approaches in separate
   vertical slices. Design D against existing tail-sup/inf developments and
   the public sup/inf selection boundary before promising finite selectors
   for arbitrary unbounded sequences.

## 9. Owners, compatibility and output

Expected ownership, using existing pipeline stages:

| Responsibility | Existing source owner / intended addition |
| --- | --- |
| Values, facts and negation | [Obj](../src/ast/obj.rs), [atomic facts](../src/ast/fact/atomic.rs), fact helpers; approved new arms only |
| Parsing and names | [object parser](../src/parse/object/primary.rs), parser fact dispatch and reserved vocabulary; arity selects `lim` form |
| Callable domains and WD | [complete domains](../src/execute/execute_fact_stmt/function_domain.rs), [object WD](../src/execute/execute_fact_stmt/well_defined_results/verify_obj/core.rs); a new limit branch consumes them |
| Candidate and law proofs | Existing atomic/quantified/definition/theorem owners; typed limit branches mirror their proof route |
| Equality | [equality verification](../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md); selected-value equality consumes independently checked existence |
| Recursive consumers | Existing instantiate, comparison/identity, display/IR, JSON, LaTeX and Lean dispatches |

Expected future Rust level: R1 branch addition, provisionally L3 producer /
consumer validation. Keep old route ordering, permissions, scopes, memoization
and transaction behavior. If an existing shared contract must change, classify
that separately and return to the decision boundary.

Reserving `lim` breaks existing bare declarations with that name; both the
nutshell and Analysis Chapter 6 contain one. Namespace qualification behavior
also needs a real parser test, not an assumption that qualification bypasses
reserved-name rules. The alternate prefixed API avoids these specific bare
name migrations. Final migration scope and counts must come from the scan.

LaTeX should produce `\lim_{n\to\infty} a(n)` and
`\lim_{x\to a,\,x\in D_f} f(x)`, preserving restricted domains when relevant;
left/right forms use `a^-`/`a^+`. Fresh display binders must not capture free
names. With predicates/guards in the actual domain, render them or identify
the domain precisely instead of presenting an unrestricted limit. Existing
parse-only `-latex` remains unverified; output alone establishes no existence.

Lean replay requires its own semantic bridge. Until supported, every new
limit value, relation, WD route and proof family must fail closed with an
explicit unsupported result. Do not emit an axiom or placeholder proof.

## 10. Acceptance matrix and current planning evidence

Future runnable paths are planned artifacts, not links to existing files:

| Gate | Required cases |
| --- | --- |
| Candidate / selection | Explicit epsilon proof; candidate implies existence; uniqueness; selected value satisfies the candidate; use `lim(...)` inside arithmetic and a function call |
| A positives | Constant, `1/n -> 0`, identity, polynomial/rational at legal points, punctured `x^2/x -> 0`, local equality, algebra, squeeze |
| Mathematical negatives | False constant limit, oscillating sequence, sign jump; strict-order preservation is not assumed |
| Domain negatives | Empty/isolated approach, wrong carrier/arity, quotient undefined at an early sequence index, side with no accumulating inputs, invalid nested operand such as `0*lim(bad)` |
| Evidence / liveness | Candidate facts from a failed statement do not leak; previous accepted facts survive; no circular selection; missing proof distinguished from false theorem |
| B/C | Relative endpoint versus left/right limits; matching/mismatching sides; `1/x -> 0` at unbounded ends; bounded domain cannot vacuously approach infinity; finite and infinite outputs remain distinct |
| D | Bounded oscillating sequences have different finite limsup/liminf; convergence gives equality of both; no finite selector for unsupported unbounded cases |
| Consumers | Substitution/capture, identity and congruence, real membership, diagnostics/JSON, LaTeX binder/domain output, explicit unsupported Lean boundary |

Planned focused Rust tests: `tests/unit/execute/limits/tests.rs`. Planned
durable examples include `examples/wd/sequence_limit.lit`, the primary
`examples/wd/real_function_limit_at.lit`, dedicated rule/theorem files in the
matching proof-node families, and executable negative fixtures. No `trust`
is allowed in proof/WD tracers.

For implementation, run focused release tests for new producers and their
consumers, then the actual saved strict files, e.g.:

```sh
cargo test --release limits -- --nocapture
target/release/litex -strict -lang en -f examples/wd/real_function_limit_at.lit
```

The final command and test filter must be checked against the implemented test
registration. Require exit 0 and Normal JSON `kind=run`,
`run_result=success`, `session_terminated=false`, `termination=null` for
positive CLI gates; negative cases must fail for their stated reason. Run
name-migrated public snippets and affected docs. Broader Cargo, release and
local textbook gates are not automatically part of this feature.

This planning pass inspects the sources linked above and checks this document's
links, fences, scope and whitespace. It does not run new syntax, rebuild the
binary, verify the analysis collection, or establish implementation results.
The next handoff is semantic/name selection and the concrete AST decision,
followed by A's candidate-and-selection tracer; no implementation starts here.

Planning validation on 2026-10-20: local relative links in this plan and the
parent roadmap resolve; this plan's eight fenced blocks are balanced and all
new source interfaces are marked as proposals; the contract inventory and
parent link checks pass. Scoped whitespace checks pass. Concurrent Lean
compiler edits are outside this planning task and were preserved.
