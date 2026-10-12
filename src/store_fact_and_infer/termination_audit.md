# Inference termination and necessity audit

Audited on 2026-10-12 against the current working tree, including its existing
uncommitted changes. This was a read-only kernel investigation: no production
Rust, runtime, environment, AST, search policy or test expectations were changed.

## Findings

There is a confirmed same-fact recursion in function-range inference, and two
confirmed unbounded expansion paths through set-builder inference. Limiting
optional truth-search stages does not terminate these consequence chains.
There is also substantial avoidable repeated work, but deleting entire inference
families would break existing structural and formation contracts.

### 1. Function-range codomain projection repeats its own seed

This complete, strict input crashes the production release CLI:

```litex
have f fn(t R) R
forall x R:
    f $in fn(t R) fn_range(f)
    x $in fn_range(f)
    =>:
        x = x
```

Observed result: SIGABRT (Python subprocess return code `-6`), with
`has overflowed its stack` and `fatal runtime error: stack overflow, aborting`.
No Normal JSON run envelope was emitted. The source contains no user trust or
axiom. The local signature is formed using the previously declared function.

Owner: `membership_fn.rs:109`, specifically the codomain store at line 129:

```rust
set: body.ret_set.as_ref().clone(),
// ...
self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(codomain), verify_state)?
```

The local signature is selected before the outer signature. Its return set is
`fn_range(f)`, so the inferred codomain membership equals the source membership.
Every recursive call allocates another FactId and re-enters inference.

A diagnostic copy, capped at 81 infer calls, recorded:

```text
6  scope=3 x $in fn_range(f)
7  scope=3 x $in fn_range(f)
8  scope=3 x $in fn_range(f)
...
80 scope=3 x $in fn_range(f)
```

A second diagnostic input uses local signatures
`f $in fn(t R) fn_range(g)` and `g $in fn(t R) fn_range(f)`;
it alternates between the two memberships. Comparing only the immediate source
and target would fix the direct self-case but miss this mutual cycle.

Repair ownership: **local Rust semantic repair**. Proposed behavior, not
implemented: retain the seed and its normal WD/evidence, avoid recursively
republishing an exact visible codomain membership, and still publish the
independent preimage existential when appropriate. Do not return early from
the entire rule merely because the codomain was already known.

Required repair gates: self and mutual cycles terminate through the public CLI;
ordinary function-range codomain/preimage publication remains available;
displayed applications keep their existing preimage behavior; invalid domains,
scope boundaries and failed-statement rollback remain unchanged.

### 2. Builder projection generates infinitely many different facts

The exact visible-fact guard and per-call membership queue terminate repeated
memberships with the same element. They do not terminate this strict input:

```litex
forall S set, x R:
    S = {y R: y + 1 $in S}
    x $in S
    =>:
        x = x
```

Observed production result: killed by the harness after 18 seconds, without a
JSON envelope. Changing the builder body to `y $in S` yields a successful run.
The diagnostic copy records `x $in S`, `x+1 $in S`, `x+1+1 $in S`, and so on,
all in the same scope. This is an unbounded derivation established by the source
transition and the trace, rather than a timeout alone being called a proof.

A second strict input crosses builder and Cartesian projection:

```litex
forall S set, x S:
    S = {y cart(S): 0 = 0}
    x $in S
    =>:
        x = x
```

It also exceeded 18 seconds. The diagnostic trace alternates between memberships
in `S` and `cart(S)`, with elements `x`, `x(1)`, `x(1)(1)`, and so on.

Owners: `membership_projection.rs:23-70`, its inferred-store helper at line 129,
and Cartesian coordinate publication in `membership_cart_interval.rs:43-71`.
The existing queue records `member.ir()`; a recursively stored child enters a
new queue. More fundamentally, every element expression here is different,
so even a shared set of exact fact keys would not terminate the expansion.

Repair ownership: **needs discussion** if the repair changes the general
recursion/expansion contract. Proposed invariant: automatic consequence expansion
must have a terminating structural descent or an explicit bound; a repeated
carrier definition must not unfold indefinitely on newly constructed elements.
This is not a proposal to reject these mathematically expressible premises.
The intended completion behavior is a finite check, retaining checked useful
consequences and leaving further unfolding to explicit proof steps.

Required gates: both growth cases terminate; ordinary nested builders and
Cartesian coordinates still work; late carrier equalities, mutual same-element
carriers, exact free owners, no Or branch selection and rollback remain valid.

### 3. Concrete proposition expansion repeats known subtrees

```litex
prop base(x R):
    x = x
prop twice(x R):
    $base(x) and $base(x)
by def $base(1)
by def $twice(1)
```

The diagnostic trace repeats both `1 $in R` and `1 = 1`. Parameter obligations
and instantiated definition clauses always enter inferred store/infer again
(`expand_definition.rs:66` and `:116`). The source comment says one-layer
expansion, but recursively inferring those children traverses all descendant
definitions.

In strict production runs, repeating the same two-child pattern at depths
2, 4, 6, 8 and 10 produced respectively **20, 92, 380, 1,532 and 6,140**
inferred records in the final statement. Every lower predicate was explicitly
proved beforehand. These programs all completed successfully; this is finite
exponential duplication, not a same-state infinite loop.

Proposed behavior, not implemented: retain checked definition consequences,
avoid re-expanding already available identical consequences, and preserve
the evidence needed by consumers. Deletion of parameter-type projection in a
diagnostic copy left the renamed-carrier and bounded-WD examples successful;
that is evidence for further simplification work, not proof that the rule is
globally unnecessary. WD can prove a carrier without storing it, and later
restricted consumers or Lean evidence replay can need its publication.

Ownership: **provisional, diagnosing**. Inspect existing source/provenance
consumers before choosing a local deduplication or changing shared publication.

### 4. Equality-chain closure has redundant pairs and a real structural role

For `a = b = c = d`, the store already indexes adjacent equality edges. The
equality verifier can cite a path through those edges. The closure rule still
stores every nonadjacent pair (`transitive_closure.rs:64-84`). It produces
`(n-1)(n-2)/2` records for n chain objects and retains a separate edge-index
vector per pair, whose aggregate length grows cubically.

A strict chain of 120 identical objects published **7,021** redundant inferred
equalities. Disabling only pure equality-chain closure in the diagnostic copy
left ordinary scalar endpoint proofs successful and a disconnected endpoint
rejected; the same 120-object chain then published zero inferred equalities.

However, the following full input passes in the baseline copy and fails when
that closure is disabled:

```litex
claim:
    ? forall A, B set:
        A = B = fn(t R) R
        =>:
            0 = 0
    forall f A:
        f(0) $in R
```

The analogous chain ending in `{t R: t > 0}` has the same difference for a
subsequently introduced `x A`. Exact structural-property readers need the
direct `A = <constructor>` endpoint; adjacent graph connectivity alone does
not currently supply it. Removing all equality closures would lose this
contract. Numeric-order and user-registered transitive closures are separate
families; scalar equality path lookup does not replace them.

Proposed direction, not implemented: remove repeated/reflexive scalar work while
preserving required structural endpoints and provenance. The producer, exact
property readers, JSON explanations and Lean closure replay must agree on any
changed publication contract. Ownership: **needs discussion** for a broad
closure/publication change; a strictly local redundant-pair repair may be smaller.

## Complete inference-family inventory

Inspected all 46 Rust files under this module and the inferred-store WD entry,
VerifyState, exact-property readers, binder WD and equality graph consumers.
The termination reasons below are local; child WD can introduce scoped facts
and reach another inference family, so a finite outer loop alone is not a
global termination proof.

| Family | Recursive consequence shape / stopping reason | Assessment |
| --- | --- | --- |
| Atomic dispatcher | Calls matching rules with inherited state | No global fuel or active-fact guard |
| And / chain adjacency | Finite atomic components | Preserve packaging; children inherit risks |
| Or / plain exist / forall / forall-iff | NoInfer | Preserve logical scope/branch boundaries |
| exist! / not exist / not forall | Finite uniqueness/De Morgan conversion to terminal forall/exist | Not an identified truth-inference cycle |
| Equality cancellation: add/subtract/product/division | Removes outer scalar constructors; skips known endpoints; bounded type/nonzero premises | Useful, locally decreasing; preserve nonzero boundaries |
| Positive-real power | Membership in R+, then finitely many signs | Useful; optional premises capped at BuiltinRule |
| Concrete prop parameter types | Finite signature obligations, recursively inferred | Repeats known carriers; deletion requires consumer audit |
| Concrete prop body | Instantiated clauses recursively inferred | Measured exponential repeated expansion |
| Builder membership | Carrier/body projection with exact-visible guard and local visited queue | Confirmed growth paths above |
| Power-set membership | Subset fact, then finite/universal projection | Finite outer conversion; WD inherits risks |
| List / union / intersect / set-minus | Singleton equality, terminal Or, smaller literal carriers / negative facts | Useful structural decomposition; carrier children can reach builders |
| Cartesian membership | Coordinates in strictly smaller literal factors | Locally decreasing carrier, but builder aliases can reintroduce it |
| Integer / real intervals | Base numeric carrier, fixed bounds and optional singleton equality | Fixed fan-out; natural/sign guard matters |
| Signed standard sets | Fixed sign/nonzero facts; N-to-weak-bound-to-N stops on visible N membership | Useful for later division/modulo WD |
| Strict lower bound | Publishes zero lower bound; zero source is skipped | Useful for log/positive-carrier WD |
| Weak integer lower bound | Publishes N membership; exact-visible N guard breaks sign cycle | Useful for restricted natural function WD |
| FnSet / seq / finite_seq alias transport | Direct carrier constructor; seq becomes FnSet, literal FnSet stops transport | Finite transport; formation may visit binder carriers |
| Function range | Same element in selected return carrier, plus existential | Confirmed exact and mutual cycles |
| Preimage / preimage_set | Builder projection; active construction-root guard and exact-visible facts | Preserve complete-domain/guard evidence; local guards are not universal fuel |
| Family/index union/intersection | Ambient membership and terminal existential/universal | Finite outer conversion; children/WD can reach other families |
| Indexed Cartesian product | FnSet membership and choice definition | Fixed outer fan-out; preserve callable contracts |
| Subset / superset | Finite-upper certificate and/or elementwise forall | Useful; forall formation itself checks scoped members |
| Builtin definitions | Fixed definition DAG, e.g. bijective to injective/surjective; forall/exist/Or leaves | Useful checked definition publication; not a new open search route |
| Negative atomics / is-set / finite / nonempty | NoInfer | No positive consequence generation |

`VerifyStateLevel` explicitly denotes search-stage permission, not recursion
depth. Optional premise restrictions are sound boundaries, but do not replace
a termination contract for eager fact publication. A generic exact-fact visited
set would address finding 1 and some duplicate work, but not finding 2.

## Executed evidence and limits

Production build: `cargo build --release`, exit 0.

Focused tests, all exit 0:

```bash
cargo test --release --lib -- store_fact_and_infer:: set_builder_projection_cycle weak_integer_lower_bound positive_power_inference
cargo test --release --lib -- function_preimages finite_set_cardinality_rule chain_fact mixed_equality_order_chain
cargo test --release --lib -- native_scalar_codomain
```

Results: 40, 26 and 16 passing tests, respectively; three tests overlap,
so **79 distinct tests** passed. They establish existing contracts and do not
cover the newly discovered crashing/growing inputs.

Seven focused existing examples passed the strict release CLI: builder replay,
signed nonzero, weak integer lower bound, finite upper subset, additive
cancellation, bounded power premises and function range. Each exited 0 with
`kind: run`, `success: true`, `session_error: null`.

Diagnostics and independent rule-deletion controls ran only in
`tmp/2026-10-12/infer-termination-audit/diagnostic-copy/`. The copy adds a trace
and 81-call cap, plus switches to omit parameter projection or pure equality
closure. Its results are explicitly separate from production behavior.
The production module remained identical to the copied snapshot apart from
those three diagnostic-only additions.

Reproduction sources, traces, timeout/crash receipts, ablation controls,
benchmarks and source/binary hashes are retained in the same ignored task area.
`audit-metadata.json` records the exact diagnostic patch and production binary
SHA256 `c14ffe80ad437aab906600d3707c5f5db730475dbd09ca64fbc45c2a0fa9f46b`.

No full-kernel, whole-textbook or real-Lean gate was selected because this task
changed no executable contract. Deletion controls are focused evidence, not
compatibility certification. All fixes described here remain proposals.

Recommended order: repair exact function-range recursion; establish a finite
builder-expansion contract; reduce repeated concrete-prop work; then optimize
equality closure while preserving structural endpoints.
