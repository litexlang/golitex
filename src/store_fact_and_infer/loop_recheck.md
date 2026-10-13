# Inference loop recheck, 2026-10-13

This audit follows the completed one-step/result-family migration. No new
infer-to-infer cycle was found in the current rule owners and their reviewed
outward helper paths. No production Rust or mathematical rule changed.
The [historical termination audit](termination_audit.md) records the old
crashes and unbounded growth; those are not the current behavior.

## Current stopping boundary

```rust
// infer_fact: all rules receive a child state that cannot infer.
let verify_state = verify_state.without_inference();

// store_inferred_fact: store and cache direct formed subjects only.
let store = self.store_fact(fact)?;
self.remember_formed_atomic_subjects(fact);
Ok(StoreInferredFactResult { store })
```

All rule outputs use that direct store. It does not verify generated facts,
visit their definitions or call infer again. Stored And/Chain components are
indexed without inference. The only calls to `infer_atomic_fact` inside the
rule tree dispatch the original seed or enumerate original And/Chain edges.
No rule owner calls `infer_fact`, `store_fact_and_infer` or `exec_stmt`, and
none creates a fresh VerifyState or a descendant work queue.

Every rule family was classified: equality candidates have finite operand
positions; membership rules enumerate source factors, conditions or exact
properties; builtin definitions build a finite consequence list; existential
conversions traverse finite source clauses; chain closure enumerates finite
source pairs. Or/plain-exist/forall and the empty atomic families add no rules.

The outward helper review covers exact-property lookup, function signatures
and complete domains, preimage construction, template RHS instantiation,
closed-number resolution, and storage/special-property/formed-subject indexing.
Exact lookup reads only the subject's indexed direct records. Template
instantiation substitutes its selected RHS once. FnRange selects one signature.
Complete-domain template/application checks preserve their incoming state;
binder assumptions also pass it to storage, whose inference flag stays off.
Preimage construction additionally retains its active-root guard.

Fresh Direct states in forall argument matching were examined: their strict
equality consumer only performs known-equality/closed-calculation lookup and
does not enter WD, store or infer. The finite-function helper's fresh root
state belongs to explicit tuple-equality execution, not the infer callers.
Other fresh states found in the inspected builtin files are test fixtures.
Ordinary recursive verification and numeric evaluation remain separate
algorithms; this audit does not prove a universal time/depth bound for them.

## Executed controls

The release [one-step tracer](../../examples/infer/atomic/one_step_store_only.lit)
passes again, including exact/mutual FnRange cycles and both old builder growth
cases. For example, this unchanged source now terminates:

```litex
forall S set, x R:
    S = {y R: y + 1 $in S}
    x $in S
    =>:
        x = x
```

The stored direct consequence does not become another automatic seed. An
explicit later statement can still start its own one-step inference.

Additional strict controls were accepted statement by statement in one live
Session, then saved and checked as a clean file:

```litex
have f,g fn(t R) R
have h fn(t R) R
forall x R:
    f $in fn(t R) fn_range(g)
    g $in fn(t R) fn_range(h)
    h $in fn(t R) fn_range(f)
    x $in fn_range(f)
    =>:
        x=x
```

```litex
forall A,B set, x R:
    A={a R: a+1 $in B}
    B={b R: b+1 $in A}
    x $in A
    =>:
        x=x
```

A concrete predicate with two identical clauses was repeated to depth 12.
The accepted fragment starts:

```litex
prop audit_base(x R):
    x=x
by def $audit_base(1)
prop audit_double_1(x R):
    $audit_base(x) and $audit_base(x)
by def $audit_double_1(1)
```

Each later definition replaces both calls with the preceding predicate. Every
`by def` at depths 1 through 12 publishes exactly four Normal `infers` records;
it no longer recursively expands the duplicated descendants.

## Finite remaining cost

Equality/order/transitive chain closure still enumerates every nonadjacent
source pair and retains its whole premise-edge path:

```rust
for start in 0..chain_fact.objs.len() {
    for end in start + 2..chain_fact.objs.len() {
        // The captured closure retains these source edges.
        let edges: Vec<_> = (start..end).collect();
    }
}
```

This is a reduced illustration of the current producer. With n source objects,
there are `(n-1)(n-2)/2` closures and cubic aggregate path length. A 120-object
chain consisting entirely of `0` still publishes 7,021 redundant equalities.
The clean combined 42-statement control file, including that chain, completed
in about 0.12 seconds on this checkout. That timing is one observation, not a
performance guarantee. There is finite unnecessary work here; it is not a
remaining consequence cycle. Removing closures must preserve structural
endpoint publication and original proof provenance, so this audit leaves that
contract unchanged.

## Verification receipts

- `cargo build --release` exits 0.
- The selected release library gate passes 60 tests: store-only/next-seed,
  builder cycles, preimage construction, bounded predicate expansion,
  positive-power premises, exact properties, order capture and scalar domains.
- All 44 infer examples pass strict CLI execution with a 20-second per-file
  watchdog. Their slowest observed run was under 0.08 seconds.
- The combined additional control file passes strict CLI execution with
  `success: true`, `session_error: null` and all 42 statements successful.
- Proof sources, Session transcript/journal, full CLI envelopes and test logs
  remain under `tmp/2026-10-13/infer-loop-recheck/`.

The only existing tracer edit clarifies a stale WD comment; its executable
source is unchanged. No new trust, axiom, AST field, mutable state owner,
compiler adapter or inference rule was introduced.
