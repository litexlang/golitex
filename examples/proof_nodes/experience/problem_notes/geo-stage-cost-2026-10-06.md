# Geo CPU cost: ordinary lookup and alpha endpoint scanning

Status: historical diagnosis accepted. The subsequent user-approved production
change is implemented but untested; see
[local-alpha-only implementation](geo-local-alpha-only-2026-10-06.md).
Date: 2026-10-06, Asia/Shanghai.
Classification: performance `kernel_problem`; repair owner provisional until
candidate/alpha compatibility and any Env-owned index change are specified.

## Observed cause and exact source

The release diagnosis reproduces the accepted `dependency51.lit` context and
unchanged cost35/optimized-vertical controls from the prior geo audit. Actual
source code is run through `Runtime::run_litex_code` and transactional
`exec_stmt`. All three normal, observed and ablated controls pass. No production
kernel code, AST or Env/Runtime state was modified by this investigation.

The ordinary stored-atomic lookup uses a predicate/polarity bucket, clones its
facts, then tries object equality for each candidate's arguments:

```rust
candidates.extend(knowns.iter().cloned());
for known in candidates {
    // args are compared to goal_args
    self.lookup_known_obj_equality_with_graph(left, right, &mut adjacency)
}
```

[Owner](../../../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/lookup_known_atomic_fact.rs).
This includes ordinary membership/type facts. It is independent of the newly
implemented forall equality index. A failed identity/path match falls through
to graph-level alpha lookup, whose first branch scans all visible equality edges:

```rust
for edges in adjacency.values() {
    for (_, cited) in edges {
        for reversed in [false, true] {
            // compare the candidate's two endpoints
        }
    }
}
```

[Alpha owner](../../../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/search_equal_fact_proof_by_equivalence_class.rs).
The following class-member alpha-path comparison is also inside that measured
function. A finite search can still be expensive when invoked hundreds of
thousands of times. The ordinary fact candidate scan and whole-graph alpha scan
multiply each other's cost; unrelated candidates produce most of the work.

## Measurements

The observer uses `CLOCK_THREAD_CPUTIME_ID` from the system C header. Sleeping
and scheduling delays do not count as current-thread CPU. Nested exclusive
CPU totals exactly partition each single frame span; inclusive times overlap
and are not summed. All observation hooks exist in an allocated source copy.
The same-source unobserved binaries quantify observer overhead. These modes
omit the former benchmark's three framing statements, consistently in all
profile/baseline/ablation runs; terminal IO is excluded.

| Dependency51 input | No-observer CPU | Observed CPU | Alpha exclusive CPU / share | Alpha edge visits |
| --- | ---: | ---: | ---: | ---: |
| Scalar helper | 4.53 s | 4.84 s | 3.22 s / 66.5% | 3,674,840 |
| Cost35 | 33.25 s | 34.93 s | 28.48 s / 81.5% | 36,150,634 |
| Optimized vertical | 44.72 s | 48.98 s | 37.52 s / 76.6% | 47,854,402 |

Cost35 makes367,783 ordinary fact candidate attempts and432,731 object-equality
lookups. Optimized vertical makes689,003 candidate attempts and800,048
object-equality lookups. Graph snapshot copying costs1.42/2.63 s; path BFS
costs1.58/2.52 s. These are secondary to alpha lookup in these controls.
Algebra normalization and monomial collection together consume below0.1%
exclusive observed CPU. Function-body normalization's inclusive time includes
its nested WD/search work, so that inclusive number is not an algebra cost.

The forall equality index is not queried by these controlled geometric proofs.
Cost35 invokes no generic forall-search call; optimized vertical invokes12
calls totaling about1.08 ms inclusive CPU. Explicit theorem release is a
separate route. This explains why speeding forall equality candidate retrieval
did not substantially accelerate these particular proofs.

The identical scalar helper has5911 object-WD calls in both scalar2 and
dependency51 contexts, with3973 cache misses and1938 hits. Yet its no-observer
CPU grows0.85->4.53 s; ordinary candidate attempts grow58,415->109,526 and
alpha-edge visits653,434->3,674,840. The larger fact context increases search
work even though the number of WD calls is unchanged.

## Causal ablation and required boundary

Only the copied diagnostic source adds this branch:

```rust
// Diagnostic ablation, not a production fix
if skip_global_alpha { return None; }
```

With timers disabled, cost35 CPU changes33.25->5.60 s (83.2% lower), optimized
vertical44.72->9.59 s (78.6% lower), and the scalar helper4.53->1.35 s.
All those exact inputs still verify. This is strong evidence that graph-level
alpha fallback causes most of their remaining CPU cost.

It cannot simply be deleted: the real `reached_binder_aliases` control stores
`f = fn(x R) R {x}`, `g = fn(y R) R {y}` and the proved forall `f(t)=t`, then
checks the Direct argument-transport match for `g(2)=2`. The normal matcher
accepts that match; disabling graph-level alpha rejects it. Pure identity
alpha comparison remains enabled in both modes, so this tests the distinct
known-class alpha-path route. The ablation is not a proposed semantic change
or a shipped speedup.

## Repair direction and ownership

The next owner is ordinary fact lookup plus Direct equality/alpha retrieval:
reduce unrelated predicate-bucket attempts and avoid repeating full graph
alpha work for each failed argument comparison. Preserve real source cites,
known-equality aliases, renamed binders/free owners, genuine alpha paths,
known-fact precedence, type/domain checks and transaction boundaries.

Query-local derived views/miss reuse and pure compatibility filtering can be
reviewed as local repairs. Adding/retyping a persistent ordinary-fact or alpha
anchor index changes an Env-owned container; the maintainer must approve that
concrete change. Previous authorization covered forall `by_equal`, not those
additional owners. No repair variant has been implemented or certified here.

[Full CPU receipt](../../../../docs/audits/geo-stage-profile-2026-10-06.json)
contains exact inputs' existing hashes, frozen source fingerprints, observer
locations, CPU-clock calibration, all measurements, overhead and the rejected
capability boundary. The allocated draft/source area is
`tmp/2026-10-06/geo-performance-diagnosis/stage-profile/`.
