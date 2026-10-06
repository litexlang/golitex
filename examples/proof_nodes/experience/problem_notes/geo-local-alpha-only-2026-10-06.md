# Ordinary equality lookup: local alpha only

Date: 2026-10-06, Asia/Shanghai.
Status: implemented; tests and performance measurements skipped at the user's
explicit request. No candidate build was performed. Regression sources and the
tracer are unrun.

## Contract and source change

The user approved retaining pairwise structural alpha while removing implicit
whole-graph alpha endpoint/path discovery. Free identifiers keep their real
identity; only bound identifiers may be renamed. No Obj/Fact/Stmt fields or
Runtime/Env owned state are changed.

Before, ordinary lookup performed:

```rust
// Reduced former control flow.
compare_submitted_pair_by_ir_or_structural_alpha();
find_exact_stored_path();
search_alpha_endpoints(&adjacency, &comparison);
```

Now `lookup_known_obj_equality_with_graph` returns `None` after the first two
steps miss. The later equality class-search stage also returns `Ok(None)`
after its existing restricted peer comparisons miss. The whole-graph
`search_alpha_endpoints` implementation is removed. Forall index query
variants follow existing IR edges without scanning all edges for alpha anchors.
The pairwise alpha helper and its recursive handling of nested binders remain.

```litex
# Before: Direct lookup could alpha-bridge these two independent stored classes.
# let a = fn(x R) R
# let b = a
# let c = fn(y R) R
# let d = c
# b = d
# Now: that Direct lookup returns no proof.

# Current directly submitted objects still use pairwise structural alpha.
fn(x R) R = fn(y R) R
have f fn(p fn(x R) R, q fn(y R) R) R
f(fn(x R) R, fn(y R) R) = f(fn(u R) R, fn(v R) R)
```

The active source above is in
[`local_alpha_without_graph_scan.lit`](../../equal/by_they_are_the_same/local_alpha_without_graph_scan.lit).
It is not executed in this change. The regression sources cover local alpha,
the Direct miss, exact cited paths, free-identifier boundaries, forall candidate
pruning and explicit selected-theorem citations; those sources are also unrun.

## Explicit routes and remaining scope

`by thm ... => ...` keeps its existing pairwise comparison against only that
theorem invocation's returned conclusions. It can emit `AlphaEndpoints`
evidence without a graph search. `release thm` still instantiates a selected
theorem and checks its obligations; no new alpha strategy or bypass is added.
Existing Strategy-level peer comparisons stay within the two reachable
classes and retain their original permission ceiling. A top-level proof may
therefore still succeed via that later route or object definitions; only the
removed Direct/whole-graph route is guaranteed absent.

The `AlphaPaths` evidence representation and JSON reader remain unchanged;
ordinary lookup no longer constructs those certificates. This change does not
alter alpha alignment during forall instantiation, object WD or capture checks.

## Evidence and performance limit

Only source/diff inspection was performed for this implementation. A copied
**pre-change baseline** release build had finished when the user cancelled
testing; it does not validate the modified implementation. No candidate build,
Rust test, CLI tracer or new performance run was issued.

The earlier isolated diagnostic disabled graph alpha fallback and measured
cost35 CPU **33.25 -> 5.60 seconds** and optimized vertical **44.72 -> 9.59
seconds**, with those controls still accepted. A genuine implicit alpha
transport control stopped matching. These are historical ablation results,
not timings or correctness evidence for this implementation. They explain
the expected benefit and the user-approved capability tradeoff.

See the [historical diagnosis](geo-stage-cost-2026-10-06.md) and
[implementation audit](../../../../docs/audits/geo-local-alpha-only-2026-10-06.json).

## Subsequent requested whole-geo run

The user subsequently requested the complete geo file. A frozen current-source
release build passed. The latest16:59 scalar-local227-declaration draft completed
in410.79 wall /405.39 CPU seconds, with223 accepted and4 failed (exit1). The
focused regression suites remain unrun. This does not establish whole-file
correctness or a same-source speedup. See the
[complete run record](geo-full-run-2026-10-06.md).
