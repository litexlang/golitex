# Direct theorem selection acceptance — 2026-10-06

> Historical audit: these code fences preserve dated verifier observations,
> including rejected inputs and excerpts that depend on their original context.
> They are evidence, not current standalone tutorial examples. The maintained
> executable language examples are in the Manual, README, and examples corpus.

The user required `by thm T(args) => fact` to select a directly returned
conclusion and explicitly rejected combining `a = b` and `b = c` into `a = c`
inside this command. The change is confined to selected theorem calls.

## Before and now

<!-- litex:skip-test -->
```litex
# Before (incorrectly accepted):
# thm reflexive:
#     ? forall x R:
#         x = x
# by thm reflexive(7) => 2 + 3 = 5
# Ordinary calculation proved an unrelated target.
#
# Now (verified):
thm reflexive:
    ? forall x R:
        x = x
by thm reflexive(7) => 7 = 7
```

The unchanged former call now rejects with `reason: "not_returned"` and
`returned_conclusions: ["7 = 7"]`. Its executable negative fixture is
[unrelated-true-target.lit](../../examples/test_statements/negative/by_thm_stmt/unrelated-true-target.lit).
The positive [tracer](../../examples/stmt_nodes/by/by_thm_strict_selection.lit)
is collected by `run_examples_by_thm_strict_selection_tracer`.

## Contract and evidence

Only returned atomic conclusions, explicit conjunction components and adjacent
chain components are selectable. Matching uses structural identity and bound
variable alpha renaming. It does not rewrite arguments, reverse equalities,
combine conclusions, or use ambient/inferred facts. Type, premise and WD checks
remain required. Bare `by thm` and `release thm` keep their release behavior.

The selected proof is constructed from the matched conclusion's actual FactId,
even for an already known target. Equalities retain a cited `alpha_endpoints`
certificate; other atoms retain `by_known_atomic`. The existing retained local
environment owns the citation. Failure does not publish facts.

Current-source gates:

- `cargo build --release`: exit 0.
- `cargo test --release --lib by_thm_selection -- --nocapture`: 12/12 passed,
  covering unrelated calculations, definitions, ambient facts, returned-source
  citations, alpha renaming, negative conclusions, package components, rollback,
  the user's symbolic composition rejection and ten-language output.
- Detailed JSON consumer: 9/9 passed; theorem type/premise boundaries: 6/6 passed.
- `python3 examples/test_statements/run.py --leaf ByThmStmt`: 9 expected checks,
  no unexpected failures or recorded gaps.
- All 19 previously inventoried selected-call `.lit` files: expected outcomes
  passed. The strict tracer and five before/after CLI probes also passed.
- `cargo test --release --test test_statements -- --nocapture`: passed the
  integration test that executes all 51 root statement fixtures.

CLI gates require exit 0 and parsed `success: true` with no session error for
positives, and exit 1 / `success: false` with no session error for negatives.
This workspace's current CLI does not support the older runner flags.

## Wider checks and limits

The broader native-theorem catalogue and examples filter are **not all green**.
They respectively have 21 passes / 2 failures and 12 passes / 2 failures.
Ordinary equality and WD failures are outside this command's selection path:

<!-- litex:skip-test -->
```litex
# Excerpt from cart_function_set_definition.lit; ordinary equality misses.
have D set = {p finite_seq(union(R,Z),2): p(1) $in R, p(2) $in Z}
D = cart(R,Z)
```

<!-- litex:skip-test -->
```litex
# Excerpt from the finite-enumeration theorem body; this is a release call.
release thm sum_over_bijective_finite_set_enumerations(sum(1, 2, fn(k closed_range(1, 2)) R {f(e1(k))}), sum(1, 2, fn(k closed_range(1, 2)) R {f(e2(k))}))
```

<!-- litex:skip-test -->
```litex
# Excerpt from the new local-alpha tracer; the first call fails WD.
have f fn(p fn(x R) R, q fn(y R) R) R
f(fn(x R) R, fn(y R) R) = f(fn(u R) R, fn(v R) R)
# Its later by-thm alpha_identity selection succeeds.
```

The broad Markdown scan ran 682 blocks: baseline had 115 historical-audit
failures; the final working tree has those 115 plus the same Cantor fence in
both Blueprints. That fence fails before any selected theorem call:

<!-- litex:skip-test -->
```litex
# Excerpt under the diagonal nonmembership contradiction assumptions.
a $in {x X: not x $in f(x)}
```

Unrelated equality-index and documentation files changed concurrently during
verification. A temporary missing `helper::contains_binder` also blocked one
rebuild and disappeared before the final successful build. This task did not
edit that index, AST shapes, or Env/Runtime structures. These wider failures
are recorded separately and are not claimed solved. The edited selection
contract and migration snippets pass their focused gates.

Raw command results, source hashes and CLI receipts are in
[the machine receipt](by-thm-strict-selection-2026-10-06.json). Detailed logs and
baseline snapshots remain in `tmp/2026-10-06/by-thm-strict-selection/`.

Documentation impact: Manual, FAQ, learner and authoring cheatsheets, execute
architecture prose and JSON evidence notes specify the direct-selection
contract. Four existing theorem/axiom examples now select a returned equality;
two executable negative fixtures cover unrelated truth and composition. The
older audit retains its example as explicitly historical, with the current
rejection and tracer linked. No unrelated proof was weakened or given trust.
