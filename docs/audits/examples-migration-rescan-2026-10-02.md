# Examples migration rescan — 2026-10-02

> Historical audit: these code fences preserve dated verifier observations,
> including rejected inputs and excerpts that depend on their original context.
> They are evidence, not current standalone tutorial examples. The maintained
> executable language examples are in the Manual, README, and examples corpus.

Follow-up repair checkpoint: [local fixes and current residuals](example-local-repairs-2026-10-02.md). The scan below is historical evidence.

Latest conversation recheck: [2026-10-03 status and remaining issues](conversation-issue-recheck-2026-10-03.md).

## Scope and baseline

This is an inspection and report requested by the user, using the classification
framework in `litex-example-migration`. It does not repair the kernel, examples,
manifests, or intended mathematical contracts.

Two independently frozen working-tree checkpoints were built in release mode.
The first collected 1427 `.lit` files. Concurrent work then changed numeric,
complex, and domain verification paths, so the entire scan was repeated on a
later snapshot with 1430 files. **All current findings below refer to the later
checkpoint**, except comparisons explicitly labeled earlier. These are two
`src/` checkpoints, not a comparison against a named historical legacy release.
An untraced legacy migration omission remains a hypothesis.

The workspace was already dirty and other tasks continued editing it. A source
fingerprint identifies the tested behavior more precisely than the shared Git
HEAD. Live files may change after this report; the frozen fixtures remain the
reproducible source of each observation.

- Final source SHA-256: `d1c7e9f1c61a745194dc365b32467730bdf14e357f39548fdbcd173491c96b9a`.
- Pinned binary SHA-256: `bb525a4ee11f7c9f827947ae70592de63266f788c2cd89181b19a2f047e39555`.
- Fixture/config/manifest SHA-256: `20007f4df40cb46c1b4fd476172587314b53597da93a275094fc6f09f9f2dd1d`.
- Frozen standard-library source SHA-256: `8271e68c3b2c97f61de72aed65dde29199c7242e906683bcb005b54e4c8c30fe`.
- Source copying was stable; the final scan independently confirmed source, fixture, and binary stability.
- Baseline/build/coverage: [latest-baseline.json](../../tmp/2026-10-02/examples-migration-rescan/latest-baseline.json), [latest-snapshot-build.log](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot-build.log), [latest-coverage.json](../../tmp/2026-10-02/examples-migration-rescan/latest-coverage.json).

## Outcome counts

Counts below are fixture or check outcomes, **not independent bug counts**.
The same upstream boundary can affect Obj, Stmt, public files, and module runs.

| Collection | Executed coverage | Remaining observed mismatch |
| --- | --- | --- |
| All collected `.lit` paths | 1430 / 1430; no uncovered path | Outcomes are partitioned below |
| Obj inventory | 99 object groups; 464 fixture files | 97 manifest-labelled desired positives reject; 2 ordinary positive files fail internally; 5 must-reject fixtures accept |
| Stmt runner | 50 statement leaves; 372 checks | 367 match expectations; 5 unexpected choice-related failures; K005 remains one expected known gap |
| Remaining direct-file runs | 764 files | 37 public mismatches: 16 obsolete-config launch failures and 21 mathematical/operational failures; 18 exploratory failures separately |
| Module and cwd entrypoints | 26 checks | 12 mismatches: 11 obsolete-config checks and one stack-overflow module; overlap with direct files |

All 97 Obj desired-positive failures are listed with unchanged source in the
appendix. They include absent automatic proof routes, WD/carrier propagation,
matching, and possible semantic-contract mismatches. They are **not 97 confirmed
implementation bugs**. An ordinary Stmt runner also counts the expected K005
failure as a matching check; that does not establish the requested capability.

## Confirmed incorrect admissions: three WD families, five negative fixtures

### A. Finite aggregate callable domain is not checked on a resolved unary signature

Executed reduced reproductions:

<!-- litex:skip-test -->
```litex
let s = finite_set_sum({1}, fn(x {2}) Z {x})
```

<!-- litex:skip-test -->
```litex
let s = finite_set_product({1}, fn(x {2}) Z {x})
```

Both accept. The callable is defined only on `{2}` and cannot supply a value at
the aggregated element `1`; both should fail WD. The valid control
`let s = finite_set_sum({1}, fn(x Z) Z {x})` accepts.

Classification: **implementation defect**, earliest owner **aggregate WD**,
facets semantic contract and callable composition. In `verify_obj/iterated.rs`,
the resolved unary-function branch proves the scalar return carrier but skips
the required domain coverage; the fallback branch calls
`require_callable_as_expected_unary`. Check the shared callable-domain producer,
including aliases and named functions, rather than weakening every caller.

### B. An unordered finite-set fold admits subtraction

Executed reduced reproduction:

<!-- litex:skip-test -->
```litex
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0)
```

This accepts. Current `Manual.md` requires the operation to be associative and
commutative for this unordered interface. Subtraction satisfies neither
condition; it should fail WD. The corresponding additive declaration accepts,
but declaration success alone does not prove all required algebraic evidence
was checked. `verify_finite_set_reduce_obj_well_definedness_by_def` checks
finiteness, homogeneous signatures and the seed, without requiring the stated
associative/commutative proofs.

Classification: **implementation defect relative to the documented contract**,
earliest owner **fold WD**, facet semantic contract. Verify the shared algebraic
requirements and their evidence consumption. Ordered `reduce` has a different
contract and should not inherit this rejection.

### C. Finite extrema accept a non-real set

Executed reduced reproductions:

<!-- litex:skip-test -->
```litex
let n = finite_set_max({i})
```

<!-- litex:skip-test -->
```litex
let n = finite_set_min({i})
```

Both accept; `i` is the reserved imaginary unit. The current contract requires
a finite, nonempty subset of `R`, so these should fail WD. A real control
`let n = finite_set_max({1, 2})` accepts. `verify_obj/sets.rs` checks finite and
nonempty requirements but omits the real-subset requirement in these two owners.

Classification: **implementation defect**, earliest owner **extremum WD**,
facet semantic contract. The missing premise belongs to the shared object
contract, not a caller-specific repair.

The frozen contract text is in `latest-snapshot/docs/Manual.md`, aggregate
section around lines 970–1003 and WD table around line 1489. All executed probes
are preserved in `latest-probes.json`; the five exact corpus negatives appear
in Appendix A.

## Internal failures and availability regressions

### D. Product-shape inference cannot satisfy its own strengthened WD boundary

Executed reduced reproductions:

<!-- litex:skip-test -->
```litex
cart({}, {1}) = {}
```

<!-- litex:skip-test -->
```litex
proj(cart(cart(R, Z), N), 1) = cart(R, Z)
```

Both now produce `Runtime(InternalBug("inferred fact failed well-definedness
check"))`. The first accepted on the earlier pinned binary. The complete
`test_objs/cart.lit` and `test_objs/proj.lit` were earlier positive and now fail
internally. Ordinary `proj(cart(R, Z), 1) = R`, projection 2, and direct tuple
membership still accept; **do not generalize this to all projection cases**.

An alias tracer also fails internally:

<!-- litex:skip-test -->
```litex
let C = cart(R, Z)
cart_dim(C) = 2
```

This alias was already a WD gap in the earlier checkpoint; its transition is
from a rejected obligation to an internal error, not a newly lost positive.

The source stages are `infer_equal_fact_cart_tuple_shape`,
`infer_is_cart_dimension_lower_bound`, and `store_inferred_fact_and_infer`.
The first transports shape/dimension evidence along equality; the second
stores `cart_dim(C) >= 2`; the last reports an internal bug when inferred WD
fails. Numeric order predicates now require real carriers. The missing
carrier/shape boundary needs inspection before the downstream facts are stored.
Empty-product equality also raises a dimension-metadata contract question:
different empty products denote the same empty set, so shape transport must not
invent contradictory dimensions. This audit did not resolve that design issue.

Classification: **confirmed internal operational failure; producer/consumer
composition regression**, earliest observed owner **inference/storage WD**.
A true set identity should verify without an internal failure, while every
inferred fact must retain valid WD evidence. Dropping the new WD checks would
not establish a valid repair.

### E. A supported module aborts; four public files exceed the scan deadline

The unchanged `module_manager/function_family_bindings/main.lit` contains:

<!-- litex:skip-test -->
```litex
release obj def Other::functions::step
template<t R>:
    have fn step(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: Other::functions::step(n - 1)
\step<0>(1) = Other::functions::step(1 - 1)
```

Both direct-file and repository entrypoints abort with stack overflow
(exit `-6`, no successful run envelope). It passed in the earlier full scan.
The full file, including later qualified-predicate checks, is retained in the
appendix; the snippet above is an excerpt, **not an isolated crash reproducer**.
The exact recursive cycle is not yet established.

Four public files exceeded a 20-second release-process deadline:
`standard_set_subset_and_fn_app_in_codomain.lit`, `fn_tuple_projection.lit`,
`let_template_struct_aliases.lit`, and `mul_nested_fn_app_in_c.lit`.
For example, the vector/nested-function files start with:

<!-- litex:skip-test -->
```litex
have fn vec(A, B cart(R, R)) cart(R, R) = (B[1] - A[1], B[2] - A[2])
have fn dot(u, v cart(R, R)) R = u[1] * v[1] + u[2] * v[2]
have p, q, r cart(R, R)
dot(vec(q, p), vec(q, r)) $in R
```

This is an excerpt of the timed-out fixture. The isolated `vec` declaration
accepts in about 3.735 seconds on the later checkpoint, versus 0.006 seconds
earlier. That comparison supports a search-cost regression; it does not prove
that the whole file cannot finish under a larger deadline. The template/struct
file previously rejected at `chosen_struct.first = 1`; its later observation is
a deadline, not a completed search failure.

Classification: stack overflow is an **implementation defect**; deadline
outcomes are **availability findings, cause undetermined**. Facets search
policy, composition, scope/state and computation. Preserve real-context
reproductions; inspect guarded WD/search recursion and the winning route before
choosing a repair. Do not relabel a process crash or deadline as mathematical
rejection.

## Strengthened contracts with incomplete capability composition

### F. Callable-signature evidence does not compose across all representations

Executed pair:

<!-- litex:skip-test -->
```litex
let A = fn(k {1, 2}) power_set(N) {{1}}
let X = index_union({1, 2}, N, A)
```

This fails at the required `A $in fn(k {1, 2}) power_set(N)` obligation. The
following named-function control accepts:

<!-- litex:skip-test -->
```litex
have fn A(k {1, 2}) power_set(N) = {1}
let X = index_union({1, 2}, N, A)
X = X
```

The corresponding anonymous literal membership also rejects in search:

<!-- litex:skip-test -->
```litex
fn(k {1, 2}) power_set(N) {{1}} $in fn(j {1, 2}) power_set(N)
```

This is a callable/alpha-matching/evidence boundary, not evidence that
`index_union`'s nonempty requirement is wrong. The two public indexed-family
files fail at analogous membership obligations.

The latest predicate WD now explicitly verifies callable domains for
`$injective`, `$surjective`, `$bijective`, and `$is_choice_function_for`.
That contract strengthening exposes additional unconnected representations:

<!-- litex:skip-test -->
```litex
release axiom_of_choice: set {{1}}:
    forall A {{1}}:
        $is_nonempty_set(A)
```

This fails on the later binary and passed earlier. Its nonempty-family premise
still accepts alone. The generated existence/choice signature fails WD. Five
Stmt checks and the public choice statement share this family of failures.
The standalone definition-based choice predicate also regresses.

<!-- litex:skip-test -->
```litex
release thm finite_set_has_bijective_index({1, 2})
```

This fails with a precise generated-conclusion obligation:
`idx $in fn(k closed_range(1, finite_set_size({1, 2}))) {1, 2}`,
although `idx` is introduced in `finite_seq({1, 2}, finite_set_size({1, 2}))`.
The missing bridge is from the finite-sequence representation to the required
FnSet membership. The detailed JSON establishes this upstream boundary.

Classification: **intended stronger domain/WD checks plus incomplete
producer/consumer capability composition**; migration omission versus a
new implementation gap remains unproven without legacy route comparison.
Earliest owner **WD consuming callable membership**, facet representation and
wiring. Preserve the stronger mathematical conditions; check anonymous,
named, aliased and finite-sequence membership bridges separately.

### G. Named real bound theorems construct undeclared predicate certificates

<!-- litex:skip-test -->
```litex
release thm real_least_upper_bound_exists({0}, 1)
```

It fails while checking the generated conclusion
`exist x R st {$is_real_least_upper_bound({0}, x)}` because
`is_real_least_upper_bound` is an undefined predicate. The analogous greatest
lower bound certificate has the same signature problem. Six public examples
collapse to these two upstream predicate names; later `L`-undefined parse
errors are consequences of a failed prior release.

Classification: **builtin certificate/registration wiring gap**, earliest owner
**generated conclusion WD / predicate signature**, facet public interfaces and
composition. Determine whether the predicate belongs to builtin registration
or required library definitions, then reconnect that established interface.
No `abstract_prop` or trust was inserted to bypass it.

### H. WD and mathematical inference still have additional independent gaps

<!-- litex:skip-test -->
```litex
have x N
2^(log(2, 2^x)) = 2^x
```

This fails WD on both pinned checkpoints. Explicit `2^x $in R+` or `2^x > 0`
premises themselves verify, but the outer expression still fails WD. Merely
adding positivity is therefore **not a verified repair**. Inspect the exact
power/log carrier and nonzero obligations before selecting the missing rule.

The surjection-size example has the following established premises:

<!-- litex:skip-test -->
```litex
have A set = {1, 2}
have B set = {1}
have fn f(x A) B = 1
exist x A st {x = 1}
by def $surjective(A, B, f)
$is_finite_set(A)
finite_set_size(B) <= finite_set_size(A)
```

The last fact now fails WD although all preceding statements accept. It passed
on the earlier binary. Inspect the finite-codomain prerequisite and its
publication before entering the size comparison; that owner is distinct from
the observed undefined real-bound predicate.

Classification: **reproduced WD/inference boundaries; exact causes not fully
established**, facets semantic contract, evidence publication and capability.
The 97 Obj desired-positive failures in Appendix A broaden this inventory
across functions, arithmetic/trigonometry, sets, products, aggregates, struct
fields and qualified identifiers. An unchanged manifest expectation is not
sufficient evidence to relax WD or restore an implicit route.

## Capability limits, logical routes and result stability

### I. Closed aggregates and negated existence still lack the requested routes

<!-- litex:skip-test -->
```litex
sum(1, 3, fn(x Z) Z {x}) = 6
```

This rejects in proof search. `eval sum(1, 3, fn(x Z) Z {x})` rejects with
`unsupported_expression`. These are separate verification and computation
paths. The mathematics is valid; the tested checkpoint does not supply those
automatic routes. Classify a route as intentional limitation versus omission
only after its intended policy or named historical implementation is checked.

K005 remains:

<!-- litex:skip-test -->
```litex
forall x {0}:
    x != 1
not exist x {0} st {x = 1}
```

The universal exclusion accepts and the equivalent negative-existence
conclusion fails proof search. This is a confirmed unmet logical route; no
change to the intended proposition is required. Inspect the universal-exclusion
consumer rather than adding trust or weakening the claim.

### J. Identical fresh processes disagree on a contradiction proof

<!-- litex:skip-test -->
```litex
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

The fixed earlier binary accepted 3 of 12 runs and rejected 9. The fixed later
binary accepted 6 and rejected 6 at `by_contra`. Every run used the same code,
binary, frozen source/std and cwd in a fresh process, with no infrastructure
failure. Meanwhile direct `i != 0` now accepts. Do not treat this explicit proof
as a reliable workaround or conflate it with the previously missing direct
imaginary nonzero rule.

Classification: **confirmed behavioral instability, root undetermined**;
earliest observed owner **explicit contradiction proof/search**, facets search
policy and state/evidence. Hash iteration, route selection or evidence lifetime
are hypotheses, not established causes. Compare branch/equality/contradiction
evidence across successful and failed processes.

Two additional current rejections were repeated 12 times each:
`sqrt(2) $in R*` and the unchanged `sqrt_quotient.lit`; all 12 runs rejected.
They accepted in the earlier scan. This is a regression observation across
these checkpoints, not evidence of their own nondeterminism. The empty-product
internal failure likewise repeated in all 12 later runs.

## Configuration drift and deliberate rejection boundaries

Sixteen public module files and nine configured directories still use old
`[hierarchy]`/`[module]` layouts. Example context:

```toml
[hierarchy]
module = "..."
```

This is an illustrative excerpt of the obsolete schema; exact configurations
are linked with every fixture. Current launch rejects with
`litex.config does not use [hierarchy] or [module]` (exit 2). That is **public
configuration migration drift**, not a mathematical proof failure. The 11
module/cwd launch mismatches overlap those files. Even an expected-negative
fixture must reach its intended semantic failure: a config rejection does not
prove the original negative behavior.

The current supported launch surface is `-e`, `-f`, `-r`, `-strict`, `-lang`,
and `-session`. Older skill recipes `-compact`, `-runner`, `-before`, and
`try:` are absent and were not used as verification commands.

The following tested rejection is deliberate under the current indexed-family
nonempty-domain contract:

<!-- litex:skip-test -->
```litex
have fn empty_family(empty_index {}) power_set(N) = {}
index_union({}, N, empty_family) = {}
```

Its WD rejection is not automatically a migration bug. Likewise,
`let f = fn(x R) N {x}` and `fn(x R) N {x}(-1) = -1` now reject correctly:
their body is not universally in the declared `N` return carrier.

Eighteen `_internal`/root scratch failures are exploratory observations, not
public acceptance regressions. Several use removed `$fn_eq`, finite-set
induction, old inline trust syntax, bare operators, or obsolete configuration.
Their exact source and observed phase are listed separately.

## Findings no longer open on the later checkpoint

<!-- litex:skip-test -->
```litex
2.400 = 2.4
```

This now accepts; `2.400 != 2.4` correctly rejects. The earlier wrong admission
is historical, not one of the five current bad negatives.

<!-- litex:skip-test -->
```litex
i != 0
1 / i = -i
```

Both now accept. This closes the tested direct routes, not the unstable
contradiction-proof behavior above.

K004 is already reclassified as an intentional automatic-search limit; the
manifest's explicit recursive equality chain passes. K010's unchanged finite
numeric enumeration regression passes. The trust-have printed statement now
contains its separator and executes correctly; the issue index records D001's
fresh-parser replay acceptance. The latest issue index no longer incorrectly
lists K004/K010/D001 as open. These were not repaired by this scan.

## Reproduction, evidence and completion boundaries

Use the frozen checkpoint for the exact observations:

```bash
cd tmp/2026-10-02/examples-migration-rescan/latest-snapshot
LITEX_STD_PATH="$PWD/std" ../litex-latest -lang en -e 'cart({}, {1}) = {}'
LITEX_STD_PATH="$PWD/std" ../litex-latest -lang en -f examples/test_objs/negative/sum_of_finite_set__n02.lit
LITEX_STD_PATH="$PWD/std" python3 examples/test_statements/run.py --binary "$(cd .. && pwd)/litex-latest"
```

Successful execution requires process exit 0, top-level `success:true`, no
session error, and no failed statement; launch rejection, internal session
error, stack overflow and deadline are interpreted separately. Raw records
retain exact commands, cwd, source, result envelopes for failures and timings.

No kernel/example/manifest source was modified by this task. Live exploratory
launches could refresh existing import caches; no new canonical cache directory
was created, and concurrent/pre-existing changes were preserved. Task binaries,
frozen source/fixtures/std and raw records remain under the dated `tmp/` task
area for reproducibility. The completed execution ledger is removed only after
this durable report and evidence are verified.

This scan is complete for collected examples and entrypoints. It is not a
whole-kernel soundness proof, all Rust tests, all scope rollback permutations,
Normal/Detailed output equivalence, Lean export, or full repository release
certification. No semantic repairs or architectural choices are claimed.

Prioritization: verify the three incorrect-admission WD families first;
then internal errors, stack overflow and result instability; then reconnect
callable/finite-sequence/predicate evidence under the established stronger
contracts; finally audit remaining requested capability routes and migrate
obsolete configurations. This order follows behavior and upstream owners,
not the number of downstream failing files.

Raw evidence: [latest-objects.json](../../tmp/2026-10-02/examples-migration-rescan/latest-objects.json), [latest-statements.json](../../tmp/2026-10-02/examples-migration-rescan/latest-statements.json), [latest-other-files.json](../../tmp/2026-10-02/examples-migration-rescan/latest-other-files.json), [latest-modules.json](../../tmp/2026-10-02/examples-migration-rescan/latest-modules.json), [latest-probes.json](../../tmp/2026-10-02/examples-migration-rescan/latest-probes.json), [boundary-replays.json](../../tmp/2026-10-02/examples-migration-rescan/boundary-replays.json), [projection-choice-probes.json](../../tmp/2026-10-02/examples-migration-rescan/projection-choice-probes.json), [stability-probes.json](../../tmp/2026-10-02/examples-migration-rescan/stability-probes.json), [snapshot-baseline.json](../../tmp/2026-10-02/examples-migration-rescan/snapshot-baseline.json), [snapshot-objects.json](../../tmp/2026-10-02/examples-migration-rescan/snapshot-objects.json), [snapshot-statements.json](../../tmp/2026-10-02/examples-migration-rescan/snapshot-statements.json), [snapshot-other-files.json](../../tmp/2026-10-02/examples-migration-rescan/snapshot-other-files.json), [snapshot-probes.json](../../tmp/2026-10-02/examples-migration-rescan/snapshot-probes.json), [scan.py](../../tmp/2026-10-02/examples-migration-rescan/scan.py).

## Appendix A: complete Obj mismatch inventory

The intended outcome below comes from the audited Obj manifest. For desired positives, root cause remains undetermined unless traced in a card above; earliest phase is an observation, not a bug classification. Correctness of the old expectation must be checked before changing the language.

| Object owner | Desired positives rejected | Ordinary positive files failed | Negatives accepted |
| --- | ---: | ---: | ---: |
| `fn_obj` | 2 | 0 | 0 |
| `pow` | 1 | 0 | 0 |
| `abs` | 1 | 0 | 0 |
| `min` | 1 | 0 | 0 |
| `max` | 1 | 0 | 0 |
| `sin` | 2 | 0 | 0 |
| `cos` | 2 | 0 | 0 |
| `tan` | 3 | 0 | 0 |
| `cot` | 2 | 0 | 0 |
| `arctan` | 2 | 0 | 0 |
| `arccot` | 2 | 0 | 0 |
| `log` | 2 | 0 | 0 |
| `real_part` | 2 | 0 | 0 |
| `imaginary_part` | 1 | 0 | 0 |
| `complex_abs` | 4 | 0 | 0 |
| `union` | 1 | 0 | 0 |
| `intersect` | 1 | 0 | 0 |
| `set_minus` | 1 | 0 | 0 |
| `family_union` | 4 | 0 | 0 |
| `family_intersect` | 4 | 0 | 0 |
| `power_set` | 1 | 0 | 0 |
| `index_union` | 3 | 0 | 0 |
| `index_intersect` | 3 | 0 | 0 |
| `index_cart` | 2 | 0 | 0 |
| `list_set` | 3 | 0 | 0 |
| `range` | 2 | 0 | 0 |
| `closed_range` | 1 | 0 | 0 |
| `finite_seq_set` | 1 | 0 | 0 |
| `seq_set` | 2 | 0 | 0 |
| `cart` | 1 | 1 | 0 |
| `tuple` | 2 | 0 | 0 |
| `cart_dim` | 1 | 0 | 0 |
| `proj` | 0 | 1 | 0 |
| `obj_at_index` | 2 | 0 | 0 |
| `fn_set` | 2 | 0 | 0 |
| `anonymous_fn` | 2 | 0 | 0 |
| `fn_range` | 1 | 0 | 0 |
| `sum` | 2 | 0 | 0 |
| `product` | 2 | 0 | 0 |
| `sum_of_finite_set` | 3 | 0 | 1 |
| `product_of_finite_set` | 3 | 0 | 1 |
| `reduce` | 3 | 0 | 0 |
| `finite_set_reduce` | 4 | 0 | 1 |
| `finite_set_size` | 1 | 0 | 0 |
| `finite_set_max` | 1 | 0 | 1 |
| `finite_set_min` | 1 | 0 | 1 |
| `struct_obj` | 2 | 0 | 0 |
| `field_access` | 1 | 0 | 0 |
| `standard_set_r_pos` | 1 | 0 | 0 |
| `standard_set_r_star` | 1 | 0 | 0 |
| `identifier_with_export_file_id` | 2 | 0 | 0 |
| `identifier_with_mod_and_export_file_id` | 2 | 0 | 0 |
### examples/test_objs/gaps/fn_obj__p05.lit

[examples/test_objs/gaps/fn_obj__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/fn_obj__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have fn f(x R) R = x + 1
f(f(1)) = 3
```

First failed statement: `f(f(1)) = 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/fn_obj__p06.lit

[examples/test_objs/gaps/fn_obj__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/fn_obj__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `have_fn_equal`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have fn f(x R) fn(y R) R = fn(y R) R {x + y}
f(2)(3) = 5
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `f`", line: 3, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/fn_obj__p06.lit") }))`.

First failed statement: `have fn …`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/pow__p04.lit

[examples/test_objs/gaps/pow__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/pow__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
2^(-3) = 1 / 8
```

First failed statement: `2 ^ -3 = 1 / 8`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/abs__p05.lit

[examples/test_objs/gaps/abs__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/abs__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
forall x R:
    abs(-x) = abs(x)
```

First failed statement: `forall x R:
    abs (-x) = abs (x)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/min__p05.lit

[examples/test_objs/gaps/min__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/min__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
min(1 / 3, 1 / 2) = 1 / 3
```

First failed statement: `min(1 / 3, 1 / 2) = 1 / 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/max__p05.lit

[examples/test_objs/gaps/max__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/max__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
max(1 / 3, 1 / 2) = 1 / 2
```

First failed statement: `max(1 / 3, 1 / 2) = 1 / 2`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/sin__p04.lit

[examples/test_objs/gaps/sin__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sin__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sin(-pi / 2) = -1
```

First failed statement: `sin(-pi / 2) = -1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/sin__p06.lit

[examples/test_objs/gaps/sin__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sin__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
forall x R:
    sin(-x) = -sin(x)
```

First failed statement: `forall x R:
    sin(-x) = -sin(x)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/cos__p04.lit

[examples/test_objs/gaps/cos__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/cos__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
cos(-pi) = -1
```

First failed statement: `cos(-pi) = -1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/cos__p06.lit

[examples/test_objs/gaps/cos__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/cos__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
forall x R:
    cos(-x) = cos(x)
```

First failed statement: `forall x R:
    cos(-x) = cos(x)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/tan__p02.lit

[examples/test_objs/gaps/tan__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/tan__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
tan(pi) = 0
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/tan__p03.lit

[examples/test_objs/gaps/tan__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/tan__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
tan(pi / 4) = 1
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/tan__p04.lit

[examples/test_objs/gaps/tan__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/tan__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
tan(-pi / 4) = -1
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/cot__p02.lit

[examples/test_objs/gaps/cot__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/cot__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
cot(pi / 4) = 1
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/cot__p03.lit

[examples/test_objs/gaps/cot__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/cot__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
cot(-pi / 4) = -1
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/arctan__p02.lit

[examples/test_objs/gaps/arctan__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/arctan__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
arctan(1) = pi / 4
```

First failed statement: `arctan(1) = pi / 4`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/arctan__p03.lit

[examples/test_objs/gaps/arctan__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/arctan__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
arctan(-1) = -pi / 4
```

First failed statement: `arctan(-1) = -pi / 4`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/arccot__p02.lit

[examples/test_objs/gaps/arccot__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/arccot__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
arccot(1) = pi / 4
```

First failed statement: `arccot(1) = pi / 4`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/arccot__p04.lit

[examples/test_objs/gaps/arccot__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/arccot__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
arccot(-1) = 3 * pi / 4
```

First failed statement: `arccot(-1) = 3 * pi / 4`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/log__p05.lit

[examples/test_objs/gaps/log__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/log__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
log(1 / 2, 8) = -3
```

First failed statement: `log (1 / 2, 8) = -3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/log__p06.lit

[examples/test_objs/gaps/log__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/log__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
log(e, e) = 1
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/real_part__p04.lit

[examples/test_objs/gaps/real_part__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/real_part__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
re(-2 - i) = -2
```

First failed statement: `re(-2 - i) = -2`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/real_part__p06.lit

[examples/test_objs/gaps/real_part__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/real_part__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
re(i * i) = -1
```

First failed statement: `re(i * i) = -1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/imaginary_part__p04.lit

[examples/test_objs/gaps/imaginary_part__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/imaginary_part__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
img(-2 - i) = -1
```

First failed statement: `img(-2 - i) = -1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/complex_abs__p03.lit

[examples/test_objs/gaps/complex_abs__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/complex_abs__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
C_abs(3 + 4 * i) = 5
```

First failed statement: `C_abs(3 + 4 * i) = 5`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/complex_abs__p04.lit

[examples/test_objs/gaps/complex_abs__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/complex_abs__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
C_abs(-3) = 3
```

First failed statement: `C_abs(-3) = 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/complex_abs__p05.lit

[examples/test_objs/gaps/complex_abs__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/complex_abs__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
C_abs(-i) = 1
```

First failed statement: `C_abs(-i) = 1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/complex_abs__p06.lit

[examples/test_objs/gaps/complex_abs__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/complex_abs__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
forall z C:
    C_abs(z) >= 0
```

First failed statement: `forall z C:
    C_abs(z) >= 0`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/union__p01.lit

[examples/test_objs/gaps/union__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/union__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
union({1}, {2}) = {1, 2}
```

First failed statement: `union({1}, {2}) = {1, 2}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/intersect__p01.lit

[examples/test_objs/gaps/intersect__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/intersect__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
intersect({1, 2}, {2, 3}) = {2}
```

First failed statement: `intersect({1, 2}, {2, 3}) = {2}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/set_minus__p01.lit

[examples/test_objs/gaps/set_minus__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/set_minus__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
set_minus({1, 2}, {2}) = {1}
```

First failed statement: `set_minus({1, 2}, {2}) = {1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_union__p02.lit

[examples/test_objs/gaps/family_union__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_union__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
family_union({{1}}) = {1}
```

First failed statement: `family_union({{1}}) = {1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_union__p03.lit

[examples/test_objs/gaps/family_union__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_union__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
family_union({{1}, {2}}) = {1, 2}
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_union__p04.lit

[examples/test_objs/gaps/family_union__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_union__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
1 $in family_union({{1}, {2}})
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_union__p05.lit

[examples/test_objs/gaps/family_union__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_union__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let U = family_union({{}, {1, 2}})
U = {1, 2}
```

First failed statement: `U = {1, 2}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_intersect__p01.lit

[examples/test_objs/gaps/family_intersect__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_intersect__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
family_intersect({{1}}) = {1}
```

First failed statement: `family_intersect({{1}}) = {1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_intersect__p02.lit

[examples/test_objs/gaps/family_intersect__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_intersect__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
family_intersect({{1, 2}, {2, 3}}) = {2}
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_intersect__p03.lit

[examples/test_objs/gaps/family_intersect__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_intersect__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
family_intersect({{1}, {}}) = {}
```

First failed statement: `family_intersect({{1}, {}}) = {}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/family_intersect__p04.lit

[examples/test_objs/gaps/family_intersect__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_intersect__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let I = family_intersect({{1}, {2}})
I = I
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `I`", line: 3, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/family_intersect__p04.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/power_set__p06.lit

[examples/test_objs/gaps/power_set__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/power_set__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
power_set(power_set({})) = {{}, {{}}}
```

First failed statement: `power_set(power_set({})) = {{}, {{}}}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_union__p01.lit

[examples/test_objs/gaps/index_union__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_union__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let A = fn(k {1, 2}) power_set(N) {{1}}
let X = index_union({1, 2}, N, A)
X = X
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `X`", line: 4, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_union__p01.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_union__p02.lit

[examples/test_objs/gaps/index_union__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_union__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have fn A(k {1}) power_set(N) = {k}
index_union({1}, N, A) = {1}
```

First failed statement: `index_union({1}, N, A) = {1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_union__p04.lit

[examples/test_objs/gaps/index_union__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_union__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let A = fn(k {1}) power_set(N) {{1}}
$is_set(index_union({1}, N, A))
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_intersect__p01.lit

[examples/test_objs/gaps/index_intersect__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_intersect__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let A = fn(k {1, 2}) power_set(N) {{1}}
let X = index_intersect({1, 2}, N, A)
X = X
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `X`", line: 4, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_intersect__p01.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_intersect__p02.lit

[examples/test_objs/gaps/index_intersect__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_intersect__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have fn A(k {1}) power_set(N) = {k}
index_intersect({1}, N, A) = {1}
```

First failed statement: `index_intersect({1}, N, A) = {1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_intersect__p04.lit

[examples/test_objs/gaps/index_intersect__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_intersect__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let A = fn(k {1}) power_set(N) {{1}}
$is_set(index_intersect({1}, N, A))
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_cart__p01.lit

[examples/test_objs/gaps/index_cart__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_cart__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let A = fn(k {1}) power_set(N) {{1}}
let P = index_cart({1}, power_set(N), A)
P = P
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `P`", line: 4, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_cart__p01.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/index_cart__p02.lit

[examples/test_objs/gaps/index_cart__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_cart__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let A = fn(k {1, 2}) power_set(N) {{1, 2}}
let P = index_cart({1, 2}, power_set(N), A)
$is_set(P)
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `P`", line: 4, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/index_cart__p02.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/list_set__p04.lit

[examples/test_objs/gaps/list_set__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/list_set__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
{1, 2} = {2, 1}
```

First failed statement: `{1, 2} = {2, 1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/list_set__p06.lit

[examples/test_objs/gaps/list_set__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/list_set__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
{1} $in {{1}, {2}}
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/list_set__p07.lit

[examples/test_objs/gaps/list_set__p07.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/list_set__p07.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
(1, 2) $in {(1, 2), (2, 1)}
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/range__p04.lit

[examples/test_objs/gaps/range__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/range__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
range(-2, 1) = {-2, -1, 0}
```

First failed statement: `range(-2, 1) = {-2, -1, 0}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/range__p06.lit

[examples/test_objs/gaps/range__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/range__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
not 3 $in range(1, 3)
```

First failed statement: `not 3 $in range(1, 3)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/closed_range__p04.lit

[examples/test_objs/gaps/closed_range__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/closed_range__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
closed_range(-1, 1) = {-1, 0, 1}
```

First failed statement: `closed_range(-1, 1) = {-1, 0, 1}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/finite_seq_set__p05.lit

[examples/test_objs/gaps/finite_seq_set__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_seq_set__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn(x closed_range(0, 1)) R {x} $in finite_seq(R, 2)
```

First failed statement: `fn (x closed_range(0, 1)) R{x} $in finite_seq(R, 2)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/seq_set__p03.lit

[examples/test_objs/gaps/seq_set__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/seq_set__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn(x N) N {x} $in seq(N)
```

First failed statement: `fn (x N) N{x} $in seq(N)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/seq_set__p04.lit

[examples/test_objs/gaps/seq_set__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/seq_set__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn(x N) R {0} $in seq(R)
```

First failed statement: `fn (x N) R{0} $in seq(R)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/cart.lit

[examples/test_objs/cart.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/cart.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `mount_or_runtime`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sketch:
    (1, 2) $in cart(R, Z)

sketch:
    (1, 2, 3) $in cart(R, Z, N)

sketch:
    ((1, 2), 3) $in cart(cart(R, Z), N)

sketch:
    cart({}, {1}) = {}

sketch:
    cart_dim(cart(R, Z, N)) = 3
```

Session error: `Runtime(InternalBug("inferred fact failed well-definedness check"))`.

### examples/test_objs/gaps/cart__p04.lit

[examples/test_objs/gaps/cart__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/cart__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
cart({1}, {2}) = {(1, 2)}
```

First failed statement: `cart({1}, {2}) = {(1, 2)}`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/tuple__p04.lit

[examples/test_objs/gaps/tuple__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/tuple__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
((1, 2), 3)[1][2] = 2
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/tuple__p06.lit

[examples/test_objs/gaps/tuple__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/tuple__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
(1, 2) != (2, 1)
```

First failed statement: `(1, 2) != (2, 1)`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/cart_dim__p04.lit

[examples/test_objs/gaps/cart_dim__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/cart_dim__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `mount_or_runtime`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let C = cart(R, Z)
cart_dim(C) = 2
```

Session error: `Runtime(InternalBug("inferred fact failed well-definedness check"))`.

### examples/test_objs/proj.lit

[examples/test_objs/proj.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/proj.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `mount_or_runtime`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sketch:
    proj(cart(R, Z), 1) = R

sketch:
    proj(cart(R, Z), 2) = Z

sketch:
    proj(cart(R, Z, N), 3) = N

sketch:
    proj(cart(cart(R, Z), N), 1) = cart(R, Z)
```

Session error: `Runtime(InternalBug("inferred fact failed well-definedness check"))`.

### examples/test_objs/gaps/obj_at_index__p04.lit

[examples/test_objs/gaps/obj_at_index__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/obj_at_index__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
((1, 2), 3)[1][2] = 2
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/obj_at_index__p06.lit

[examples/test_objs/gaps/obj_at_index__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/obj_at_index__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
(2 + 3, 4 * 2)[2] = 8
```

First failed statement: `(2 + 3, 4 * 2)[2] = 8`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/fn_set__p05.lit

[examples/test_objs/gaps/fn_set__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/fn_set__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn(x R) R {x} $in fn(y R) R
```

First failed statement: `fn (x R) R{x} $in fn (y R) R`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/fn_set__p06.lit

[examples/test_objs/gaps/fn_set__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/fn_set__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn(x, y R) R {x + y} $in fn(a, b R) R
```

First failed statement: `fn (x, y R) R{x + y} $in fn (a, b R) R`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/anonymous_fn__p05.lit

[examples/test_objs/gaps/anonymous_fn__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/anonymous_fn__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn(x R) R {x + 1} $in fn(y R) R
```

First failed statement: `fn (x R) R{x + 1} $in fn (y R) R`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/anonymous_fn__p06.lit

[examples/test_objs/gaps/anonymous_fn__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/anonymous_fn__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let y = 3
fn(x R) R {x + y}(2) = 5
```

First failed statement: `fn (x R) R{x + y}(2) = 5`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/fn_range__p02.lit

[examples/test_objs/gaps/fn_range__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/fn_range__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
fn_range(fn(x R) R {x}) = R
```

First failed statement: `fn_range(fn (x R) R{x}) = R`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/sum__p03.lit

[examples/test_objs/gaps/sum__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sum__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sum(1, 3, fn(x Z) Z {x}) = 6
```

First failed statement: `sum(1, 3, fn (x Z) Z{x}) = 6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/sum__p04.lit

[examples/test_objs/gaps/sum__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sum__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sum(1, 3, fn(x Z) Z {2}) = 6
```

First failed statement: `sum(1, 3, fn (x Z) Z{2}) = 6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/product__p03.lit

[examples/test_objs/gaps/product__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/product__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
product(1, 3, fn(x Z) Z {x}) = 6
```

First failed statement: `product(1, 3, fn (x Z) Z{x}) = 6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/product__p04.lit

[examples/test_objs/gaps/product__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/product__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
product(1, 3, fn(x Z) Z {2}) = 8
```

First failed statement: `product(1, 3, fn (x Z) Z{2}) = 8`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/negative/sum_of_finite_set__n02.lit

[examples/test_objs/negative/sum_of_finite_set__n02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/negative/sum_of_finite_set__n02.lit)

Expected: **reject**; observed: **accept**; earliest reported phase: `success`; process exit: `0`.

<!-- litex:skip-test -->
```litex
let s = finite_set_sum({1}, fn(x {2}) Z {x})
```

### examples/test_objs/gaps/sum_of_finite_set__p03.lit

[examples/test_objs/gaps/sum_of_finite_set__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sum_of_finite_set__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_sum({1, 2}, fn(x Z) Z {x}) = 3
```

First failed statement: `finite_set_sum({1, 2}, fn (x Z) Z{x}) = 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/sum_of_finite_set__p04.lit

[examples/test_objs/gaps/sum_of_finite_set__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sum_of_finite_set__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_sum({2, 1}, fn(x Z) Z {x}) = 3
```

First failed statement: `finite_set_sum({2, 1}, fn (x Z) Z{x}) = 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/sum_of_finite_set__p06.lit

[examples/test_objs/gaps/sum_of_finite_set__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/sum_of_finite_set__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_sum(closed_range(3, 1), fn(x Z) Z {x}) = 0
```

First failed statement: `finite_set_sum(closed_range(3, 1), fn (x Z) Z{x}) = 0`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/negative/product_of_finite_set__n02.lit

[examples/test_objs/negative/product_of_finite_set__n02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/negative/product_of_finite_set__n02.lit)

Expected: **reject**; observed: **accept**; earliest reported phase: `success`; process exit: `0`.

<!-- litex:skip-test -->
```litex
let s = finite_set_product({1}, fn(x {2}) Z {x})
```

### examples/test_objs/gaps/product_of_finite_set__p03.lit

[examples/test_objs/gaps/product_of_finite_set__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/product_of_finite_set__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_product({2, 3}, fn(x Z) Z {x}) = 6
```

First failed statement: `finite_set_product({2, 3}, fn (x Z) Z{x}) = 6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/product_of_finite_set__p04.lit

[examples/test_objs/gaps/product_of_finite_set__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/product_of_finite_set__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_product({3, 2}, fn(x Z) Z {x}) = 6
```

First failed statement: `finite_set_product({3, 2}, fn (x Z) Z{x}) = 6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/product_of_finite_set__p06.lit

[examples/test_objs/gaps/product_of_finite_set__p06.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/product_of_finite_set__p06.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_product({0, 2}, fn(x Z) Z {x}) = 0
```

First failed statement: `finite_set_product({0, 2}, fn (x Z) Z{x}) = 0`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/reduce__p03.lit

[examples/test_objs/gaps/reduce__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/reduce__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
reduce(1, 3, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 6
```

First failed statement: `reduce(1, 3, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/reduce__p04.lit

[examples/test_objs/gaps/reduce__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/reduce__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
reduce(1, 3, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0) = -6
```

First failed statement: `reduce(1, 3, fn (x Z) Z{x}, fn (a, b Z) Z{a - b}, 0) = -6`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/reduce__p05.lit

[examples/test_objs/gaps/reduce__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/reduce__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
reduce(1, 3, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 10) = 16
```

First failed statement: `reduce(1, 3, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 10) = 16`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/negative/finite_set_reduce__n01.lit

[examples/test_objs/negative/finite_set_reduce__n01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/negative/finite_set_reduce__n01.lit)

Expected: **reject**; observed: **accept**; earliest reported phase: `success`; process exit: `0`.

<!-- litex:skip-test -->
```litex
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0)
```

### examples/test_objs/gaps/finite_set_reduce__p02.lit

[examples/test_objs/gaps/finite_set_reduce__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_reduce__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_reduce({2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 2
```

First failed statement: `finite_set_reduce({2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 2`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/finite_set_reduce__p03.lit

[examples/test_objs/gaps/finite_set_reduce__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_reduce__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
```

First failed statement: `finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/finite_set_reduce__p04.lit

[examples/test_objs/gaps/finite_set_reduce__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_reduce__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_reduce({2, 1}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
```

First failed statement: `finite_set_reduce({2, 1}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0) = 3`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/finite_set_reduce__p05.lit

[examples/test_objs/gaps/finite_set_reduce__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_reduce__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 10) = 13
```

First failed statement: `finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 10) = 13`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/finite_set_size__p05.lit

[examples/test_objs/gaps/finite_set_size__p05.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_size__p05.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_size({{1}, {2}}) = 2
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/negative/finite_set_max__n03.lit

[examples/test_objs/negative/finite_set_max__n03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/negative/finite_set_max__n03.lit)

Expected: **reject**; observed: **accept**; earliest reported phase: `success`; process exit: `0`.

<!-- litex:skip-test -->
```litex
let n = finite_set_max({i})
```

### examples/test_objs/gaps/finite_set_max__p04.lit

[examples/test_objs/gaps/finite_set_max__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_max__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_max({1 / 3, 1 / 2}) = 1 / 2
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/negative/finite_set_min__n03.lit

[examples/test_objs/negative/finite_set_min__n03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/negative/finite_set_min__n03.lit)

Expected: **reject**; observed: **accept**; earliest reported phase: `success`; process exit: `0`.

<!-- litex:skip-test -->
```litex
let n = finite_set_min({i})
```

### examples/test_objs/gaps/finite_set_min__p04.lit

[examples/test_objs/gaps/finite_set_min__p04.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/finite_set_min__p04.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
finite_set_min({1 / 3, 1 / 2}) = 1 / 3
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/struct_obj__p01.lit

[examples/test_objs/gaps/struct_obj__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/struct_obj__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
struct Point:
    x R
    y R
have p &Point = (1, 2)
p.x = 1
```

First failed statement: `p.x = 1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/struct_obj__p02.lit

[examples/test_objs/gaps/struct_obj__p02.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/struct_obj__p02.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
struct Pair<S set>:
    first S
    second S
have p &Pair<N> = (1, 2)
p.second = 2
```

First failed statement: `p.second = 2`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/field_access__p01.lit

[examples/test_objs/gaps/field_access__p01.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/field_access__p01.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
struct Point:
    x R
    y R
have p &Point = (1, 2)
p.x = 1
p.y = 2
```

First failed statement: `p.x = 1`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/standard_set_r_pos__p03.lit

[examples/test_objs/gaps/standard_set_r_pos__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/standard_set_r_pos__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sqrt(2) $in R+
```

First failed statement: `sqrt (2) $in R+`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/standard_set_r_star__p03.lit

[examples/test_objs/gaps/standard_set_r_star__p03.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/standard_set_r_star__p03.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sqrt(2) $in R*
```

First failed statement: `sqrt (2) $in R*`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/identifier_with_export_file_id__p04/main.lit

[examples/test_objs/gaps/identifier_with_export_file_id__p04/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/identifier_with_export_file_id__p04/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have k R = 1
tuple_dim(base::pair) = 2
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/identifier_with_export_file_id__p05/main.lit

[examples/test_objs/gaps/identifier_with_export_file_id__p05/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/identifier_with_export_file_id__p05/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have k R = 1
tuple_dim(other::pair) = 3
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p04/main.lit

[examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p04/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p04/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have k R = 1
tuple_dim(Values::base::pair) = 2
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p05/main.lit

[examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p05/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p05/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have k R = 1
tuple_dim(Values::other::pair) = 3
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

## Appendix B: complete remaining public-file mismatch inventory

### examples/module_manager/cwd_eval/main.lit

[examples/module_manager/cwd_eval/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/cwd_eval/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
1 = 1
```

Configuration: [examples/module_manager/cwd_eval/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/cwd_eval/litex.config)

```toml
[hierarchy]
module

[export]
main = "./main.lit"
```

### examples/module_manager/export_order_repo/A/chap2.lit

[examples/module_manager/export_order_repo/A/chap2.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/A/chap2.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
have x R = 1
```

Configuration: [examples/module_manager/export_order_repo/A/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/A/litex.config)

```toml
[hierarchy]
submodule

[export]
chap2 = "./chap2.lit"
chap3 = "./chap3.lit"
main = "./main.lit"
```

### examples/module_manager/export_order_repo/A/chap3.lit

[examples/module_manager/export_order_repo/A/chap3.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/A/chap3.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
A::chap2::x = 1
have z R = 1
```

Configuration: [examples/module_manager/export_order_repo/A/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/A/litex.config)

```toml
[hierarchy]
submodule

[export]
chap2 = "./chap2.lit"
chap3 = "./chap3.lit"
main = "./main.lit"
```

### examples/module_manager/export_order_repo/A/main.lit

[examples/module_manager/export_order_repo/A/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/A/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
A::chap3::z = 1
```

Configuration: [examples/module_manager/export_order_repo/A/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/A/litex.config)

```toml
[hierarchy]
submodule

[export]
chap2 = "./chap2.lit"
chap3 = "./chap3.lit"
main = "./main.lit"
```

### examples/module_manager/export_order_repo/explicit_export_selection.lit

[examples/module_manager/export_order_repo/explicit_export_selection.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/explicit_export_selection.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
have explicit_export_selection_witness R = 1

try:
    unlisted_sidecar::unlisted_sidecar_value = 2
```

Configuration: [examples/module_manager/export_order_repo/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/litex.config)

```toml
[hierarchy]
module

[export]
A = "./A"
explicit_export_selection = "./explicit_export_selection.lit"
main = "./main.lit"
```

### examples/module_manager/export_order_repo/main.lit

[examples/module_manager/export_order_repo/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
A::chap3::z = 1

have answer R = 1
```

Configuration: [examples/module_manager/export_order_repo/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/litex.config)

```toml
[hierarchy]
module

[export]
A = "./A"
explicit_export_selection = "./explicit_export_selection.lit"
main = "./main.lit"
```

### examples/module_manager/export_order_repo/unlisted_sidecar.lit

[examples/module_manager/export_order_repo/unlisted_sidecar.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/unlisted_sidecar.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
have unlisted_sidecar_value R = 2
```

Configuration: [examples/module_manager/export_order_repo/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/export_order_repo/litex.config)

```toml
[hierarchy]
module

[export]
A = "./A"
explicit_export_selection = "./explicit_export_selection.lit"
main = "./main.lit"
```

### examples/module_manager/file_extra/a.lit

[examples/module_manager/file_extra/a.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_extra/a.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
1 = 1
```

Configuration: [examples/module_manager/file_extra/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_extra/litex.config)

```toml
[hierarchy]
module

[export]
a = "./a.lit"
```

### examples/module_manager/file_extra/scratch.lit

[examples/module_manager/file_extra/scratch.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_extra/scratch.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
1 = 1
```

Configuration: [examples/module_manager/file_extra/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_extra/litex.config)

```toml
[hierarchy]
module

[export]
a = "./a.lit"
```

### examples/module_manager/file_prefix/a.lit

[examples/module_manager/file_prefix/a.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_prefix/a.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
1 = 1
```

Configuration: [examples/module_manager/file_prefix/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_prefix/litex.config)

```toml
[hierarchy]
module

[export]
a = "./a.lit"
b = "./b.lit"
```

### examples/module_manager/file_prefix/b.lit

[examples/module_manager/file_prefix/b.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_prefix/b.lit)

Expected: **reject**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
1 = 2
```

Configuration: [examples/module_manager/file_prefix/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/file_prefix/litex.config)

```toml
[hierarchy]
module

[export]
a = "./a.lit"
b = "./b.lit"
```

### examples/module_manager/function_family_bindings/main.lit

[examples/module_manager/function_family_bindings/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/function_family_bindings/main.lit)

Expected: **accept**; observed: **infrastructure_failure**; earliest reported phase: `launch_or_json`; process exit: `-6`.

<!-- litex:skip-test -->
```litex
release obj def Other::functions::step

template<t R>:
    have fn step(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: Other::functions::step(n - 1)

\step<0>(1) = Other::functions::step(1 - 1)
Other::functions::step(1 - 1) = 1
\step<0>(1) = 1

prop get(a R):
    exist x R st {x = 1}
release thm Other::functions::ready
obtain k from $Other::functions::get(0)
k = 0
witness $Other::functions::get(2) from 0
```

Process stderr:

```text
thread 'litex-launch' (68331025) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

### examples/module_manager/import_alias_qualified_arithmetic/main.lit

[examples/module_manager/import_alias_qualified_arithmetic/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/import_alias_qualified_arithmetic/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
gf::main::a + gf::main::a = gf::main2::b
gf::main::pair[1] = 3
gf::main2::pair[1] = 8
cart_dim(gf::main::ProductSet) = 2
```

Configuration: [examples/module_manager/import_alias_qualified_arithmetic/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/import_alias_qualified_arithmetic/litex.config)

```toml
[hierarchy]
module

[import]
gf = "../../_internal/fixtures/geometry_foundation"

[export]
main = "./main.lit"
```

### examples/module_manager/lib_pkg/base.lit

[examples/module_manager/lib_pkg/base.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/lib_pkg/base.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
prop above_zero(x R):
    x > 0

thm add_zero_right:
    ? forall x R:
        x + 0 = x
    x + 0 = x
```

Configuration: [examples/module_manager/lib_pkg/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/lib_pkg/litex.config)

```toml
[hierarchy]
module

[export]
base = "./base.lit"
```

### examples/module_manager/repo/main.lit

[examples/module_manager/repo/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/repo/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
by def $Lib::base::above_zero(1)

release thm Lib::base::add_zero_right(2)
2 + 0 = 2

by thm Lib::base::add_zero_right(3) => 3 + 0 = 3
```

Configuration: [examples/module_manager/repo/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/repo/litex.config)

```toml
[hierarchy]
module

[import]
Lib = "../lib_pkg"

[export]
main = "./main.lit"
```

### examples/module_manager/trusted_template_prefix/main.lit

[examples/module_manager/trusted_template_prefix/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/trusted_template_prefix/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
\prefix::copied<R> = R
```

Configuration: [examples/module_manager/trusted_template_prefix/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/trusted_template_prefix/litex.config)

```toml
[hierarchy]
module

[export]
prefix = "./prefix.lit"
main = "./main.lit"
```

### examples/module_manager/trusted_template_prefix/prefix.lit

[examples/module_manager/trusted_template_prefix/prefix.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/trusted_template_prefix/prefix.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
template<S set>:
    have copied set = S
```

Configuration: [examples/module_manager/trusted_template_prefix/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/module_manager/trusted_template_prefix/litex.config)

```toml
[hierarchy]
module

[export]
prefix = "./prefix.lit"
main = "./main.lit"
```

### examples/proof_nodes/atomic/by_builtin_rule/less_equal_finite_set_size_surjection_codomain_le_domain.lit

[examples/proof_nodes/atomic/by_builtin_rule/less_equal_finite_set_size_surjection_codomain_le_domain.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/atomic/by_builtin_rule/less_equal_finite_set_size_surjection_codomain_le_domain.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have A set = {1, 2}
have B set = {1}
have fn f(x A) B = 1
exist x A st {x = 1}
by def $surjective(A, B, f)
$is_finite_set(A)
finite_set_size(B) <= finite_set_size(A)
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/proof_nodes/atomic/by_builtin_strategy/standard_set_subset_and_fn_app_in_codomain.lit

[examples/proof_nodes/atomic/by_builtin_strategy/standard_set_subset_and_fn_app_in_codomain.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/atomic/by_builtin_strategy/standard_set_subset_and_fn_app_in_codomain.lit)

Expected: **accept**; observed: **infrastructure_failure**; earliest reported phase: `timeout`; process exit: `None`.

<!-- litex:skip-test -->
```litex
have fn vec(A, B cart(R, R)) cart(R, R) = (B[1] - A[1], B[2] - A[2])
have fn dot(u, v cart(R, R)) R = u[1] * v[1] + u[2] * v[2]

have p, q, r cart(R, R)

dot(vec(q, p), vec(q, r)) $in R
dot(vec(q, p), vec(q, r)) $in C
vec(q, p) $in cart(R, R)
```

No completed proof outcome within the 20-second process deadline. This does not establish mathematical rejection or nontermination.

### examples/proof_nodes/atomic/by_definition/builtin_is_choice_function_for.lit

[examples/proof_nodes/atomic/by_definition/builtin_is_choice_function_for.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/atomic/by_definition/builtin_is_choice_function_for.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `by_def`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have fn g_choice(alpha {1}) power_set({1}) = {1}
have fn f_choice(alpha {1}) {1} = 1
forall alpha {1}:
    f_choice(alpha) $in g_choice(alpha)
by def $is_choice_function_for({1}, power_set({1}), g_choice, f_choice)
```

First failed statement: `by def`. Full nested requirements are in the linked raw JSON.

### examples/proof_nodes/equal/by_builtin_rule/cart_with_empty_factor.lit

[examples/proof_nodes/equal/by_builtin_rule/cart_with_empty_factor.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/equal/by_builtin_rule/cart_with_empty_factor.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `mount_or_runtime`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have A set
cart(A, {}) = {}
```

Session error: `Runtime(InternalBug("inferred fact failed well-definedness check"))`.

### examples/proof_nodes/equal/by_builtin_rule/pow_of_log_inverse.lit

[examples/proof_nodes/equal/by_builtin_rule/pow_of_log_inverse.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/equal/by_builtin_rule/pow_of_log_inverse.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `well_defined`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have x N
2^(log(2, 2^x)) = 2^x
```

First failed statement: `<wd_failed>`. Full nested requirements are in the linked raw JSON.

### examples/proof_nodes/equal/by_builtin_rule/sqrt_quotient.lit

[examples/proof_nodes/equal/by_builtin_rule/sqrt_quotient.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/equal/by_builtin_rule/sqrt_quotient.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have a R+
have b R+
a / b $in R+
sqrt(b) $in R*
sqrt(a / b) = sqrt(a) / sqrt(b)
```

First failed statement: `sqrt (b) $in R*`. Full nested requirements are in the linked raw JSON.

### examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit

[examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit)

Expected: **accept**; observed: **infrastructure_failure**; earliest reported phase: `timeout`; process exit: `None`.

<!-- litex:skip-test -->
```litex
have fn vec(a,b cart(R,R)) cart(R,R) = (b[1]-a[1],b[2]-a[2])
have a,b cart(R,R)
vec(a,b)[1] = b[1]-a[1]
vec(a,b)[2] = b[2]-a[2]
vec(a,b) = (vec(a,b)[1],vec(a,b)[2])
let vector_alias = vec
vector_alias(a,b)[1] = b[1]-a[1]
```

No completed proof outcome within the 20-second process deadline. This does not establish mathematical rejection or nontermination.

### examples/stmt_nodes/definition/let_template_struct_aliases.lit

[examples/stmt_nodes/definition/let_template_struct_aliases.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/definition/let_template_struct_aliases.lit)

Expected: **accept**; observed: **infrastructure_failure**; earliest reported phase: `timeout`; process exit: `None`.

<!-- litex:skip-test -->
```litex
struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

let triple_R = \triple<R>

let chosen = \triple<R>(1, 2, 3)

triple_R(4, 5, 6) = (4, 5, 6)
chosen = (1, 2, 3)

have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1


struct ScalarOps:
    add fn(x, y R) R

struct Space:
    scalars &ScalarOps

thm callable_struct_field_alias:
    ? forall space &Space, x, y R:
        space.scalars.add(x, y) = space.scalars.add(x, y)
    let scalar_add = space.scalars.add
    scalar_add(x, y) = space.scalars.add(x, y)
```

No completed proof outcome within the 20-second process deadline. This does not establish mathematical rejection or nontermination.

### examples/stmt_nodes/release_and_expand/builtin_thm/finite_set_has_bijective_index.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/finite_set_has_bijective_index.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/finite_set_has_bijective_index.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm finite_set_has_bijective_index({1, 2})
exist idx finite_seq({1, 2}, finite_set_size({1, 2})) st {$bijective(closed_range(1, finite_set_size({1, 2})), {1, 2}, idx)}
```

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_exists.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_exists.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_exists.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm real_greatest_lower_bound_exists({0}, -1)
exist L R st {$is_real_greatest_lower_bound({0}, L)}
```

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_le_member.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_le_member.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_le_member.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm real_greatest_lower_bound_exists({0}, -1)
obtain L from exist L R st {$is_real_greatest_lower_bound({0}, L)}
release thm real_greatest_lower_bound_le_member({0}, L, 0)
L <= 0
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `L`", line: 7, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_greatest_lower_bound_le_member.lit") }))`.

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_exists.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_exists.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_exists.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm real_least_upper_bound_exists({0}, 1)
exist L R st {$is_real_least_upper_bound({0}, L)}
```

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_le_upper_bound.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_le_upper_bound.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_le_upper_bound.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm real_least_upper_bound_exists({0}, 1)
obtain L from exist L R st {$is_real_least_upper_bound({0}, L)}
release thm real_least_upper_bound_le_upper_bound({0}, L, 1)
L <= 1
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `L`", line: 7, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_least_upper_bound_le_upper_bound.lit") }))`.

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/builtin_thm/real_lower_bound_le_greatest_lower_bound.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/real_lower_bound_le_greatest_lower_bound.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_lower_bound_le_greatest_lower_bound.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm real_greatest_lower_bound_exists({0}, -1)
obtain L from exist L R st {$is_real_greatest_lower_bound({0}, L)}
release thm real_lower_bound_le_greatest_lower_bound({0}, L, -1)
-1 <= L
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `L`", line: 7, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_lower_bound_le_greatest_lower_bound.lit") }))`.

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/builtin_thm/real_member_le_least_upper_bound.lit

[examples/stmt_nodes/release_and_expand/builtin_thm/real_member_le_least_upper_bound.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_member_le_least_upper_bound.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `release_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
release thm real_least_upper_bound_exists({0}, 1)
obtain L from exist L R st {$is_real_least_upper_bound({0}, L)}
release thm real_member_le_least_upper_bound({0}, L, 0)
0 <= L
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `L`", line: 7, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/builtin_thm/real_member_le_least_upper_bound.lit") }))`.

First failed statement: `release thm …`. Full nested requirements are in the linked raw JSON.

### examples/stmt_nodes/release_and_expand/release_axiom_of_choice.lit

[examples/stmt_nodes/release_and_expand/release_axiom_of_choice.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/stmt_nodes/release_and_expand/release_axiom_of_choice.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `claim`; process exit: `1`.

<!-- litex:skip-test -->
```litex
claim:
    ? forall F set:
        forall A F:
            $is_nonempty_set(A)
        =>:
            exist f fn(A F) family_union(F) st {$is_choice_function_for(F, F, fn(B F) F {B}, f)}
    release axiom_of_choice: set F:
        forall A F:
            $is_nonempty_set(A)
```

First failed statement: `claim`. Full nested requirements are in the linked raw JSON.

### examples/wd/known_function_cart_projection.lit

[examples/wd/known_function_cart_projection.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/wd/known_function_cart_projection.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `mount_or_runtime`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have plane set = cart(R,R)
have p plane
$is_tuple(p)
tuple_dim(p) = 2
p[1] $in R
have fn pair(x R) cart(R,R) = (x,x)
have a R
$is_tuple(pair(a))
tuple_dim(pair(a)) = 2
pair(a)[1] $in R
```

Session error: `Runtime(InternalBug("inferred fact failed well-definedness check"))`.

### examples/wd/obj/index_cart.lit

[examples/wd/obj/index_cart.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/wd/obj/index_cart.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let g = fn(alpha {1}) power_set(N) {{1}}
let c = index_cart({1}, power_set(N), g)
c = c
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `c`", line: 9, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/wd/obj/index_cart.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/wd/obj/index_union.lit

[examples/wd/obj/index_union.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/wd/obj/index_union.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `let`; process exit: `1`.

<!-- litex:skip-test -->
```litex
let family = fn(k {1, 2}) power_set(N) {{1}}
let u = index_union({1, 2}, N, family)
let v = index_intersect({1, 2}, N, family)
u = u
v = v
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `u`", line: 10, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/wd/obj/index_union.lit") }))`.

First failed statement: `let …`. Full nested requirements are in the linked raw JSON.

### examples/wd/obj/mul_nested_fn_app_in_c.lit

[examples/wd/obj/mul_nested_fn_app_in_c.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/wd/obj/mul_nested_fn_app_in_c.lit)

Expected: **accept**; observed: **infrastructure_failure**; earliest reported phase: `timeout`; process exit: `None`.

<!-- litex:skip-test -->
```litex
have fn vec(A, B cart(R, R)) cart(R, R) = (B[1] - A[1], B[2] - A[2])
have fn dot(u, v cart(R, R)) R = u[1] * v[1] + u[2] * v[2]

have p, q, r cart(R, R)
2 * dot(vec(q, p), vec(q, r)) = 2 * dot(vec(q, p), vec(q, r))
dot(vec(q, p), vec(q, r)) + 0 = dot(vec(q, p), vec(q, r))
-(dot(vec(q, p), vec(q, r))) = -(dot(vec(q, p), vec(q, r)))

dot(vec(q, p), vec(q, r)) $in C
dot(vec(q, p), vec(q, r)) $in R
```

No completed proof outcome within the 20-second process deadline. This does not establish mathematical rejection or nontermination.

## Appendix C: statement and module mismatches

### ReleaseAxiomOfChoiceStmt/whole-file

[examples/test_statements/release_axiom_of_choice_stmt.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_statements/release_axiom_of_choice_stmt.lit)

<!-- litex:skip-test -->
```litex
claim:
    ? forall F set:
        forall A F:
            $is_nonempty_set(A)
        =>:
            exist f fn(A F) family_union(F) st {$is_choice_function_for(F, F, fn(B F) F {B}, f)}
    release axiom_of_choice: set F:
        forall A F:
            $is_nonempty_set(A)

claim:
    ? forall ChoiceFamily set:
        forall A ChoiceFamily:
            $is_nonempty_set(A)
        =>:
            exist f fn(A ChoiceFamily) family_union(ChoiceFamily) st {$is_choice_function_for(ChoiceFamily, ChoiceFamily, fn(B ChoiceFamily) ChoiceFamily {B}, f)}
    release axiom_of_choice: set ChoiceFamily:
        forall A ChoiceFamily:
            $is_nonempty_set(A)

release axiom_of_choice: set {{1}}:
    forall A {{1}}:
        $is_nonempty_set(A)
```

Observed exit: `1`. Runner mismatches: success differs from expectation, exit code differs from expectation, positive contains an error or no executed statements. The raw record preserves every statement result.

### ReleaseAxiomOfChoiceStmt/conditional-family-choice

<!-- litex:skip-test -->
```litex
claim:
    ? forall F set:
        forall A F:
            $is_nonempty_set(A)
        =>:
            exist f fn(A F) family_union(F) st {$is_choice_function_for(F, F, fn(B F) F {B}, f)}
    release axiom_of_choice: set F:
        forall A F:
            $is_nonempty_set(A)

```

Observed exit: `1`. Runner mismatches: success differs from expectation, exit code differs from expectation, positive contains an error or no executed statements. The raw record preserves every statement result.

### ReleaseAxiomOfChoiceStmt/renamed-family-choice

<!-- litex:skip-test -->
```litex
claim:
    ? forall ChoiceFamily set:
        forall A ChoiceFamily:
            $is_nonempty_set(A)
        =>:
            exist f fn(A ChoiceFamily) family_union(ChoiceFamily) st {$is_choice_function_for(ChoiceFamily, ChoiceFamily, fn(B ChoiceFamily) ChoiceFamily {B}, f)}
    release axiom_of_choice: set ChoiceFamily:
        forall A ChoiceFamily:
            $is_nonempty_set(A)

```

Observed exit: `1`. Runner mismatches: success differs from expectation, exit code differs from expectation, positive contains an error or no executed statements. The raw record preserves every statement result.

### ReleaseAxiomOfChoiceStmt/singleton-nonempty-family

<!-- litex:skip-test -->
```litex
release axiom_of_choice: set {{1}}:
    forall A {{1}}:
        $is_nonempty_set(A)

```

Observed exit: `1`. Runner mismatches: success differs from expectation, exit code differs from expectation, positive contains an error or no executed statements. The raw record preserves every statement result.

### boundary/strict-choice-allowed

[examples/test_statements/boundaries/strict-choice-allowed.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/test_statements/boundaries/strict-choice-allowed.lit)

<!-- litex:skip-test -->
```litex
release axiom_of_choice: set {{1}}:
    forall A {{1}}:
        $is_nonempty_set(A)
```

Observed exit: `1`. Runner mismatches: success differs from expectation, exit code differs from expectation, positive contains an error or no executed statements. The raw record preserves every statement result.

| Module | Mode | Observed phase | Exit |
| --- | --- | --- | ---: |
| `examples/module_manager/cwd_eval` | repository | `launch_config` | 2 |
| `examples/module_manager/export_order_repo/A` | repository | `launch_config` | 2 |
| `examples/module_manager/export_order_repo` | repository | `launch_config` | 2 |
| `examples/module_manager/file_extra` | repository | `launch_config` | 2 |
| `examples/module_manager/file_prefix` | repository | `launch_config` | 2 |
| `examples/module_manager/function_family_bindings` | repository | `launch_or_json` | -6 |
| `examples/module_manager/import_alias_qualified_arithmetic` | repository | `launch_config` | 2 |
| `examples/module_manager/lib_pkg` | repository | `launch_config` | 2 |
| `examples/module_manager/repo` | repository | `launch_config` | 2 |
| `examples/module_manager/trusted_template_prefix` | repository | `launch_config` | 2 |
| `examples/module_manager/cwd_eval` | cwd_eval | `launch_config` | 2 |
| `examples/module_manager/file_prefix` | cwd_eval | `launch_config` | 2 |

## Appendix D: exploratory failures

These source files are not public acceptance fixtures; classify removed syntax or unfinished proofs before proposing a kernel repair.

### examples/_internal/drafts/dihedral_group_isomorphism_draft.lit

[examples/_internal/drafts/dihedral_group_isomorphism_draft.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/drafts/dihedral_group_isomorphism_draft.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
prop injective_fn(S, T set, phi fn(x S) T):
    forall x1, x2 S:
        phi(x1) = phi(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, phi fn(x S) T):
    forall y T:
        exist x S st {y = phi(x)}

prop bijective_fn(S, T set, phi fn(x S) T):
    $injective_fn(S, T, phi)
    $surjective_fn(S, T, phi)

abstract_prop group_homomorphism(G, H, phi)

prop group_isomorphism(G, H set, phi fn(x G) H):
    $group_homomorphism(G, H, phi)
    $bijective_fn(G, H, phi)

prop isomorphic_group(G, H set):
    exist phi fn(x G) H st {$group_isomorphism(G, H, phi)}

abstract_prop generated_by_r_and_f(G, r, f)
abstract_prop relator_r8_is_identity(G, r)
abstract_prop relator_f2_is_identity(G, f)
abstract_prop relator_rfrf_is_identity(G, r, f)

prop presentation_r8_f2_rfrf(G set, r, f G):
    $generated_by_r_and_f(G, r, f)
    $relator_r8_is_identity(G, r)
    $relator_f2_is_identity(G, f)
    $relator_rfrf_is_identity(G, r, f)

abstract_prop regular_octagon_rotation_order_8(D, rho)
abstract_prop regular_octagon_reflection_order_2(D, sigma)
abstract_prop regular_octagon_flip_relation(D, rho, sigma)
abstract_prop regular_octagon_generated_by_rotation_and_reflection(D, rho, sigma)
abstract_prop octagon_rotation_collection_has_8_members(D, rho)
abstract_prop octagon_reflection_collection_has_8_members(D, rho, sigma)
abstract_prop octagon_rotation_and_reflection_collections_cover(D, rho, sigma)
abstract_prop octagon_rotation_and_reflection_collections_disjoint(D, rho, sigma)

prop regular_octagon_has_16_symmetries(D set, rho, sigma D):
    $octagon_rotation_collection_has_8_members(D, rho)
    $octagon_reflection_collection_has_8_members(D, rho, sigma)
    $octagon_rotation_and_reflection_collections_cover(D, rho, sigma)
    $octagon_rotation_and_reflection_collections_disjoint(D, rho, sigma)

prop regular_octagon_dihedral_group(D set, rho, sigma D):
    $regular_octagon_rotation_order_8(D, rho)
    $regular_octagon_reflection_order_2(D, sigma)
    $regular_octagon_flip_relation(D, rho, sigma)
    $regular_octagon_generated_by_rotation_and_reflection(D, rho, sigma)
    $regular_octagon_has_16_symmetries(D, rho, sigma)

abstract_prop generator_map(G, D, r, f, rho, sigma, phi)
abstract_prop has_at_most_16_elements(G)
abstract_prop has_exactly_16_elements(G)
abstract_prop target_relators_match_presentation(G, D, r, f, rho, sigma)

prop target_satisfies_presentation_relators(D set, rho, sigma D):
    $regular_octagon_rotation_order_8(D, rho)
    $regular_octagon_reflection_order_2(D, sigma)
    $regular_octagon_flip_relation(D, rho, sigma)

prop presentation_universal_map(G, D set, r, f G, rho, sigma D):
    exist phi fn(x G) D st {$group_homomorphism(G, D, phi), phi(r) = rho, phi(f) = sigma, $generator_map(G, D, r, f, rho, sigma, phi)}

abstract_prop fr_rewrites_to_inverse_rotation_then_f(G, r, f)
abstract_prop word_has_all_reflections_on_right(G, r, f)
abstract_prop adjacent_reflections_cancel(G, f)
abstract_prop every_generator_word_reduces_to_normal_form(G, r, f)
abstract_prop written_as_r_power(G, r, x)
abstract_prop written_as_r_power_times_f(G, r, f, x)
abstract_prop exponent_reduced_mod_8(G, r)
abstract_prop element_uses_one_of_16_dihedral_slots(G, r, f, x)

prop can_move_reflection_to_the_right(G set, r, f G):
    $fr_rewrites_to_inverse_rotation_then_f(G, r, f)

prop presentation_word_reduction(G set, r, f G):
    $word_has_all_reflections_on_right(G, r, f)
    $adjacent_reflections_cancel(G, f)
    $every_generator_word_reduces_to_normal_form(G, r, f)

prop dihedral_normal_form(G set, r, f, x G):
    $written_as_r_power(G, r, x) or $written_as_r_power_times_f(G, r, f, x)

prop every_element_has_dihedral_normal_form(G set, r, f G):
    forall x G:
        $dihedral_normal_form(G, r, f, x)

prop each_normal_form_uses_one_of_16_slots(G set, r, f G):
    forall x G:
        $dihedral_normal_form(G, r, f, x)
        =>:
            $element_uses_one_of_16_dihedral_slots(G, r, f, x)

prop normal_forms_have_at_most_16_slots(G set, r, f G):
    $exponent_reduced_mod_8(G, r)
    $each_normal_form_uses_one_of_16_slots(G, r, f)

prop presentation_reflection_swap_rule(G set, r, f G):
    $can_move_reflection_to_the_right(G, r, f)

prop presentation_normal_form_cover(G set, r, f G):
    $every_element_has_dihedral_normal_form(G, r, f)

prop presentation_normal_form_slot_bound(G set, r, f G):
    $normal_forms_have_at_most_16_slots(G, r, f)

abstract_prop normal_form_cover_uses_16_slot_map(G, r, f)
abstract_prop slot_map_bounds_cardinality_by_16(G, r, f)

prop presentation_normal_form_bound(G set, r, f G):
    $presentation_normal_form_cover(G, r, f)
    $presentation_normal_form_slot_bound(G, r, f)
    $normal_form_cover_uses_16_slot_map(G, r, f)
    $slot_map_bounds_cardinality_by_16(G, r, f)
    $has_at_most_16_elements(G)

prop regular_octagon_d8_cardinality(D set, rho, sigma D):
    $regular_octagon_has_16_symmetries(D, rho, sigma)
    $has_exactly_16_elements(D)

abstract_prop image_contains_rho_and_sigma(G, D, r, f, rho, sigma, phi)
abstract_prop image_contains_all_rho_sigma_words(G, D, rho, sigma, phi)
abstract_prop image_equals_target_group(G, D, phi)

prop presentation_map_surjective(G, D set, r, f G, rho, sigma D, phi fn(x G) D):
    $group_homomorphism(G, D, phi)
    $regular_octagon_generated_by_rotation_and_reflection(D, rho, sigma)
    $generator_map(G, D, r, f, rho, sigma, phi)
    $image_equals_target_group(G, D, phi)
    $surjective_fn(G, D, phi)

abstract_prop finite_cardinality_comparison_for_phi(G, D, phi)
abstract_prop surjective_same_size_map_is_injective(G, D, phi)

prop finite_surjective_map_bijective(G, D set, r, f G, rho, sigma D, phi fn(x G) D):
    $presentation_map_surjective(G, D, r, f, rho, sigma, phi)
    $presentation_normal_form_bound(G, r, f)
    $regular_octagon_d8_cardinality(D, rho, sigma)
    $finite_cardinality_comparison_for_phi(G, D, phi)
    $surjective_same_size_map_is_injective(G, D, phi)
    $bijective_fn(G, D, phi)

trust forall G, D set, r, f G, rho, sigma D:
    $presentation_r8_f2_rfrf(G, r, f)
    $regular_octagon_dihedral_group(D, rho, sigma)
    =>:
        exist phi fn(x G) D st {$group_homomorphism(G, D, phi), phi(r) = rho, phi(f) = sigma, $generator_map(G, D, r, f, rho, sigma, phi)}

trust forall G set, r, f G:
    $presentation_r8_f2_rfrf(G, r, f)
    =>:
        $presentation_reflection_swap_rule(G, r, f)

trust forall G set, r, f G:
    $presentation_r8_f2_rfrf(G, r, f)
    $presentation_reflection_swap_rule(G, r, f)
    =>:
        $presentation_normal_form_cover(G, r, f)

trust forall G set, r, f G:
    $presentation_r8_f2_rfrf(G, r, f)
    =>:
        $presentation_normal_form_slot_bound(G, r, f)

trust forall G set, r, f G:
    $presentation_normal_form_cover(G, r, f)
    $presentation_normal_form_slot_bound(G, r, f)
    =>:
        $presentation_normal_form_bound(G, r, f)

claim:
    ? forall G set, r, f G:
        $presentation_r8_f2_rfrf(G, r, f)
        =>:
            $presentation_normal_form_bound(G, r, f)
    $presentation_reflection_swap_rule(G, r, f)
    $presentation_normal_form_cover(G, r, f)
    $presentation_normal_form_slot_bound(G, r, f)

trust forall D set, rho, sigma D:
    $regular_octagon_dihedral_group(D, rho, sigma)
    =>:
        $regular_octagon_d8_cardinality(D, rho, sigma)

trust forall G, D set, r, f G, rho, sigma D, phi fn(x G) D:
    $regular_octagon_dihedral_group(D, rho, sigma)
    $generator_map(G, D, r, f, rho, sigma, phi)
    =>:
        $presentation_map_surjective(G, D, r, f, rho, sigma, phi)

trust forall G, D set, r, f G, rho, sigma D, phi fn(x G) D:
    $presentation_map_surjective(G, D, r, f, rho, sigma, phi)
    $presentation_normal_form_bound(G, r, f)
    $regular_octagon_d8_cardinality(D, rho, sigma)
    =>:
        $finite_surjective_map_bijective(G, D, r, f, rho, sigma, phi)

claim:
    ? forall G, D set, r, f G, rho, sigma D:
        $presentation_r8_f2_rfrf(G, r, f)
        $regular_octagon_dihedral_group(D, rho, sigma)
        =>:
            $isomorphic_group(G, D)

    obtain phi from exist phi fn(x G) D st {$group_homomorphism(G, D, phi), phi(r) = rho, phi(f) = sigma, $generator_map(G, D, r, f, rho, sigma, phi)}

    $group_homomorphism(G, D, phi)
    phi(r) = rho
    phi(f) = sigma
    $generator_map(G, D, r, f, rho, sigma, phi)
    $presentation_normal_form_bound(G, r, f)
    $regular_octagon_d8_cardinality(D, rho, sigma)
    $presentation_map_surjective(G, D, r, f, rho, sigma, phi)
    $surjective_fn(G, D, phi)
    $finite_surjective_map_bijective(G, D, r, f, rho, sigma, phi)
    $bijective_fn(G, D, phi)
    by def $group_isomorphism(G, D, phi)
    $group_isomorphism(G, D, phi)

    witness exist psi fn(x G) D st {$group_isomorphism(G, D, psi)} from phi:
        $group_isomorphism(G, D, phi)
    by def $isomorphic_group(G, D)
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "inline `trust` cannot have an indented body; use `trust:`", line: 156, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/drafts/dihedral_group_isomorphism_draft.lit") }))`.

### examples/_internal/drafts/finite_set_index_draft.lit

[examples/_internal/drafts/finite_set_index_draft.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/drafts/finite_set_index_draft.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `def_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

prop is_index_fn(S finite_set, index fn(x N+: x <= finite_set_size(S)) S):
    forall y S => exist i1 N+ st {i1 <= finite_set_size(S), y = index(i1)}

prop finite_set_size_has_index(n N+):
    forall s finite_set:
        $is_finite_set(s)
        finite_set_size(s) = n
        =>:
            exist idx fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx)}

forall A, B finite_set:
    $is_finite_set(intersect(A, B))
    =>:
        finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(intersect(A, B))
forall A finite_set:
    finite_set_size(A) = 0
    =>:
        A = {}

thm intersect_with_singleton:
    ? forall s set, a set:
        a $in s
        =>:
            intersect(s, {a}) = {a}
    by extension:
        ? intersect(s, {a}) = {a}
        forall z intersect(s, {a}):
            z $in s
            z $in {a}
            z = a
        forall z {a}:
            z = a
            a $in s
            z $in s
            z $in {a}

thm remove_singleton_from_singleton_sized_set_is_empty:
    ? forall s finite_set, a set:
        $is_finite_set(s)
        finite_set_size(s) = 1
        a $in s
        =>:
            set_minus(s, {a}) = {}
    release thm intersect_with_singleton(s, a)
    intersect(s, {a}) = {a}
    finite_set_size({a}) = 1
    $is_finite_set(set_minus(s, {a}))
    $is_finite_set(intersect(s, {a}))
    finite_set_size(intersect(s, {a})) = finite_set_size({a}) = 1
    finite_set_size(s) - finite_set_size(intersect(s, {a})) = finite_set_size(s) - 1
    finite_set_size(s) - 1 = 1 - 1
    finite_set_size(set_minus(s, {a})) = finite_set_size(s) - finite_set_size(intersect(s, {a})) = finite_set_size(s) - 1 = 1 - 1 = 0

thm index_function_for_singleton:
    ? forall s finite_set:
        $is_finite_set(s)
        finite_set_size(s) = 1
        =>:
            exist idx fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx)}
    finite_set_size(s) >= 1
    $is_nonempty_set(s)
    have a s
    a $in s
    release thm remove_singleton_from_singleton_sized_set_is_empty(s, a)
    set_minus(s, {a}) = {}
    have fn idx(i1 N+: i1 <= finite_set_size(s)) s = a
    witness exist idx0 fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx0)} from idx:
        claim:
            ? forall y s => exist i1 N+ st {i1 <= finite_set_size(s), y = idx0(i1)}
            by contra:
                ? y = a
                y != a
                not y $in {a}
                y $in set_minus(s, {a})
                witness $is_nonempty_set(set_minus(s, {a})) from y:
                    y $in set_minus(s, {a})
                impossible $is_nonempty_set(set_minus(s, {a}))
            idx0(1) = idx(1) = a
            witness exist i1 N+ st {i1 <= finite_set_size(s), y = idx0(i1)} from 1:
                1 <= finite_set_size(s)
                y = idx0(1)
        by def $is_index_fn(s, idx0)
        $is_index_fn(s, idx0)

thm index_function_step:
    ? forall n N+, s finite_set:
        $is_finite_set(s)
        finite_set_size(s) = n + 1
        $finite_set_size_has_index(n)
        =>:
            exist idx fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx)}
    n >= 1
    n + 1 >= 1
    finite_set_size(s) = n + 1 >= 1
    $is_nonempty_set(s)
    have a s
    a $in s
    release thm intersect_with_singleton(s, a)
    intersect(s, {a}) = {a}
    finite_set_size({a}) = 1
    $is_finite_set(set_minus(s, {a}))
    $is_finite_set(intersect(s, {a}))
    finite_set_size(intersect(s, {a})) = finite_set_size({a}) = 1
    finite_set_size(s) - finite_set_size(intersect(s, {a})) = finite_set_size(s) - 1
    finite_set_size(s) - 1 = (n + 1) - 1
    finite_set_size(set_minus(s, {a})) = finite_set_size(s) - finite_set_size(intersect(s, {a})) = finite_set_size(s) - 1 = (n + 1) - 1 = n
    $finite_set_size_has_index(n)
    $is_finite_set(set_minus(s, {a}))
    finite_set_size(set_minus(s, {a})) = n
    exist prev fn(x N+: x <= finite_set_size(set_minus(s, {a}))) set_minus(s, {a}) st {$is_index_fn(set_minus(s, {a}), prev)}
    obtain prev from exist prev fn(x N+: x <= finite_set_size(set_minus(s, {a}))) set_minus(s, {a}) st {$is_index_fn(set_minus(s, {a}), prev)}
    set_minus(s, {a}) $subset s
    have fn idx(i1 N+: i1 <= finite_set_size(s)) s by cases:
        case i1 <= n: prev(i1)
        case i1 > n: a
    idx(1) = prev(1)
    prev(1) $in set_minus(s, {a})
    prev(1) $in s
    idx(1) $in s
    witness exist idx0 fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx0)} from idx:
        claim:
            ? forall y s => exist i1 N+ st {i1 <= finite_set_size(s), y = idx0(i1)}
            y = a or y != a
            by cases:
                ? exist i1 N+ st {i1 <= finite_set_size(s), y = idx0(i1)}
                case y = a:
                    n + 1 <= finite_set_size(s)
                    idx0(n + 1) = idx(n + 1) = a
                    witness exist i1 N+ st {i1 <= finite_set_size(s), y = idx0(i1)} from n + 1:
                        n + 1 <= finite_set_size(s)
                        y = idx0(n + 1)
                case y != a:
                    not y $in {a}
                    y $in set_minus(s, {a})
                    exist i1 N+ st {i1 <= finite_set_size(set_minus(s, {a})), y = prev(i1)}
                    obtain j from exist i1 N+ st {i1 <= finite_set_size(set_minus(s, {a})), y = prev(i1)}
                    j <= finite_set_size(set_minus(s, {a}))
                    j <= n
                    n <= n + 1
                    j <= n <= n + 1 = finite_set_size(s)
                    idx0(j) = idx(j) = prev(j)
                    witness exist i1 N+ st {i1 <= finite_set_size(s), y = idx0(i1)} from j:
                        j <= finite_set_size(s)
                        y = idx0(j)
        by def $is_index_fn(s, idx0)
        $is_index_fn(s, idx0)

claim:
    ? forall n N+:
        $finite_set_size_has_index(n)
    by induc n from 1:
        ? $finite_set_size_has_index(n)

        ? from n = 1:
            claim:
                ? forall s finite_set:
                    $is_finite_set(s)
                    finite_set_size(s) = 1
                    =>:
                        exist idx fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx)}
                release thm index_function_for_singleton(s)
            by def $finite_set_size_has_index(1)
            $finite_set_size_has_index(1)
            $finite_set_size_has_index(n)

        ? induc:
            $finite_set_size_has_index(n)
            claim:
                ? forall s finite_set:
                    $is_finite_set(s)
                    finite_set_size(s) = n + 1
                    =>:
                        exist idx fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx)}
                release thm index_function_step(n, s)
            by def $finite_set_size_has_index(n + 1)
            $finite_set_size_has_index(n + 1)

claim:
    ? forall s finite_set:
        finite_set_size(s) >= 1
        =>:
            exist idx fn(x N+: x <= finite_set_size(s)) s st {$is_index_fn(s, idx)}
    finite_set_size(s) >= 1
    finite_set_size(s) $in N+
    have n N+ = finite_set_size(s)
    finite_set_size(s) = n
    $finite_set_size_has_index(n)
```

First failed statement: `thm`. Full nested requirements are in the linked raw JSON.

### examples/_internal/drafts/output_trace_showcase.lit

[examples/_internal/drafts/output_trace_showcase.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/drafts/output_trace_showcase.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
claim:
    ? forall x {y R: y > 0}:
        x = 1
        =>:
            x = 1
    x = x

claim:
    ? 1 = 1
    1 = 1

by cases:
    ? 1 = 1
    ? 2 = 2
    case 1 = 1
    case 1 != 1:
        impossible 1 = 1

by contra:
    ? 1 = 1
    impossible 1 != 1

thm tmp_one_eq_one:
    ? forall:
        1 = 1

release thm tmp_one_eq_one()

by enumerate finite_set:
    ? forall a {1, 2}:
        a < 3

by for:
    ? forall n range(0, 3):
        n < 3

claim:
    ? forall x range(1, 3):
        x = 1 or x = 2
    expand: x $in range(1, 3)

claim:
    ? forall y closed_range(1, 2):
        y = 1 or y = 2
    expand: y $in 1...2

by extension:
    ? {1} = {1}

abstract_prop tmp_induc_p(a)
trust $tmp_induc_p(0)
trust forall m Z:
    m >= 0
    $tmp_induc_p(m)
    =>:
        $tmp_induc_p(m + 1)
by induc n from 0:
    ? $tmp_induc_p(n)

    ? from n = 0:
        $tmp_induc_p(0)

    ? induc:
        $tmp_induc_p(n + 1)

prop tmp_same_obj(x set, y set):
    x = y

by reflexive_prop:
    ? forall x set:
        $tmp_same_obj(x, x)

by transitive_prop:
    ? forall x, y, z set:
        $tmp_same_obj(x, y)
        $tmp_same_obj(y, z)
        =>:
            $tmp_same_obj(x, z)

by symmetric_prop:
    ? forall x, y set:
        $tmp_same_obj(x, y)
        =>:
            $tmp_same_obj(y, x)


have tmp_index set
have tmp_factors nonempty_set
have tmp_family fn(tmp_coordinate tmp_index) tmp_factors
trust forall X tmp_factors:
    $is_nonempty_set(X)
release thm index_cart_nonempty_by_choice_from_family(index_cart(tmp_index, tmp_factors, tmp_family))
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "inline `trust` cannot have an indented body; use `trust:`", line: 66, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/drafts/output_trace_showcase.lit") }))`.

### examples/_internal/fixtures/geometry_foundation/main.lit

[examples/_internal/fixtures/geometry_foundation/main.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/fixtures/geometry_foundation/main.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
have a R = 1
have pair cart(R, R) = (3, 4)
have ProductSet set = cart(R, R)
```

Configuration: [examples/_internal/fixtures/geometry_foundation/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/fixtures/geometry_foundation/litex.config)

```toml
[hierarchy]
module

[export]
main = "main.lit"
main2 = "main2.lit"
```

### examples/_internal/fixtures/geometry_foundation/main2.lit

[examples/_internal/fixtures/geometry_foundation/main2.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/fixtures/geometry_foundation/main2.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `launch_config`; process exit: `2`.

<!-- litex:skip-test -->
```litex
have b R = 2
have pair cart(R, R) = (8, 9)
```

Configuration: [examples/_internal/fixtures/geometry_foundation/litex.config](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/fixtures/geometry_foundation/litex.config)

```toml
[hierarchy]
module

[export]
main = "main.lit"
main2 = "main2.lit"
```

### examples/_internal/regression/by_thm_anonymous_function_body_equality.lit

[examples/_internal/regression/by_thm_anonymous_function_body_equality.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/by_thm_anonymous_function_body_equality.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
abstract_prop is_probe_integrable(f)
trust have probe_integral fn(f fn(x R) R) R

thm direct_anonymous_function_body_equality:
    ? forall g fn(x R) R:
        fn(x R) R {-1 * 1 * g(x)} = fn(x R) R {-1 * g(x)}
    by def $fn_eq(fn(x R) R {-1 * 1 * g(x)}, fn(x R) R {-1 * g(x)})

thm probe_scalar_multiplication:
    ? forall f fn(x R) R, c R:
        $is_probe_integrable(f)
        =>:
            $is_probe_integrable(fn(x R) R {c * f(x)})
            probe_integral(fn(x R) R {c * f(x)}) = c * probe_integral(f)
    trust:
        $is_probe_integrable(fn(x R) R {c * f(x)})
        probe_integral(fn(x R) R {c * f(x)}) = c * probe_integral(f)

thm probe_addition:
    ? forall f, g fn(x R) R:
        $is_probe_integrable(f)
        $is_probe_integrable(g)
        =>:
            $is_probe_integrable(fn(x R) R {f(x) + g(x)})
            probe_integral(fn(x R) R {f(x) + g(x)}) = probe_integral(f) + probe_integral(g)
    trust:
        $is_probe_integrable(fn(x R) R {f(x) + g(x)})
        probe_integral(fn(x R) R {f(x) + g(x)}) = probe_integral(f) + probe_integral(g)

thm probe_subtraction:
    ? forall f, g fn(x R) R:
        $is_probe_integrable(f)
        $is_probe_integrable(g)
        =>:
            probe_integral(fn(x R) R {f(x) - g(x)}) = probe_integral(f) - probe_integral(g)
    release thm probe_scalar_multiplication(g, -1)
    $is_probe_integrable(fn(x R) R {-1 * g(x)})
    probe_integral(fn(x R) R {-1 * g(x)}) = -1 * probe_integral(g)
    release thm fn_set_member(fn(x R) R {-1 * g(x)}, fn(x R) R)
    release thm probe_addition(f, fn(x R) R {-1 * g(x)})
    $is_probe_integrable(fn(x R) R {f(x) + (-1 * g(x))})
    probe_integral(fn(x R) R {f(x) + (-1 * g(x))}) = probe_integral(f) + probe_integral(fn(x R) R {-1 * g(x)})
    trust:
        probe_integral(fn(x R) R {f(x) - g(x)}) = probe_integral(f) - probe_integral(g)
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "`$fn_eq` is removed; use ordinary equality `f = g` or `by fn_extension` / `forall` for pointwise agreement", line: 10, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/by_thm_anonymous_function_body_equality.lit") }))`.

### examples/_internal/regression/empty_integer_interval_is_empty.lit

[examples/_internal/regression/empty_integer_interval_is_empty.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/empty_integer_interval_is_empty.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `def_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
thm empty_half_open_integer_interval_is_empty:
    ? forall:
        not $is_nonempty_set(range(0, 0))
        range(0, 0) = {}
    by contra:
        ? not $is_nonempty_set(range(0, 0))
        $is_nonempty_set(range(0, 0))
        have x range(0, 0)
        impossible x < 0
    range(0, 0) = {}

thm reversed_symbolic_closed_integer_interval_is_empty:
    ? forall a, b Z:
        b < a
        =>:
            not $is_nonempty_set(closed_range(a, b))
            closed_range(a, b) = {}
    not $is_nonempty_set(closed_range(a, b))
    closed_range(a, b) = {}

range(3, 2) = {}
closed_range(3, 2) = {}
finite_set_size(range(3, 2)) = 0
finite_set_size(closed_range(3, 2)) = 0

forall i1 range(3, 2):
    1 = 0

forall i1 closed_range(3, 2):
    1 = 0

by for:
    ? forall i1 range(3, 2) => 1 = 0
by for:
    ? forall i1 closed_range(3, 2) => 1 = 0

have fn empty_to_empty(x {}) {} = x

forall x {}:
    x $in N
```

First failed statement: `thm`. Full nested requirements are in the linked raw JSON.

### examples/_internal/regression/finite_set_induction.lit

[examples/_internal/regression/finite_set_induction.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/finite_set_induction.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
"""
Finite-set induction has an explicit empty case and a fresh-element insertion
case. It stores the resulting universal fact over `finite_set`.
"""

abstract_prop finite_set_induction_regression(P)

trust $finite_set_induction_regression({})

trust:
    forall x set, S finite_set:
        not x $in S
        $finite_set_induction_regression(S)
        =>:
            $finite_set_induction_regression(union({x}, S))

by induc P:
    ? $finite_set_induction_regression(P)
    ? from P = {}:
        $finite_set_induction_regression({})
    ? induc x, S:
        $finite_set_induction_regression(S)
        $finite_set_induction_regression(union({x}, S))

$finite_set_induction_regression({1, 2})
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "by induc: finite-set induction was removed; use `by induc <param> from <base>:`", line: 18, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/finite_set_induction.lit") }))`.

### examples/_internal/regression/fn_eq_implies_equality.lit

[examples/_internal/regression/fn_eq_implies_equality.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/fn_eq_implies_equality.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
thm fn_eq_implies_equality_regression:
    ? forall f, g fn(n N) N:
        forall n N:
            f(n) = g(n)
        =>:
            $fn_eq(f, g)
            f = g
            power_set(f) = power_set(g)
    by def $fn_eq(f, g)
    $fn_eq(f, g)
    f = g
    power_set(f) = power_set(g)
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "`$fn_eq` is removed; use ordinary equality `f = g` or `by fn_extension` / `forall` for pointwise agreement", line: 6, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/fn_eq_implies_equality.lit") }))`.

### examples/_internal/regression/gcd_from_finite_divisors.lit

[examples/_internal/regression/gcd_from_finite_divisors.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/gcd_from_finite_divisors.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `def_thm`; process exit: `1`.

<!-- litex:skip-test -->
```litex
thm positive_divisor_le_abs:
    ? forall d N+, a Z:
        $dvd(a, d)
        a != 0
        =>:
            d <= abs(a)
    obtain k from exist k Z st {a = d * k}
    by contra:
        ? k != 0
        k = 0
        a = d * k = d * 0 = 0
        impossible a != 0
    abs(k) > 0
    abs(k) $in N+
    d * 1 <= d * abs(k)
    abs(d) = d
    abs(a) = abs(d * k) = abs(d) * abs(k) = d * abs(k)
    d = d * 1 <= d * abs(k) = abs(a)

thm common_divisor_set_is_finite_and_nonempty:
    ? forall a, b Z:
        a != 0 or b != 0
        =>:
            $is_finite_set({d N+: $dvd(a, d), $dvd(b, d)})
            $is_nonempty_set({d N+: $dvd(a, d), $dvd(b, d)})
    have c power_set(N) = {d N+: $dvd(a, d), $dvd(b, d)}
    claim:
        ? $is_finite_set(c)
        by cases:
            ? $is_finite_set(c)
            case a != 0:
                claim:
                    ? forall d c:
                        d $in closed_range(1, abs(a))
                    d $in c
                    d $in N+
                    d >= 1
                    $dvd(a, d)
                    release thm positive_divisor_le_abs(d, a)
                by def c $subset closed_range(1, abs(a))
                release thm subset_of_finite_set_is_finite(c, closed_range(1, abs(a)))
            case b != 0:
                claim:
                    ? forall d c:
                        d $in closed_range(1, abs(b))
                    d $in c
                    d $in N+
                    d >= 1
                    $dvd(b, d)
                    release thm positive_divisor_le_abs(d, b)
                by def c $subset closed_range(1, abs(b))
                release thm subset_of_finite_set_is_finite(c, closed_range(1, abs(b)))
    witness $is_nonempty_set(c) from 1:
        1 $in N+
        witness exist k Z st {a = 1 * k} from a:
            a = 1 * a
        by def $dvd(a, 1)
        witness exist k Z st {b = 1 * k} from b:
            b = 1 * b
        by def $dvd(b, 1)
        release thm set_builder_member(1, {d N+: $dvd(a, d), $dvd(b, d)})
        1 $in c
    $is_finite_set({d N+: $dvd(a, d), $dvd(b, d)})
    $is_nonempty_set({d N+: $dvd(a, d), $dvd(b, d)})

have fn gcd_from_finite_divisors(a, b Z: a != 0 or b != 0) N = finite_set_max({d N+: $dvd(a, d), $dvd(b, d)})

thm gcd_from_finite_divisors_eq_native:
    ? forall a, b Z:
        a != 0 or b != 0
        =>:
            gcd_from_finite_divisors(a, b) = gcd(a, b)
    release thm common_divisor_set_is_finite_and_nonempty(a, b)
    gcd_from_finite_divisors(a, b) = finite_set_max({d N+: $dvd(a, d), $dvd(b, d)})
    finite_set_max({d N+: $dvd(a, d), $dvd(b, d)}) $in {d N+: $dvd(a, d), $dvd(b, d)}
    gcd_from_finite_divisors(a, b) $in {d N+: $dvd(a, d), $dvd(b, d)}
    $dvd(a, gcd_from_finite_divisors(a, b))
    $dvd(b, gcd_from_finite_divisors(a, b))
    obtain ka from exist k Z st {a = gcd_from_finite_divisors(a, b) * k}
    obtain kb from exist k Z st {b = gcd_from_finite_divisors(a, b) * k}
    a % gcd_from_finite_divisors(a, b) = (gcd_from_finite_divisors(a, b) * ka) % gcd_from_finite_divisors(a, b) = 0
    b % gcd_from_finite_divisors(a, b) = (gcd_from_finite_divisors(a, b) * kb) % gcd_from_finite_divisors(a, b) = 0
    gcd_from_finite_divisors(a, b) <= gcd(a, b)
    gcd(a, b) $in N+
    a % gcd(a, b) = 0
    b % gcd(a, b) = 0
    by def $dvd(a, gcd(a, b))
    by def $dvd(b, gcd(a, b))
    release thm set_builder_member(gcd(a, b), {d N+: $dvd(a, d), $dvd(b, d)})
    gcd(a, b) <= finite_set_max({d N+: $dvd(a, d), $dvd(b, d)})
    gcd(a, b) <= gcd_from_finite_divisors(a, b)
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `gcd_from_finite_divisors`", line: 75, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/gcd_from_finite_divisors.lit") }))`.

First failed statement: `thm`. Full nested requirements are in the linked raw JSON.

### examples/_internal/regression/generic_cart_member_coordinates.lit

[examples/_internal/regression/generic_cart_member_coordinates.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/generic_cart_member_coordinates.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
have n N+ = 3

forall p c:
    tuple_dim(p) = n

forall p c, i1 closed_range(1, n):
    p[i1] $in proj(c, i1)

claim:
    ? forall p c:
        p[1] $in proj(c, 1)
        proj(c, 1) = R
        p[1] $in R
        p[2] $in proj(c, 2)
        proj(c, 2) = R
        p[2] $in R
        p[3] $in proj(c, 3)
        proj(c, 3) = R
        p[3] $in R
    1 $in closed_range(1, n)
    p[1] $in proj(c, 1)
    proj(c, 1) = R
    p[1] $in R
    2 $in closed_range(1, n)
    p[2] $in proj(c, 2)
    proj(c, 2) = R
    p[2] $in R
    3 $in closed_range(1, n)
    p[3] $in proj(c, 3)
    proj(c, 3) = R
    p[3] $in R

tuple_dim(q) = n

forall i1 closed_range(1, n):
    q[i1] = 0
    0 $in R
    proj(c, i1) = R
    q[i1] $in proj(c, i1)

release thm cart_member_from_coordinates(q, c)
q $in c


forall i1 closed_range(1, n):
    q[i1] = 0
    r[i1] = 0
    q[i1] = r[i1]

release thm tuple_equal_from_coordinates(q, r)
q = r

have fn X(i1 closed_range(1, n)) power_set(R) = R
prop has_X_values(f fn(i1 closed_range(1, n)) R):
    forall j closed_range(1, n):
        f(j) $in X(j)
prop has_values_in_family(m N+, V set, Y fn(i1 closed_range(1, m)) power_set(V), g fn(i1 closed_range(1, m)) V):
    forall i1 closed_range(1, m):
        g(i1) $in Y(i1)
have P set = {f fn(i1 closed_range(1, n)) R: $has_X_values(f)}
have fn raw_choice_tuple_encode(p c) fn(i1 closed_range(1, n)) R = fn(j closed_range(1, n)) R {p[j]}

claim:
    ? forall p c:
        raw_choice_tuple_encode(p) $in P
    claim:
        ? forall i1 closed_range(1, n):
            raw_choice_tuple_encode(p)(i1) $in X(i1)
        fn(j closed_range(1, n)) R {p[j]}(i1) = p[i1]
        raw_choice_tuple_encode(p)(i1) = p[i1]
        p[i1] $in proj(c, i1)
        proj(c, i1) = R = X(i1)
        p[i1] $in X(i1)
    by def $has_X_values(raw_choice_tuple_encode(p))
    $has_X_values(raw_choice_tuple_encode(p))
    release thm set_builder_member(raw_choice_tuple_encode(p), {f fn(i1 closed_range(1, n)) R: $has_X_values(f)})
    raw_choice_tuple_encode(p) $in {f fn(i1 closed_range(1, n)) R: $has_X_values(f)}

have fn choice_tuple_encode(p c) P = raw_choice_tuple_encode(p)

claim:
    ? forall m N+:
        2 <= m
        =>:
            m = m
    1 <= m
    tuple_dim(symbolic_tuple) = m

claim:
    ? forall m N+, V set, Y fn(i1 closed_range(1, m)) power_set(V), S set:
        2 <= m
        S = {g fn(i1 closed_range(1, m)) V: $has_values_in_family(m, V, Y, g)}
        =>:
            S = S
    1 <= m
    claim:
        ? forall g S:
            g = g
        g $in {h fn(i1 closed_range(1, m)) V: $has_values_in_family(m, V, Y, h)}
        tuple_dim(tuple_from_member) = m
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "undefined name `c`", line: 10, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/generic_cart_member_coordinates.lit") }))`.

### examples/_internal/regression/iterated_scalar_return_set_validation.lit

[examples/_internal/regression/iterated_scalar_return_set_validation.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/iterated_scalar_return_set_validation.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
sum(1, 2, fn(k Z) Z {k}) = sum(1, 2, fn(k Z) Z {k})
product(1, 2, fn(k Z) Z {k}) = product(1, 2, fn(k Z) Z {k})
finite_set_sum({1, 2}, fn(k {1, 2}) Z {k}) = finite_set_sum({1, 2}, fn(k {1, 2}) Z {k})
finite_set_product({1, 2}, fn(k {1, 2}) Z {k}) = finite_set_product({1, 2}, fn(k {1, 2}) Z {k})
finite_set_sum(3...1, fn(k Z) Z {0}) = 0
finite_set_product(3...1, fn(k Z) Z {1}) = 1
```

First failed statement: `finite_set_sum(closed_range(3, 1), fn (k Z) Z{0}) = 0`. Full nested requirements are in the linked raw JSON.

### examples/_internal/regression/lambda_alpha_equivalence.lit

[examples/_internal/regression/lambda_alpha_equivalence.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/lambda_alpha_equivalence.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
abstract_prop alpha_assumption(f)
abstract_prop alpha_conclusion(f)

trust $alpha_assumption(fn(k R) R {k})
$alpha_assumption(fn(i1 R) R {i1})

thm alpha_theorem:
    ? forall a R:
        $alpha_assumption(fn(k R) R {k + a})
        =>:
            $alpha_conclusion(fn(k R) R {k + a})
    trust $alpha_conclusion(fn(k R) R {k + a})

claim:
    ? forall a R:
        $alpha_assumption(fn(k R) R {k + a})
        =>:
            $alpha_conclusion(fn(k R) R {k + a})
    trust $alpha_conclusion(fn(k R) R {k + a})

trust $alpha_assumption(fn(i1 R) R {i1 + 1})
$alpha_conclusion(fn(i1 R) R {i1 + 1})
release thm alpha_theorem(1)
$alpha_conclusion(fn(j R) R {j + 1})
```

First failed statement: `$alpha_conclusion(fn (i1 R) R{i1 + 1})`. Full nested requirements are in the linked raw JSON.

### examples/_internal/regression/named_restricted_return_set.lit

[examples/_internal/regression/named_restricted_return_set.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/named_restricted_return_set.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
thm named_restricted_return_set_supports_nested_function_use:
    ? forall U set, u U, P set:
        P = {f fn(i1 closed_range(1, 2)) U: f(1) = u and f(2) = u}
        =>:
            exist h fn(p {u}) P st {$fn_eq(h(u), fn(i1 closed_range(1, 2)) U {u})}
    P = {f fn(i1 closed_range(1, 2)) U: f(1) = u and f(2) = u}
    release thm fn_set_member(fn(i1 closed_range(1, 2)) U {u}, fn(i1 closed_range(1, 2)) U)
    release thm set_builder_member(fn(i1 closed_range(1, 2)) U {u}, {f fn(i1 closed_range(1, 2)) U: f(1) = u and f(2) = u})
    have fn encode(p {u}) P = fn(i1 closed_range(1, 2)) U {u}
    encode(u)(1) = u
    forall i1 closed_range(1, 2):
        encode(u)(i1) = fn(j closed_range(1, 2)) U {u}(i1)
    encode(u) $in P
    encode(u) $in fn(i1 closed_range(1, 2)) U
    by def $fn_eq(encode(u), fn(i1 closed_range(1, 2)) U {u})
    $fn_eq(encode(u), fn(i1 closed_range(1, 2)) U {u})
    witness exist h fn(p {u}) P st {$fn_eq(h(u), fn(i1 closed_range(1, 2)) U {u})} from encode:
        $fn_eq(encode(u), fn(i1 closed_range(1, 2)) U {u})
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "`$fn_eq` is removed; use ordinary equality `f = g` or `by fn_extension` / `forall` for pointwise agreement", line: 5, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/named_restricted_return_set.lit") }))`.

### examples/_internal/regression/numeric_power_rules.lit

[examples/_internal/regression/numeric_power_rules.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/numeric_power_rules.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
forall a, b N, n N+:
    a < b
    =>:
        a^n < b^n

forall a, b, n N:
    n >= 1
    a < b
    =>:
        a^n < b^n

forall a, b, n N+:
    a < b
    =>:
        a^n < b^n

forall x, y Q, n N+:
    x > y
    y >= 0
    =>:
        x^n > y^n

forall x Q*, n Z:
    x^n != 0

forall x Q*, n N+:
    x^n != 0
    =>:
        x^(-n) = 1 / x^n

forall x, y Q*, n Z:
    (x * y)^n = x^n * y^n

forall x, y Q+, n Z:
    x >= y
    n < 0
    =>:
        x^n <= y^n

forall x, y Q+, n Z:
    n != 0
    x^n = y^n
    =>:
        x = y

forall x Q*, n Z:
    x $in R
    abs(x^n) = abs(x)^n

forall a, b R:
    a * b = 0
    a != 0
    =>:
        b = 0

forall a, b, c R*:
    a / (b / c) = a * c / b
    (a / b) / c = a / (b * c)

forall u, v, w R:
    w != 0
    u = v / w
    =>:
        u * w = v

forall u, v, w R:
    w != 0
    u * w = v
    =>:
        u = v / w

forall x R:
    x + x = 2 * x

forall a R:
    a * a = a^2

forall x, y R:
    x + x + y = 2 * x + y

forall a, b R:
    a * a * b = a^2 * b

forall x, c R:
    x != c
    =>:
        x - c != 0

forall x, c R:
    x - c != 0
    =>:
        x != c

forall x, c R:
    =>:
        x != c
    <=>:
        x - c != 0

forall x, c R:
    x != -c
    =>:
        x + c != 0

forall x, c R:
    x + c != 0
    =>:
        x != -c

forall x, c R:
    =>:
        x != -c
    <=>:
        x + c != 0
```

First failed statement: `forall a, b, n N:
    n >= 1
    a < b
    =>:
        a ^ n < b ^ n`. Full nested requirements are in the linked raw JSON.

### examples/_internal/regression/operator_self_equality.lit

[examples/_internal/regression/operator_self_equality.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/operator_self_equality.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `parse`; process exit: `1`.

<!-- litex:skip-test -->
```litex
+ = +
```

Session error: `Runtime(ParseError(RuntimeParseError { message: "expected object, got `+`", line: 1, path: Real("/Users/shenjiachen/主要文件夹/GeekGems/litex/golitex/tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/operator_self_equality.lit") }))`.

### examples/_internal/regression/vector_space_scalar_system.lit

[examples/_internal/regression/vector_space_scalar_system.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/_internal/regression/vector_space_scalar_system.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `def_struct`; process exit: `1`.

<!-- litex:skip-test -->
```litex
struct ScalarSystem<s nonempty_set>:
    zero s
    one s
    add fn(x, y s) s
    mul fn(x, y s) s

struct VectorSpace<s nonempty_set, v nonempty_set>:
    scalars &ScalarSystem<s>
    zero v
    add fn(x, y v) v
    smul fn(a s, x v) v
    <=>:
        forall a, b s, x v:
            smul(scalars.mul(a, b), x) = smul(a, smul(b, x))
```

First failed statement: `struct …`. Full nested requirements are in the linked raw JSON.

### examples/tmp_inverse_trig.lit

[examples/tmp_inverse_trig.lit](../../tmp/2026-10-02/examples-migration-rescan/latest-snapshot/examples/tmp_inverse_trig.lit)

Expected: **accept**; observed: **reject**; earliest reported phase: `search_proof`; process exit: `1`.

<!-- litex:skip-test -->
```litex
arcsin(0) = 0
arcsin(1) = pi / 2
arcsin(-1) = -pi / 2
arccos(1) = 0
arccos(0) = pi / 2
arccos(-1) = pi
arctan(0) = 0
arccot(0) = pi / 2

forall x R:
    (-1) <= x
    x <= 1
    =>:
        arcsin(x) $in R
        arccos(x) $in R
        sin(arcsin(x)) = x
        cos(arccos(x)) = x
        -pi / 2 <= arcsin(x) <= pi / 2
        0 <= arccos(x) <= pi

forall x R:
    arctan(x) $in R
    arccot(x) $in R
    tan(arctan(x)) = x
    cot(arccot(x)) = x
    -pi / 2 < arctan(x) < pi / 2
    0 < arccot(x) < pi

forall y R:
    -pi / 2 <= y
    y <= pi / 2
    =>:
        arcsin(sin(y)) = y

forall y R:
    0 <= y
    y <= pi
    =>:
        arccos(cos(y)) = y

forall y R:
    -pi / 2 < y
    y < pi / 2
    =>:
        arctan(tan(y)) = y

forall y R:
    0 < y
    y < pi
    =>:
        arccot(cot(y)) = y
```

First failed statement: `forall x R:
    -1 <= x
    x <= 1
    =>:
        arcsin(x) $in R
        arccos(x) $in R
        sin(arcsin(x)) = x
        cos(arccos(x)) = x
        -pi / 2 <= arcsin(x) <= pi / 2
        0 <= arccos(x) <= pi`. Full nested requirements are in the linked raw JSON.
