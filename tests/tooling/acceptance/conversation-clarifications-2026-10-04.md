# Conversation clarification and bounded repair — 2026-10-04

Task: follow up the maintainer's six-item reply with concrete inputs, implement
authorized local repairs and withdraw unnecessary semantic decisions. Scope:
strict cache handling, induction/struct clarification, original geometry proof,
and affected test consumers. No AST/state/cache-format fields changed.

## Current result

The final release build succeeds. Frozen CLI SHA-256:
`cebcd18987723bca656be8143137ff690413f7d89735f3999e197838a0c46270`.
Final build and test captures have zero source drift within their recorded
scope. Build and Rust tests used the same `src/**/*.rs` snapshot.

| Gate | Actual result |
| --- | --- |
| Rust lib, all-targets | 829 passed / 1 failed / 830 total; exit 101 |
| Integration | 1 passed / 0 failed |
| Module tests included in lib | 26 passed / 0 failed |
| Stmt manifest | 50 leaves / 378 checks / 0 mismatches / 0 gaps |
| Basic semantic manifest | 175 passed / 0 failed |
| Clarification controls | 22 expected outcomes matched, including negatives |

The only failed Rust assertion is
`execute::showcase_local_repair_tests::unique_function_templates_recover_hidden_carriers_and_work_in_nested_wd`.
It is retained pending the concrete unused-K question below. Counts are scoped;
prior phase 871, formal docs 225 and tooling 18 belong to the earlier frozen
[retest](conversation-closeout-retest-2026-10-04.md), not this binary's full
release gate. Complete collectors remain REL02/REL04 testing work.

## Strict contains no user trust

The maintainer confirmed this behavior in the six-item reply. The earlier
concrete guard is applied in `try_finish_import_from_kb`: strict returns the
existing Miss and verifies dependency source. It adds five lines and changes
no cache shape. Strict imports now recheck source even if ordinary mode has
created a cache; ordinary mode retains actual cache hits.

```litex
# dependency
thm false_theorem:
    ? 0 = 1
    trust 0 = 1
# root
release thm Dep::main::false_theorem
0 = 1
```

Fresh-copy cold strict / ordinary warmup / warm strict produce exits `1,0,1`
and JSON successes `false,true,false`. Direct and transitive false-theorem
Rust regressions reject; a valid imported identity passes, ordinary warm
execution actually skips its source, strict warm execution rechecks it.
Error-forwarding controls continue passing. The original negative assertions
were not weakened. Test cases that require actual cache hits now use ordinary
mode; other strict controls remain strict.

## n is an induction binder; original input passes

```litex
have fn f(x N) N = x
by induc n from 0:
    ? f(n) = f(n)
```

Bare ordinary and strong induction pass. The binder ranges over integers at
least the starting value. A concurrent task implemented checked lower-bound
integer-to-N inference; this task verified it and does not claim authorship.
Explicit `n $in N` also passes. Start -1 with the same N-valued function and
`n/n=1` from zero reject. The earlier automatic-carrier decision is closed.

## The unused struct parameter needs a concrete intent

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
by extension:
    ? &Point<N,R> = &Point<Z,R>
```

K is unused: both instances currently describe real/natural pairs. Membership
and the explicit extension equality pass; bare equality and inequality searches
reject. The question is whether the original test intended `tag K`, or unused
K must still distinguish the instances. The maintainer's unclear reply is not
treated as authorization to change representation. Blocking only membership
would leave the literal tuple and extension definitions inconsistent with the
desired distinction. No such partial patch was applied. Wrong objects and
missing guards remain rejected; the old wrong-carrier assertion stays red.

## Nested contra is the earlier known feature limit

```litex
by contra:
    ? forall x {0}:
        exist y {0} st {y = x}
    impossible 0 = 0
```

This rejects at `negation_unsupported`: the reverse assumption needs
∃x∈{0}, ∀y∈{0}, y≠x, which current QF-only NotForall/PlainExist payloads cannot
store. It is the nested case already anticipated by the maintainer, not a
new bug or another request for unified NotFact. Existing compound closing
support remains implemented. No shape change was made here.

## Explicit release closes the original geometry case

```litex
release obj def geo::vec
release obj def geo::dot
release obj def geo::det
release obj def geo::distance_sq
```

The original problem_927 SSS theorem, assumptions and proof are unchanged.
Both original `-strict -f solution.lit` and `-strict -r problem_927` pass.
Qualified distance reflexivity passes after release; wrong numeric carriers
and `0=1` reject. No trust or module-owner lookup redesign was necessary.
The earlier nonlocal signature/evidence proposal for this case is withdrawn.
Historical InternalBug output remains in the earlier receipt.

## Other bounded consumer repairs and test-engineering ownership

The declaration-binding cache test now copies its five real fixture files to
an owned temporary module; strict source verification and ordinary actual
cache-hit assertions both remain. The dimension consumer uses
`have A set = cart(R,R)` instead of trusted shape evidence. Exact dimension 2
passes; wrong dimensions 0/1, unknown shape and non-tuple inputs reject.
This checks semantic boundaries instead of an obsolete route label.

The sixth earlier item was test-engineering work: an old Cargo filter can
select zero tests, and audit documents intentionally retain failed or incomplete
snippets. Codex owns collector/context/expectation maintenance. The maintainer
need not select a manifest framework. This turn does not claim those complete
collectors were restored or the whole release gate passed.

## Evidence and reproducibility

[Structured commands, scope, attempts and identities](conversation-clarifications-2026-10-04.json).
The sibling ignored `conversation-clarifications-2026-10-04_receipts.zip` holds
raw stdout/stderr, full capture fingerprints, exact probe inputs/modules,
frozen binaries/harness, compiled source snapshot and changed source copies.
Its checksum is in the JSON receipt. Earlier drifting runs and the invalid
basic-runner attempt that omitted `--manifest` remain as failed attempts.

Current CLI does not implement the historical skill `-compact/-before/-runner`
or `try` protocol. Tests use current `-strict/-f/-r/-e` and check actual JSON
success against process exit. All final commands and argument arrays are saved.
Captures cover their named directories, not every repository file; external
concurrent changes were preserved. The earlier canonical cache test rewrote
a pre-existing declaration-binding manifest, so that test now uses a copy.

SOP: `todo/2026-10-4/conversation-clarifications.md`, archived at handoff;
only task-owned `tmp/2026-10-04/conversation-clarifications/` is cleaned.
Current source-owned routes: strict_cache_policy, ByInducStmt, DefStructStmt,
ByContraStmt, problem_927 and tooling; canonical REL02/04, OBJ10, LEG29,
DEC01/04 are synchronized.
