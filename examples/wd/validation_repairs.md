# WD validation repair experience

The user authorized local WD repairs while preserving the total execution
Pipeline. The source-owned evidence is
validation_repairs.json (historical task record; retired).

## Checked domains must guard later WD

The independent WD owners for `not forall` and `forall … <=>:` checked domain
facts but did not stage them. These definitions therefore rejected `1 / y`:

```litex
prop guarded_counterexample(x R):
    not forall y R:
        y != 0
        =>:
            1 / y != 1 / y
```

```litex
prop guarded_equivalence(x R):
    forall y R:
        y != 0
        =>:
            1 / y = 1 / y
        <=>:
            y = y
```

After a domain passes its own WD check, the existing `store_fact_and_infer`
API stages it in the existing retained binder environment. Later domains and
conclusions can use it. Neither iff branch is staged as an assumption for the
other branch. No parameters, assumptions or successful WD cache records leak
into the parent. Independent WD still does not prove the proposition.

The active [acceptance file](fact/guarded_quantifier_domains.lit) includes the
original failure as comments and the unchanged active definitions and claim.
Executable negative controls reject missing guards, literal zero denominators,
and iff cross-branch assumptions. Rust regressions also check reversed guards,
rollback, name reuse, retained stages and parent-scope isolation.

## Returned evidence needs a live owner

```litex
have fn choose(a, b R) R = a
let value = choose(1 + 1, 1 + 1)
```

This executed successfully but returned `ByKnown { wd_id: wd8, … }` for the
second composite argument after dropping the signature-candidate environment
that owned `wd8`. Candidate checking now uses the caller's existing
`without_well_defined_storage()` state. It returns full child/requirement proofs
or cites ancestor-owned ids; the selected successful application still records
its own WD in the caller according to the original state. Failed candidates
remain isolated. Literal function binders legitimately retain their own local
environment and may cite ids owned there.

The [application acceptance file](obj/application_evidence_ownership.lit) and
`tests/unit/execute/function_application_wd_evidence/tests.rs` cover named,
literal, cached and field calls. The tests resolve direct and recursively
projected WD ids after the statement finishes, accounting for retained binder
environments. The initial field fixture incorrectly requested `have pair &Pair`
without proving nonemptiness; it was replaced with a real binder in `prop` /
`forall`, preserving the actual field domain instead of adding trust.

## A failed definition must retain its cause

```litex
prop broken(x R):
    1 / 0 = x
```

The runtime rejected this correctly, but Detailed output collapsed it to
`{"success": false, "kind": "def_prop"}`. Both profiles now project the
existing parameter, struct-opening or body-WD failure enum exhaustively.
Normal puts the cause in `why_failed.failure`; Detailed puts it in `failure`.
The nested cause retains the actual `0 != 0` obligation. English and Chinese
producer/consumer tests also check that failed definitions store nothing and
can be redefined successfully afterwards.

## Verification and attribution boundaries

All statements enter through `Runtime::exec_stmt`; nested work uses the
existing verify/store interfaces. WD → proof → success-only storage, failure
rollback, the distinction between Failed and SessionError, result stage order,
and retained evidence scopes are unchanged. No AST or Env/Runtime fields or
ownership contracts were changed; no trust, stack-limit or global search-policy
change was introduced.

The original imported same-name induction test and all four valid/invalid
function/algo cases recovered on concurrent source before this task's candidate
cache repair. This task verifies that recovery and does not attribute an
induction repair to itself. A concurrent scalar identity addition created an
infinite-sized proof enum cycle; the existing premise was boxed to restore
compilation without changing the rule.

A broader focused Pipeline checkpoint initially had two existing failures in
prime-definition inference, also present before the candidate repair. The
reduced failure was a divisor `d range(2, p)` whose `p % d` WD could not prove
`d != 0`. Current concurrent source added checked signed-bound nonzero evidence.
The journal records the initial failure and the final gate separately; only
passing gates establish closure.

That restoration exposed a stale `by def $prime(5)` regression expectation.
In a fresh environment the explicit proof still fails; after a computed prime
stores its checked definition consequences, the trial forall is available and
the explicit proof succeeds through `by_definition`. The updated test checks
both states and the actual range evidence.

The expanded gate also exposed the choice fixture's conclusion-search miss.
Both the goal and the conclusion had successful WD. Known-exist reuse replaced
only outer binder names in an IR string, so the generated and written identity
functions `fn(A F) F {A}` / `fn(B F) F {B}` failed the final exact comparison.
That one reuse branch now calls the existing structural alpha comparator with
the existential's typed binder map. This changes no index, storage or global
search policy. Carriers are checked before binding each group; parameter kinds,
body predicates, complete nested bodies and free owners stay exact. The
[nested-binder acceptance file](../proof_nodes/exist/by_known/nested_binder_alpha.lit)
and `tests/unit/execute/known_exist_nested_binders/tests.rs` verify rename reuse
and reject changed bodies, carriers, kinds and captured owners.

Use release builds. Focused families: `wd_`, `predicate_signature_tests`,
`declaration_binding_tests`, `exec_stmt_transaction_tests`, `json_output::` and
`induction_repair_tests` and `known_exist_nested_binder_tests`. Binary hashes and exact selected tests are recorded
in the journal. Whole-repository and Lean gates are outside this local change.

## Final acceptance

`cargo build --release` completed successfully. The frozen focused release
executable passed **262 tests**, with no failures or ignored selected tests.
The separately frozen final release CLI met **21/21** positive/negative
expectations, including the unchanged choice fixture and four imported
same-name induction variants. Missing guards and invalid return/struct domains
remain rejected. Exact test names, code/config inputs, outputs and binary
hashes are retained in the source-owned journal.
