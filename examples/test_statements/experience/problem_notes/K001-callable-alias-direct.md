# K001: Function aliases use stored facts

Status: resolved on 2026-10-02.

## Task context

- Task: user-requested redesign of `special_object_properties_by_def` into a fact-based `SpecialProperty` index, and repair of K001.
- Scope: object capability indexing, named function application WD/body unfolding, and proof citations.
- Related workspace: golitex statement regression suite.

## Before and now

```litex
# Before: the last assertion failed in search_proof (exit 1, success false).
# have fn f(x R) R = x + 1
# let g = f
# g(4) = 5

have fn f(x R) R = x + 1
let g = f
g(4) = 5
```

The unchanged [original reproduction](../../bugs/let_obj_stmt/K001-callable-alias-direct/repro.lit) now succeeds without intermediate application equalities or trust. Its [observed.json](../../bugs/let_obj_stmt/K001-callable-alias-direct/observed.json) remains historical failure evidence. The dedicated [kernel tracer](../../../proof_nodes/equal/by_object_definition/by_fn_application/callable_alias_special_property.lit) also exercises an alias chain and qualification from an ordinary local membership hypothesis.

## Mechanism and evidence

`ExecEnv.special_properties: HashMap<ObjIR, Vec<SpecialProperty>>` indexes full `Membership(InFact)` and `Equality(EqualFact)` payloads, independent of the introducing statement. `store_atomic_fact` owns their indexing; equality rows are reachable at both endpoints, and repeated writes/merges deduplicate rows. `facts_by_id` remains the fact authority. Definition executors no longer separately register callable/sequence shapes.

The original asymmetry was that WD searched equality neighbors for a signature, while function-body lookup queried only the exact function name. Both now use stored equality evidence: WD retains the head-to-signature-subject path; body unfolding retains `g = f = AnonymousFn`, substitutes the arguments, and checks the residual `4 + 1 = 5` in the existing definition-search phase. No new unrestricted premise search or recursion budget was introduced. Detailed output includes these paths as `function_equal`; known-property source citations are named `cite_property_fact_id` rather than `cite_definition_fact_id`.

`DefaultStructView(InFact)` separately labels a definition-selected field view. A later membership alone does not select default struct field names. Function/signature equality aliases retain the existing callable-signature compatibility behavior.

## Acceptance and boundaries

```bash
cargo test --release special_property_tests -- --nocapture
cargo test --release known_search_tests -- --nocapture
cargo test --release equality_search_tests -- --nocapture
cargo test --release exec_stmt_transaction_tests -- --nocapture
cargo test --release declaration_binding_tests -- --nocapture
target/release/litex -strict -f examples/proof_nodes/equal/by_object_definition/by_fn_application/callable_alias_special_property.lit
python3 examples/test_statements/run.py --leaf LetObjStmt
```

Each direct CLI success requires both exit 0 and parsed top-level `success: true`. Membership alone qualifies a call without supplying a body or particular value. Executable Rust controls reject incorrect arity/carrier/value, keep local memberships scoped, and prove that a failed claim does not commit an otherwise successful equality step. The source- and citation-integrity regression checks both oriented generating-edge paths against real stored equalities.

The suite manifest now runs the unchanged reproduction as `boundary/resolved-K001-callable-alias-direct`, requiring all three statements to succeed. [Session and verification evidence](../../proof_journals/special_property_facts.json) records the comparison and final gates. Current tooling lacks the bundled policy's `-runner`/`-before` flags and literal `try:` syntax; the accepted supported session and structured `success` gate are recorded explicitly.

## Verified checkpoint

The eight dedicated Rust tests pass; known search (20), equality search (13),
transaction/WD (137), and declaration-binding (23) gates also pass. The examples
filter runs the included dedicated tracer (1 test), not the full examples tree.
Seven directly affected function/struct artifacts pass the release CLI. The
complete statement suite checks 361 cases over 50 leaves with no unexpected
failures; eleven unrelated known-gap reproductions remain.

All 113 runnable fences in the touched Manual, FAQ, and Blueprint pass. The
full Markdown scan checks 190 fences, of which nine fail in unmodified audit
documents containing intentional failure reproductions (for example,
`witness exist x {1} st {x = 0} from 0`) or documented unsupported goals.
Those audit snippets were neither changed nor skipped. Exact failed labels and
the policy/CLI drift are retained in the journal.
