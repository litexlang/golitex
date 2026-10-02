# Statement soundness audit: confirmed false proofs

Status: **confirmed bugs repaired in the current working tree; previously generated proofs still need re-verification.** The observations and proposed behavior below describe the vulnerable baseline; the implemented repair and its verification are recorded in the after-state section.

This report records observations from the vulnerable `0.9.200-beta` release CLI on 2026-10-01. Each `.lit` case was run alone with `target/release/litex -strict -f <absolute-case-path>`, in a directory without `litex.config`. The harness checked process exit status, top-level JSON `success`, `session_error`, and every `statement_results[*].success`. None of the false-proof fixtures contains `trust`, `axiom`, or `abstract_prop`. Source files were edited concurrently during the audit; the original replay is pinned by binary SHA-256 and source-file hashes in `tmp/2026-10-01/soundness-root-cause/baseline.json`. A second replay with binary SHA-256 `065a16389bdcd86cf0b2be3ba6935f0d1ae8cfa84da0d3b8b61da060d34779ec` confirmed the principal outcomes (`latest-binary-replay.json`).

## P0: explicit theorem calls skip typed-binder obligations

Observed case (`tmp/2026-10-01/soundness-root-cause/thm_wrong_domain.lit`):

```litex
thm only_natural:
    ? forall n N:
        n >= 0
release thm only_natural(-1)
-1 >= 0
```

Exit `0`, JSON `success: true`, and all three statements succeed. The selected-result route also stores `-1 >= 0`:

```litex
by thm only_natural(-1) => -1 >= 0
```

The same environment rejects bare `-1 $in N` and bare `-1 >= 0`. An additional `thm constant: ? forall n N: 1 = 1; release thm constant(1 / 0)` is accepted, showing that even an unused, undefined argument has no independent validation.

Cause: `prepare_forall_release` in `src/execute/execute_by_stmt/exec_by_thm_stmt.rs` checks arity, builds `subst`, instantiates only `forall.dom_facts` and `forall.then_facts`, and returns no obligation derived from `forall.typed_parameters`:

```rust
let mut dom_facts = Vec::with_capacity(forall.dom_facts.len());
for dom in &forall.dom_facts {
    match runtime.inst_fact(dom, &subst) { /* ... */ }
}
```

`exec_release_thm_stmt` and `exec_by_thm_stmt` then verify this incomplete `dom_facts` list before storing conclusions. The ordinary implicit forall-search path already has a type-first check in `prove_forall_instantiation_requirements` (`src/execute/execute_fact_stmt/verify_atomic_fact/prove_forall_instantiation_requirements.rs`), so this is an inconsistent explicit-call path.

**Proposed, unimplemented behavior:** for each instantiated binder, check argument well-definedness and the substituted binder-type fact (for example `-1 $in N`), then theorem premises, before any conclusion is assumed or stored. Both explicit call forms must reject the bad case, while `only_natural(0)` remains accepted. Dependent binder types must be instantiated using the full substitution. The existing `prove_forall_instantiation_requirements` contract is the reference; reuse must preserve evidence and failure reporting for explicit calls.

## P0: existential witness type is proved using its own assumed type

Observed case (`witness_false_complete.lit`):

```litex
witness exist x {1} st {x = 0} from 0
obtain a from exist x {1} st {x = 0}
a = 1
a = 0
0 = 1
```

Exit `0`, JSON `success: true`, all five statements succeed; the last result stores `0 = 1`. Bare `0 $in {1}` and bare `0 = 1` are rejected. The valid control `witness exist x {1} st {x = 1} from 1` is accepted.

Cause: `run_witness_exist_with_proof` in `src/execute/execute_witness_stmt/exec_witness_exist_fact.rs` calls `introduce_typed_parameters` (which stores `x $in {1}`), stores `x = 0`, executes proof steps, and only then calls `check_witness_exist_obligations_after_proof`, which proves `0 $in {1}`. That check can use the assumptions whose legitimacy it is supposed to establish:

```rust
rt.introduce_typed_parameters(&plain.typed_parameters, verify_state.clone())?;
rt.store_fact_and_infer(&equal_fact)?; // x = witness
// ... proof body ...
rt.check_witness_exist_obligations_after_proof(plain, equal_tos, need_uniqueness, verify_state.clone())?;
```

The same function also returns `ParamTypeFactCheckResult::Set`, `NonemptySet`, or `FiniteSet` without checking the concrete witness. Observed consequence (`witness_nonempty_empty.lit`):

```litex
witness exist x nonempty_set st {x = {}} from {}
obtain a from exist x nonempty_set st {x = {}}
$is_nonempty_set({})
```

Exit `0`, JSON `success: true`, all three statements succeed. The direct control `witness $is_nonempty_set({1}) from 0` is rejected, so the above is specific to the existential witness path.

**Proposed, unimplemented behavior:** prove each concrete witness's substituted type in a context that lacks the existential binder's assumed type fact and `binder = witness`, before using those assumptions for the body. Check the real `$is_set(w)`, `$is_nonempty_set(w)`, or `$is_finite_set(w)` obligation for the three set-kind binders. The present optional proof body runs before type checking; preserving the ability to prove types inside that body requires a separate safe proof scope. A simpler type-first rule would change accepted authoring behavior and should be an explicit semantic decision. Both `witness exist` and `witness $P` consume this shared path.

## P0: non-structured induction tests base under induction hypotheses

Observed case (`induc_false_complete.lit`):

```litex
prop bad(n Z):
    1 = 2
by induc n from 0:
    ? $bad(n)
$bad(0)
1 = 2
```

Exit `0`, JSON `success: true`, all four statements succeed; the last result stores `1 = 2`. Bare `1 = 2` is rejected. The structured `? from` / `? induc` variant of this false target rejects its induction statement. `by strong_induc` shares `run_unstructured` and is also exposed to its mixed-scope design, although the specific `strong_false_complete.lit` case rejects at its induction statement.

Cause: `run_unstructured` in `src/execute/execute_by_stmt/exec_by_induc_stmt.rs` first calls `store_ihs`, executes one common proof body, and verifies **both** the base and successor goals in that same local environment:

```rust
store_ihs(rt, param, stmt.induc_from, goal_facts, strong)?;
run_fact_only_proof_steps(rt, stmt.proof)?;
let base_proof = verify_goal_fact(rt, &base)?;
let step_proof = verify_goal_fact(rt, &succ_goal)?;
```

The structured path already opens a base environment without IH and a distinct successor environment with IH. **Proposed, unimplemented behavior:** use the same separation for the non-structured path or reject that spelling until its proof-body semantics is made precise. The base case must never read the IH or step-local facts. Both `by induc` and `by strong_induc` need negative and positive controls.

## P0: `witness $P(args)` skips predicate argument types

Observed case (`witness_pred_wrong_domain.lit`):

```litex
prop has_any(a N):
    exist x R st {x = 0}
witness $has_any(-1) from 0
```

Exit `0`, JSON `success: true`; the witness stores `$has_any(-1)` and infers `-1 $in N` and `0 <= -1`. `exec_witness_atomic_fact` in `src/execute/execute_witness_stmt/exec_witness_atomic_fact.rs` checks arity, substitutes the arguments into the sole existential clause, verifies that clause, then stores the predicate; it never verifies the definition's `typed_parameters` against the call arguments.

**Proposed, unimplemented behavior:** validate substituted predicate parameter types before projecting and storing `$P(args)`. This is distinct from checking the projected existential witness's own type. The bad case must reject, while a valid `$has_any(0)` control must remain accepted.

## Separate availability failure: self-dependent theorem premise

The reduced case in `explicit_dom_control.lit` defines `forall n Z: n >= 0 => n >= 0`, then calls it on `-1`. The process aborts from stack overflow (exit `-6`) instead of rejecting a failed premise; this also reproduces with the second binary (`dom-crash-latest.json`). The theorem definition alone and the valid call on `0` succeed; changing its conclusion to `n = n` or `1 = 1` makes the bad call reject normally. The visible search path in `search_proof_by_known_forall_fact.rs` may reconsider a theorem conclusion while proving that theorem's own premise (`prove_forall_instantiation_requirements.rs`). This explains the likely recursion, but the exact missing cycle/depth guard has not been traced to a concrete call stack. Treat as a separate verifier-availability defect and investigate before choosing a patch.

## CLI and verification boundary

Current `src/launch_command.rs` accepts `-f`, `-r`, `-e`, `-session`, `-strict`, and `-lang`; `-runner`, `-compact`, `-isolated`, and `-before` each exit `2` with `launch_error`. `docs/cli.md` describes this current whitelist. The repository policy's old `-runner/-compact/-isolated/-before` recipe is therefore stale. This audit used the actual Normal JSON from `-strict -f`, requiring exit `0`, top-level `success: true`, `session_error: null`, and all statement results successful; it did not interpret unsupported flags as proof results. `-strict` does not prevent the false proofs above.

## Containment and repair order

1. Mark results produced through the affected `release thm`, `by thm`, witness, and non-structured induction paths as untrusted pending re-verification. For externally relied-on theorems, use a separate trusted kernel check until these paths are repaired and audited.
2. Add executable negative regressions for each false fixture and the stack-overflow input, with positive controls for valid theorem calls, witnesses, and induction. Require the entire file result and exit status to agree.
3. Repair the four earliest obligation/scope boundaries above. Do not patch the final equality checker: it correctly rejects `0 = 1` and `1 = 2` in isolation, then correctly follows facts that earlier unsound steps stored.
4. After fixes, run focused Rust and release CLI tests, then broader kernel/statement gates justified by the cross-subsystem scope. Recheck existing proof artifacts; a previously accepted statement is not automatically sound just because a later checker version rejects these specific probes.

This is a focused soundness diagnosis, not an exhaustive review of every statement or every use of the same proof-search helpers.

## After-state: repaired proof boundaries

The repair moves concrete argument-type obligations before any instantiated theorem or predicate conclusion can be stored. `release thm` and `by thm` now verify every typed binder, then the theorem premises, before releasing conclusions. `witness exist` and `witness $P` verify concrete witness types before introducing existential binder facts; the latter also verifies the predicate call's own parameter types. `by induc` and `by strong_induc` run unstructured proof steps independently in base and successor scopes, so only the successor has an induction hypothesis. These changes do not add trust, axioms, or AST fields.

The self-dependent theorem crash had a separate search-budget cause: non-equality atomic deep search could enter at round zero and recurse through a known-forall conclusion into its own premise. That entry now requires positive fuel, as the equality path already did. Chain, conjunction, disjunction, and existential known-forall entries also consume fuel and stop at zero; their self-premise controls now fail normally without a session error. The top-level budget is three rounds, preserving two nested premise steps needed by existing valid proofs while retaining a hard zero-round boundary.

The final release CLI replay in `tmp/2026-10-01/soundness-boundary-repair/after-budget3.json` is pinned to binary SHA-256 `f5880235693dbe0507afd339e22d5dfb6a10a89ba96fe5abd5472ef7efd61987` and checked exit code, top-level success, `session_error`, and each statement result. All 17 negative controls, including invalid explicit theorem calls, invalid concrete and set-kind witnesses, invalid predicate call, false induction, and self-dependent premises, exit `1` with `success: false` and a failed owning statement. All five positive controls exit `0` with every statement successful. The separate chain/and/or/exist self-premise probes are in `adjacent-self-premise.json`; adjacent constructor probes are in `adjacent-constructors.json`. The durable Rust regressions are in `tests/unit/execute/soundness_boundaries/tests.rs`; positive runnable examples are in `examples/stmt_nodes/witness/witness_type_soundness.lit`, `examples/stmt_nodes/definition/theorem_call_typed_arguments.lit`, and `examples/stmt_nodes/by/induction_base_scope.lit`.

Adjacent constructor review found that `have x S = value` proves the concrete value's type before defining `x`; `have x S` checks nonemptiness of `S` before introducing a fresh abstract object. The `ParamTypeFactCheckResult::Set`/`NonemptySet`/`FiniteSet` markers in that latter path concern the declared binder kind, not a concrete witness, so they are not the witness bug. Both `obtain … from exist` and `obtain … from $P(args)` first verify their source fact before eliminating it; `have … : facts` verifies the synthesized existential before introducing names; `have by fn_preimage` verifies range membership before storing the preimage facts. This is a targeted entry-point audit, not a proof that no other verifier path is unsound.

The witness rule is now deliberately type-first. A proof body may establish the existential body and uniqueness obligations, but it cannot establish the concrete witness's type after existential binder assumptions have been introduced. Previously accepted artifacts involving any affected path must be rechecked with a repaired verifier before being relied upon. The CLI interface drift noted above remains: repository policy flags `-runner/-compact/-isolated/-before` are unavailable, so all replay used the supported `-strict -f` JSON interface.

`cargo test --release --lib` reached 379 passing and four failures in this concurrently edited worktree (`test-budget3.log`): one finite-set union cardinality rule and three JSON expectations for the preferred known-order proof route. All six new soundness regressions passed. Raising the bounded search budget from three to four did not change those four failures, so the final setting remains three. The non-strict statement tracer sweep passed 74 of 77 files; one file intentionally expects a soft failure (`def_algo_mismatch.lit`), while callable-alias unfolding and a template/struct parser fixture still fail. These wider gates are not claimed green, and the remaining failures have not been attributed to this repair or proven independent of it.
