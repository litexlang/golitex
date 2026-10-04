# Statement execution

## Checked eval result publication

`eval expr` checks source WD, computes exactly, verifies every executed
algorithm's defining equation at its normalized arguments, checks the generated
equality's WD, then calls the existing `store_fact_and_infer` on `expr = value`.
The computation trace is retained in `ExecEvalStmtSuccess`, including checked
algorithm evidence and actual stored FactId. The command uses the ordinary
`exec_stmt` temporary environment: failure discards effects and proof-local
facts remain local. No new Env/Runtime state owner or implicit search permission
is introduced. Normal and Detailed JSON expose the store effect.

Tracer: [eval_store_result.lit](../../examples/stmt_nodes/command/eval_store_result.lit).

## Identifier identity and witness diagnostics

`env_stack_lookup::stored_identifier_definition_visible` applies its existing
ID/file-owner check to each candidate in the existing lookup walk. A local
existential binder with the same surface name but another ID is skipped rather
than reported as the definition of an ambient witness. Qualified references
still select their exact export/module owner. Storage, allocation and scope
lifetimes are unchanged. `examples/wd/witness_same_named_binder.lit` and the
`witness_binding` tests cover scalar/function witnesses, false IDs and rollback;
the registered/imported identifier and declaration suites cover file ownership.

Detailed witness failures mirror the existing atomic/exist result stages,
including argument/type WD, binder introduction, body step/check and uniqueness.
Their projections retain nested failed results without changing execution.
The subtraction-bound rule also has separate greater-equal and less-equal root
payloads sharing a numeric certificate, preserving the one-rule/one-payload
contract and the actual source citation in each directional JSON node.

## Template definition facts

A successful template retains its local body evidence and publishes only the
facts recorded by the body's successful definition stores and their ordinary
inference. `store_template_definition_facts` substitutes the body binding by
the definition-owned template instance, prefixes the template parameters and
domain premises, and calls `store_fact_and_infer` in the enclosing statement
transaction. Existing universal conclusions are flattened with the outer
binders; case and function-domain premises remain present. Each published
result links its new store evidence to a `source_fact_id` in the retained local
environment. No parameter assumption, WD probe, or proof-scope intermediate
fact is exported by scanning the environment.

For `template<S nonempty_set>: have member S`, publication stores
`forall S nonempty_set: \member<S> $in S`. Known-forall matching binds template
arguments structurally only when the canonical template identities agree.
The [acceptance example](../../examples/stmt_nodes/definition/template_definition_facts.lit)
and `tests/unit/execute/template_definition_facts/tests.rs` cover this contract.

## Hard rule: only `exec_stmt`

```text
Runners / REPL / tests / other modules  →  Runtime::exec_stmt ONLY
exec_xxx_stmt / execute_fact_statement  →  only called from inside execute,
                                           by exec_stmt
```

Never call branch `exec_*_stmt` functions from outside
`crate::execute`. Verifier-only work uses `verify_*` / `store_*`.
Nested source statements use `run_proof_body_stmts`, which calls the same
transactional `exec_stmt` inside the enclosing child proof scope. A failed
step fails that proof; helper definitions never merge into the outer scope.
This is shared by claim/witness, by-method and strategy proof bodies. Strategy
definitions publish their checked interface without injecting the goal as an
ordinary known-forall fact.

## Result shape

### Dual consumers and evidence granularity

Name clarification: `RuntimeResult<T>` is only `Result<T, RuntimeError>`
(SessionError). The contract below applies to the typed pipeline evidence
tree: `Exec*Result`, `Verify*Result` / `*SearchedProof`, `Infer*Result`, and
nested WD / builtin / known-fact payloads.

That tree is **one IR with two consumers**, not two parallel logs:

1. **Human / AI output** — JSON / `statement_results`: what each statement
   did, which route succeeded or soft-failed, what was inferred or stored.
   Source states *what*; results explain *how*.
2. **Litex-to-Lean replay** — `stmt_result_to_lean_compiler` walks the same
   winning evidence and emits Lean tactics / proof steps. Do not reconstruct
   the proof from display text or ask Lean to search a different proof.

`Exec` / `Verify` / `Infer` share this role with different slices:

| Slice | Owns |
| --- | --- |
| Exec | Statement effect on the session (Success merge / Failed discard) |
| Verify | Mathematical grounds (WD + winning search route) |
| Infer | Forward consequences stored after success |

**Granularity target:** one *named* proof route ≈ one replayable Lean step
(a dedicated builtin evidence struct, a known-fact cite, a binder/local-env
proof, a structured `by` branch, …).

| Too fine (avoid) | Too coarse (avoid) |
| --- | --- |
| Unification internals, every cache miss, failed attempts inside `searched_proof` | Only pass/fail with no route identity |
| Hard to maintain / read; weak Lean mapping | Neither readable nor Lean-replayable |

Failed attempts belong in a separate `search_trace` if retained at all; never
overload `searched_proof`. When adding a result field, ask: can a human
explain this step from the JSON, and can the Lean compiler map this field to
a tactic without re-searching?

Product prose: `docs/Litex_Blueprint.md` (Section 4). Compiler consumption:
`src/stmt_result_to_lean_compiler/README.md`. Agent constraint when reshaping
types: `.cursor/skills/litex-pipeline-result-types/SKILL.md`.

### Proof vs Result (hard convention)

```text
*Proof     = success evidence only (never embeds soft-fail)
*Result    = Success(*Proof | *SuccessResult) | Failed(...)

WD / search-proof / verify / exec outcomes that can miss
must be *Result. Do not put Fail inside a *Proof and scan
with is_failed() on the proof payload.
```

`is_failed()` is allowed only as a thin match on a real `*Result` enum
(Success | Failed, or Fail* variants). It must not walk mixed proof bags.

```text
ExecStmtResult                    // stmt-kind dispatch only
  Fact(ExecFactStmtResult)
  Definition(ExecDefinitionStmtResult)
    DefineObj(ExecDefineObjStmtResult)   // let / have / obtain / have by …
    HaveFnEqual | HaveFnEqualCaseByCase | HaveFnByForallExistUnique | HaveFnByInduc
    DefProp | DefAbstractProp | DefStruct | DefTemplate | DefThm | Axiom | DefStrategy
  Witness(ExecWitnessStmtResult)
  Trust(ExecTrustBoundaryStmtResult)
  By(ExecByStmtResult)
  Register(ExecRegisterStmtResult)
  ReleaseAndExpand(ExecReleaseAndExpandStmtResult)   // Thm / StructDef / ObjDef / ExpandRange / Zorn / AoC / Regularity
  ProofBlock(ExecProofBlockStmtResult)
  Command(ExecCommandStmtResult)   // Eval

Leaf *Result = Success(*SuccessResult) | Failed(...)
  (AbstractProp has only SuccessResult; no soft-fail path yet)

is_failed() on ExecStmtResult walks into the leaf.
  Failed  → discard temp; session continues
  Success → merge temp → parent
RuntimeResult::Err               // SessionError; stop session
```

Leaf Success/Fail types live at the head of each statement file;
`exec_stmt_result.rs` keeps the top-level dispatch shells plus shared
ParamType shells:

- `ParamTypeWellDefinedProof` — type-annotation WD
- `ParamTypeFactCheckResult` — fact obligation by ParamType (`have` nonempty,
  `witness` membership, …)

JSON presentation (not Rust names): Success → `"success"`, Failed → `"error"`,
SessionError → `"session_error"`.

## Transactional `exec_stmt`

```text
exec_stmt (pub only)
  push empty temp ExecEnv
    exec_xxx_stmt  (execute-module private; writes current top only)
  pop temp
    is_failed  → Ok(result); no merge
    else       → parent.merge_from(temp) → Ok(result)
Err → merge/invariant bugs (SessionError)
```

- Success does not carry the closed temp env.
- Binder locals (forall / prop params) are inner scopes inside the temp shell.

## Induction scope and evidence

`execute_by_stmt/exec_by_induc_stmt.rs` checks the integer base, then goal WD
under `n in Z` and `n >= from` without IH. It runs base and successor in
separate locals using the existing `run_proof_body_stmts` helper used by claims
and witnesses. The base gets `n = from`; the step gets the lower bound and
ordinary or bounded strong IH. Only the final universal is stored in the
parent. Success retains the WD, base, and step local environments and their
ordered evidence; failed results distinguish base from successor and carry
the failed goal or ordinary statement with its index.

`recover_induction_param.rs` finds the parsed free ID in all target object
shapes and proof actions. It skips nested binders and qualified identifiers;
only a genuinely unused binder receives a fresh identity. AST fields and
runtime allocation/storage contracts are unchanged by this traversal.

`execute_have_fn_by_induc_stmt.rs` validates each sibling list for coverage,
disjointness, and return WD/type before publication. Nested lists use the
parent's guard and preserve their own local evidence. Chain guards are
expanded to adjacent atomic facts, including when leaf equations are stored.
Template replay uses ordinary ID-based object instantiation for self calls,
so calls beneath arithmetic or other constructors retain the exact instance.
The existing equality budget is unchanged; a smaller-call equality can still
be needed as an explicit proof step for recursive arithmetic.

Acceptance: `tests/unit/execute/induction_repairs/tests.rs` executes positive
examples, rejects overlap/holes and false base/step, checks rollback and strict
proof actions, and checks Normal/Detailed producers against these result trees.

## Native reserved theorem calls

`execute_by_stmt/builtin_thm/` prepares the 25 legacy named contracts using
current AST constructors and verification owners. Pure name/arity metadata
lives in `builtin_theorem.rs` so parsing can reject reserved-name rebinding
without depending on execution. `exec_by_thm_stmt.rs` verifies parameter
types, premises and every conclusion's WD before publication; `by thm`
stores only its verified selected fact. No legacy runtime is called.

Complex identities containing the actual imaginary-unit AST node enter
`search_equal_fact_by_calculation.rs`. Symbolic denominator obligations
remain with the existing premise-checking strategy. Indexed union,
intersection and product explicitly require a nonempty index set in WD,
for named and anonymous families alike. Definition-unfold residuals keep
`can_use_rewrite: false`; explicit chains retain their checked endpoints.


## Enumeration and eval boundaries

The strict gate inspects both ordinary trust statements and the trust-have
body of a template before execution. Nested statements pass through this gate.
Finite enumeration introduces the original binders and one concrete assignment
as local equality assumptions. Its per-assignment evidence selects either a
proved false atomic antecedent or a checked local proof under the antecedents.
It retains parameter introduction, assumptions, proof steps, conclusion checks
and stores, and the closed local environment. Displayed list sets and concrete
integer ranges are enumerable; Cartesian-product domains are unsupported.
`eval` checks the source object's WD before rewriting or executing it. Its
success carries the source WD proof; a domain failure retains the typed WD
result. Evaluation output is not stored as a mathematical fact.


Atomic Direct search reads stored proofs, then tries pure closed evaluation and
structural membership. The latter builds a typed carrier tree over smaller AST
children with fixed raw-known/closed/intrinsic leaves; it cannot enter higher
search stages or mutate facts/WD memory. The enclosing verify pipeline continues
to own all WD evidence. See `execute_fact_stmt/README.md` and the maintained
`examples/proof_nodes/atomic/direct_structural_membership.lit` tracer.

`FnApplicationInStandardSuperset` is a read-only KnownSpecialProperty leaf for stored function signatures after application WD. It checks all fully applied standard return carriers against the intrinsic numeric inclusion relation, preserving each signature FactId and head equality path. It never searches domain premises or changes the WD cache. Nonstandard carriers and intrinsic template/field alternatives conservatively retain their existing producers. The dedicated tracer is `examples/proof_nodes/atomic/by_known_special_property/function_return_standard_superset.lit`.

The existing `LessFromPosDifference` builtin leaf consumes a saved `0 < b - a`
or `b - a > 0` after the enclosing comparison has checked real operands. It tries
at most two fixed known-premise lookups, in that order, and retains the selected
premise proof and FactId. It cannot enter another search stage, generate a bound,
or mutate facts or WD memory. Greater goals retain the existing order-dual
rewrite. The tracer is
`examples/proof_nodes/atomic/by_builtin_rule/greater_from_positive_difference.lit`;
the focused `positive_difference_order` tests cover both spellings, strictness,
direction, domain and local-scope rejection.
