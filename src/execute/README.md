# new_pipeline statement execution

## Hard rule: only `exec_stmt`

```text
Runners / REPL / tests / other modules  →  Runtime::exec_stmt ONLY
exec_xxx_stmt / execute_fact_statement  →  only called from inside execute,
                                           by exec_stmt
```

Never call branch `exec_*_stmt` functions from outside
`crate::execute`. Nested proof/WD uses `verify_*` / `store_*`,
not another `exec_stmt`.

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
