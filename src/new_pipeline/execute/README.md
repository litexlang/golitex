# new_pipeline statement execution

## Hard rule: only `exec_stmt`

```text
Runners / REPL / tests / other modules  →  Runtime::exec_stmt ONLY
exec_xxx_stmt / execute_fact_statement  →  only called from inside execute,
                                           by exec_stmt
```

Never call branch `exec_*_stmt` functions from outside
`crate::new_pipeline::execute`. Nested proof/WD uses `verify_*` / `store_*`,
not another `exec_stmt`.

## Result shape

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
  Witness(ExecWitnessStmtResult)
  Unsafe(ExecUnsafeStmtResult)
  By(ExecByStmtResult)
  ReleaseThm(ExecReleaseThmStmtResult)
  ReleaseStructDef(ExecReleaseStructDefStmtResult)

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
