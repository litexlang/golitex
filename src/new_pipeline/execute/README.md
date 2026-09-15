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

```text
ExecStmtResult
  Success(ExecStmtSuccess)     // merge temp → parent
  Failed(ExecStmtFailed)       // discard temp; session continues
RuntimeResult::Err             // SessionError; stop session

ExecStmtSuccess / ExecStmtFailed mirror stmt kind:
  Fact | Definition | Unsafe
Definition / Unsafe nest further (let / have / prop / trust / …).
```

JSON presentation (not Rust names): Success → `"success"`, Failed → `"error"`,
SessionError → `"session_error"`.

## Transactional `exec_stmt`

```text
exec_stmt (pub only)
  push empty temp ExecEnv
    exec_xxx_stmt  (execute-module private; writes current top only)
  pop temp
    Failed  → Ok(Failed); no merge
    Success → parent.merge_from(temp) → Ok(Success)
Err → merge/invariant bugs (SessionError)
```

- Success does not carry the closed temp env.
- Binder locals (forall / prop params) are inner scopes inside the temp shell.
- Object WD: stack lookup → ByCache; else ByDef; when
  `store_well_defined_fact`, record on current top so Success merge persists it.
